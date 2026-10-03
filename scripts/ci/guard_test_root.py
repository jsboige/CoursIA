#!/usr/bin/env python3
"""Garde anti-recidive : empeche l'apparition de test_*.py hors des chemins collectes par Scripts Tests (CPU).

Issue : #18888 -- 9 fichiers scripts/notebook_tools/test_*.py vivaient a la
racine de scripts/notebook_tools/, hors du dossier tests/. Aucune jambe de CI
ne les executait.

Ce garde lit la liste des chemins collectes par le job Scripts Tests (CPU)
dans `.github/workflows/scripts-tests.yml` (ligne pytest) et verifie qu'aucun
test_*.py n'apparait dans un dossier *parent* d'un chemin collecte
(typiquement la racine d'un module) sans etre dans le sous-dossier collecte
lui-meme. Pour les chemins fichier (cas de `agent_tests/tests/test_bg_tree_lock.py`),
seul le fichier exact est accepte, pas ses voisins.

Pourquoi parser le YAML au lieu de hardcoder : le coordinateur (msg
2026-10-02T230446-w8h2s0) demande que la liste des chemins soit lue a la
source, sinon le garde derivera au prochain ajout. C'est aussi une assurance
contre l'oubli : si quelqu'un ajoute un chemin au job mais oublie de tenir
le garde au courant, le garde ne va pas refuser une situation devenue
legitime.

Usage :
    python scripts/ci/guard_test_root.py             # exit 1 si regression
    python scripts/ci/guard_test_root.py --json      # sortie JSON
    python scripts/ci/guard_test_root.py --workflow <path>  # override YAML
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_WORKFLOW = REPO_ROOT / ".github" / "workflows" / "scripts-tests.yml"


class PytestBlockNotFound(Exception):
    """Le workflow contient `pytest` mais le bloc multi-lignes ne matche
    pas. C'est un defaut de lecture -- le garde ne peut pas verifier
    quoi que ce soit et DOIT le signaler plutot que rendre `ok=True` a
    tort. Cf. CONCERNS coordinateur (c.86) sur #18896 + CONCERNS
    adjoint po-2025 (c.87) sur #18951 (inline pytest + derniere ligne
    sans continuation)."""

# On matche un APPEL pytest complet : `pytest` (ou `python -m pytest`)
# suivi d'une liste d'arguments qui peut tenir sur 1 ligne (inline) ou
# sur N lignes (multi-lignes YAML block scalar, chaque ligne
# indentee). La fin de l'appel est signalee par une ligne vide, un
# retour en col 0 (debut d'une autre cle YAML), ou la fin de fichier.
# Cf. #18896 (CONCERNS c.86) : la version precedente exigeait `-n` en
# fin de bloc, ce qui rendait l extraction VIDE pour les workflows
# pytest valides sans xdist. Cf. #18951 (CONCERNS c.87) : la version
# c.86 ne capturait pas la derniere ligne d'arguments sans
# continuation, et ignorait completement les appels inline -- le
# contrat "soit on mesure, soit on refuse" n'etait pas tenu sur ces
# deux cas.
#
# Strategie : on trouve la ligne qui contient `pytest` (eventuellement
# apres `python -m`). Le bloc d'arguments est forme de toutes les
# lignes consecutives qui sont (a) NON VIDES, (b) indentées au moins
# autant que la ligne `pytest` (donc on reste dans le meme bloc YAML),
# et (c) qui ne sont pas une autre cle YAML (commencent par un
# alphabetique ou un caractere special YAML). La ligne peut finir par
# `\` (multi-lignes) ou par autre chose (fin de l'appel).
PYTEST_INVOCATION_RE = re.compile(
    r"(?:(?<=\s)|(?<=\A)|(?<=\=))(?:python[ \t]+(?:-m[ \t]+)?)?pytest(?=[ \t]+\S)",
    re.MULTILINE,
)

# Options pytest qui sont BOOLEENNES (sans valeur). Une option
# booleenne ne doit pas declencher `skip_next` dans le parser -- sinon
# le token suivant (un chemin) est avale comme valeur de l'option.
# Cf. CONCERNS adjoint po-2025 c.9 sur #18951 : `pytest --verbose
# scripts/notebook_tools/tests/` rendait `paths=[]` car `--verbose`
# etait traite comme `--xxx` (valeur) et le chemin etait avale.
# Reference : https://docs.pytest.org/en/stable/reference/reference.html#command-line-flags
PYTEST_BOOLEAN_OPTIONS: frozenset[str] = frozenset({
    # Short boolean
    "-v", "-q", "-s", "-x", "-l", "-h",
    # Long boolean
    "--verbose", "--quiet", "--exitfirst", "--capture=no", "-s",
    "--strict", "--strict-markers", "--strict-config",
    "--doctest-modules", "--doctest-ellipsis", "--doctest-glob",
    "--continue-on-collection-errors",
    "--co", "--collect-only",
    "--showlocals",
    "--lf", "--last-failed",
    "--ff", "--failed-first",
    "--sw", "--stepwise",
    "--sw-skip", "--stepwise-skip",
    "--nf", "--new-first",
    "--cache-show", "--cache-clear",
    "--ci",
    "--runxfail",
    "--no-header", "--no-summary", "--no-cov", "--no-cov-on-fail",
    "--benchmark-disable", "--benchmark-only", "--benchmark-skip",
    "--help", "--version",
    "-h",
})


def parse_collected_paths(workflow: Path) -> list[str]:
    """Lit la liste des chemins collectes par pytest depuis le YAML.

    Strategie : on cherche le premier appel `pytest` (avec ou sans
    `python -m`). Une fois trouve, on collecte tous les tokens qui
    suivent sur la meme ligne (cas inline) et sur les lignes suivantes
    qui sont dans le meme bloc YAML (meme niveau d'indentation ou plus,
    ou continuation par backslash). On s'arrete a la premiere ligne qui :
      - est vide, ou
      - commence en col 0 (sortie du bloc YAML), ou
      - commence par un caractere YAML (`-`, `#`, etc., debut d'une
        autre entree de liste).

    Si le workflow ne contient pas du tout `pytest`, on rend une liste
    vide (le workflow n'est pas dans le scope de cette garde). Si
    `pytest` est present mais qu'on ne peut pas extraire d'arguments
    (par exemple "pytest \" seul sans chemins), on leve
    ``PytestBlockNotFound`` : le garde DOIT refuser plutot que rendre
    ``ok=True`` sans rien verifier (#18896 c.86, #18951 c.87).
    """
    text = workflow.read_text(encoding="utf-8")
    m = _find_pytest_invocation(text)
    if m is None:
        return []
    # Si le match provient d'un scalaire YAML decode, on travaille sur
    # la version decodee (le match pointe sur du texte decode, pas sur
    # le texte brut). Cf. CONCERNS adjoint po-2025 c.9 sur #18951.
    if _is_decoded_match(m):
        work_text = m.decoded_text
        pytest_end = m.end()
    else:
        work_text = text
        pytest_end = m.end()
    # Capture du bloc d'arguments. On collecte toutes les lignes qui
    # font partie du meme appel pytest (meme bloc YAML, ou inline).
    rest = work_text[pytest_end:]
    lines = rest.split("\n")
    args_lines: list[str] = []
    if lines:
        # La ligne qui contient pytest (apres le mot pytest) -- cas
        # inline : on prend tout jusqu'au \n.
        first_line = lines[0]
        # Si la ligne se termine par `\\`, c'est une continuation.
        first_has_cont = first_line.rstrip().endswith("\\")
        args_lines.append(first_line)
    # Pour les lignes suivantes (cas multi-lignes), on continue tant
    # qu'on est dans le meme bloc YAML. Une ligne vide, une ligne en
    # col 0 (sans indentation), ou une ligne qui commence par `-`/`#`
    # met fin au bloc.
    base_indent = _line_indent(work_text, m.start())
    for line in lines[1:]:
        if not line.strip():
            break  # ligne vide
        line_indent = _line_indent_of(line)
        # Si on est dans une continuation `\\`, on accepte les lignes
        # indentees jusqu'a la fin du bloc.
        if line_indent == 0:
            break  # retour en col 0 : sortie du bloc YAML
        if line.lstrip().startswith(("-", "#")) and line_indent <= base_indent:
            break  # nouvelle entree de liste ou commentaire en col 0
        # On accepte la ligne (avec ou sans \).
        args_lines.append(line)
        if not line.rstrip().endswith("\\"):
            # Derniere ligne du bloc d'arguments.
            break
    # Joindre les lignes en nettoyant les continuations.
    joined = " ".join(args_lines)
    joined = re.sub(r"[ \t]*\\[ \t]*\n[ \t]*", " ", joined)
    # Filtrer les `\` orphelins (sans continuation) et les separateurs
    # YAML residuels.
    joined = re.sub(r"(?<!\\)\\(?!\S)", "", joined)
    tokens = joined.split()
    paths: list[str] = []
    skip_next = False
    for tok in tokens:
        if skip_next:
            skip_next = False
            continue
        # Filtre : flags (-x, -n 4) et leurs valeurs (--dist loadscope,
        # --tb short). Une option longue `--xxx` peut prendre une valeur
        # au token suivant -- ici on l'ignore.
        if tok.startswith("-"):
            if tok.startswith("--"):
                # Option longue. Trois cas :
                # 1) `--xxx=VAL` : la valeur est dans le meme token, pas
                #    de skip_next necessaire.
                # 2) `--xxx` (sans `=`) ET dans PYTEST_BOOLEAN_OPTIONS :
                #    option booleenne, pas de skip_next necessaire.
                # 3) `--xxx` (sans `=`) ET hors set : on suppose qu'elle
                #    prend une valeur au token suivant (skip_next).
                # Cf. CONCERNS adjoint po-2025 c.9 sur #18951 : cas
                # `--verbose` (booleen) traitait le chemin suivant comme
                # valeur, d'ou `paths=[]`.
                if "=" in tok:
                    pass  # valeur inline, on ignore le token
                elif tok in PYTEST_BOOLEAN_OPTIONS:
                    pass  # booleen, pas de skip_next
                else:
                    skip_next = True
            continue
        if tok.isdigit():
            continue
        paths.append(tok)
    # Si l'invocation matche mais qu'on n'a extrait aucun chemin, c'est
    # que pytest est appele avec uniquement des flags (par exemple
    # `pytest \` puis `-q`). Le garde ne peut rien mesurer -- il DOIT
    # refuser plutot que rendre `ok=True` sans rien verifier.
    if not paths:
        raise PytestBlockNotFound(
            f"{workflow} contient un appel pytest mais aucun chemin "
            f"n'a pu etre extrait (args trouves : {tokens!r}). Le "
            f"garde ne peut pas verifier. Cf. CONCERNS coordinateur "
            f"(c.86) sur #18896 et CONCERNS adjoint po-2025 (c.87) "
            f"sur #18951."
        )
    return paths


def _line_indent(text: str, pos: int) -> int:
    """Indentation de la ligne qui contient la position pos dans text."""
    start = text.rfind("\n", 0, pos) + 1
    line = text[start:pos]
    return len(line) - len(line.lstrip())


def _line_indent_of(line: str) -> int:
    """Indentation d'une ligne donnee."""
    return len(line) - len(line.lstrip())


def _find_pytest_invocation(text: str) -> re.Match | None:
    """Trouve le premier appel pytest qui n'est pas dans un commentaire
    YAML ni dans une chaine quotée non-scalaire. Heuristique : on
    considere pytest comme un appel si (a) la ligne ne commence pas
    par `#`, et (b) pytest est precede d'un whitespace ou debut de
    ligne, et (c) pytest est suivi d'un separateur d'argument (`\\s` ou
    fin de ligne) -- un `pytest-x` dans une dependances pip n'est pas
    un appel.

    Cas special CONCERNS adjoint po-2025 c.9 sur #18951 : un
    `run: "python -m pytest scripts/notebook_tools/tests/ -q"` est un
    **scalaire YAML valide** (la ligne entiere est entre quotes, c'est
    legal en GitHub Actions). L'ancienne implementation rejetait
    pytest dans cette chaîne (quote_count impair) et rendait
    `paths=[]`. Le fix : si la ligne est un scalaire YAML entre
    quotes et contient pytest, on decode le contenu (retire les
    quotes) et on re-matche la regex sur la version decodee.

    Renvoie soit un match direct sur `text`, soit un objet
    ``_DecodedMatch`` (namedtuple-like) qui wrap un match interne +
    le texte decode. Voir ``_is_decoded_match``.
    """
    return _find_pytest_in_decoded_or_raw(text)


def _is_decoded_match(m) -> bool:
    """Vrai si le match provient d'un scalaire YAML decode."""
    return isinstance(m, _DecodedMatch)


class _DecodedMatch:
    """Wrapper d'un re.Match + le texte decode sur lequel il a ete
    trouve. Necessaire parce que ``re.Match`` n'accepte pas
    l'attribution d'attributs (objet immutable)."""
    __slots__ = ("match", "decoded_text")

    def __init__(self, match: re.Match, decoded_text: str):
        self.match = match
        self.decoded_text = decoded_text

    def start(self) -> int:
        return self.match.start()

    def end(self) -> int:
        return self.match.end()


def _find_pytest_in_decoded_or_raw(text: str):
    """Implementation complete : essaie d'abord sur le texte brut, puis
    sur les scalaires YAML decodes (run: "..." ou run: '...')."""
    m = _find_pytest_raw(text)
    if m is not None:
        return m
    for _line_start, _line_end, decoded in _iter_yaml_scalar_lines(text):
        m = _find_pytest_raw(decoded)
        if m is not None:
            return _DecodedMatch(m, decoded)
    return None


def _iter_yaml_scalar_lines(text: str):
    """Iterateur sur les lignes de la forme `cle: "..."` ou `cle: '...'`
    ou `- cle: "..."` (sequence item). Renvoie (line_start, line_end, decoded)."""
    for line in text.splitlines(keepends=True):
        stripped = line.lstrip()
        # Forme : `key: "value"`, `key: 'value'`, ou `- key: "value"`
        # (sequence item contenant un mapping).
        if ":" not in stripped:
            continue
        # Retirer le prefix `- ` (sequence item) si present.
        if stripped.startswith("-"):
            stripped = stripped[1:].lstrip()
        if ":" not in stripped:
            continue
        key, _, rest = stripped.partition(":")
        rest = rest.strip()
        if not key.replace("-", "").replace("_", "").isalnum():
            continue
        if len(rest) >= 2 and rest[0] == rest[-1] and rest[0] in ('"', "'"):
            decoded = rest[1:-1]
            line_start = text.find(line)
            line_end = line_start + len(line)
            yield (line_start, line_end, decoded)


def _find_pytest_raw(text: str) -> re.Match | None:
    """Recherche brute d'un appel pytest dans `text`. Renvoie le match
    ou None. Cf. CONCERNS c.86 (sans-xdist) et c.87 (inline)."""
    for m in PYTEST_INVOCATION_RE.finditer(text):
        line_start = text.rfind("\n", 0, m.start()) + 1
        line_end = text.find("\n", m.end())
        if line_end == -1:
            line_end = len(text)
        line = text[line_start:line_end]
        stripped = line.lstrip()
        # Commentaire YAML : skip.
        if stripped.startswith("#"):
            continue
        # Quote check : sur la portion de ligne jusqu'au debut de pytest,
        # compter les apostrophes et guillemets. Si le compte est
        # impair, pytest est dans une chaîne YAML non-scalaire et
        # n'est pas un appel.
        prefix = line[: m.start() - line_start]
        quote_count = sum(1 for c in prefix if c in ("'", '"'))
        if quote_count % 2 == 1:
            continue
        return m
    return None


def _is_collected(entry: Path, collected_dirs: set[Path], collected_files: set[Path]) -> bool:
    """Vrai si le fichier entry est dans un chemin collecte.

    - Si entry est dans un dossier collecte (recursivement), OK.
    - Si entry est dans la liste explicite des fichiers collectes, OK.
    - Sinon, violation.
    """
    if entry.resolve() in collected_files:
        return True
    for d in collected_dirs:
        try:
            entry.resolve().relative_to(d)
            return True
        except ValueError:
            continue
    return False


def _in_scope(parent: Path) -> bool:
    """Vrai si le dossier parent est dans le scope strict du garde
    (`scripts/notebook_tools/`, conformement a l'issue #18888)."""
    try:
        parent.relative_to(REPO_ROOT / "scripts" / "notebook_tools")
        return True
    except ValueError:
        return False


def find_violations(collected_paths: list[str]) -> list[Path]:
    """Liste les test_*.py qui ne sont dans aucun chemin collecte.

    Strategie :
    - Pour chaque chemin collecte, distinguer fichier vs dossier.
    - Si dossier, accepter tout descendant (pytest collecte recursivement).
    - Si fichier, accepter UNIQUEMENT ce fichier exact (cf.
      agent_tests/tests/test_bg_tree_lock.py : whitelist explicite).
    - Pour chaque chemin collecte `dir`, chercher `test_*.py` dans `dir/`
      (le parent direct) ; si present, verifier s'il est accepte.

    Scope limite a `scripts/` : c'est le scope du deploiement #18888. Les
    notebooks MyIA.AI.Notebooks/QuantConnect/scripts/test_algorithms.py
    et scripts/lean/test_check_grothendieck_readme.py sont des faux
    positifs pour cette garde-ci (le premier est un runner, pas un test
    pytest ; le second est hors scope de #18888 et adresse par #11255).
    """
    if not collected_paths:
        return []

    collected_dirs: set[Path] = set()
    collected_files: set[Path] = set()
    parent_dirs: set[Path] = set()

    for p in collected_paths:
        resolved = (REPO_ROOT / p).resolve()
        if resolved.is_file():
            # Chemin fichier (whitelist explicite, ex. agent_tests/tests/test_bg_tree_lock.py).
            # On n'ajoute PAS le parent au scope de violation -- pytest ne
            # collecte QUE ce fichier, pas ses voisins. Les autres test_*.py
            # du meme dossier ne sont pas un probleme de cette garde-ci.
            collected_files.add(resolved)
        elif resolved.is_dir():
            collected_dirs.add(resolved)
            parent_dirs.add(resolved.parent)
        else:
            # Chemin declare mais inexistant : on l'ignore (peut-etre un
            # futur test). On ajoute juste le parent pour ne pas casser
            # la verification des voisins.
            parent_dirs.add(resolved.parent)

    violations: list[Path] = []
    for parent in parent_dirs:
        if not parent.exists():
            continue
        try:
            parent.relative_to(REPO_ROOT.resolve())
        except ValueError:
            continue
        # Scope limite a scripts/ (cf. issue #18888).
        if not _in_scope(parent):
            continue
        for entry in parent.glob("test_*.py"):
            if not entry.is_file():
                continue
            if not _is_collected(entry, collected_dirs, collected_files):
                violations.append(entry)

    return sorted(violations)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Garde anti-recidive test_*.py racine")
    parser.add_argument("--json", action="store_true", help="Sortie JSON")
    parser.add_argument("--workflow", type=Path, default=DEFAULT_WORKFLOW,
                        help=f"Chemin vers le YAML (defaut: {DEFAULT_WORKFLOW.relative_to(REPO_ROOT)})")
    args = parser.parse_args(argv)

    if not args.workflow.exists():
        print(f"FAIL: workflow absent: {args.workflow}", file=sys.stderr)
        return 2

    try:
        collected = parse_collected_paths(args.workflow)
    except PytestBlockNotFound as e:
        # #18896 (c.86) : si le workflow contient `pytest` mais que le
        # pattern multi-lignes ne matche pas, c'est un defaut de lecture
        # -- le garde rendait `ok=True` sans rien verifier. On remonte
        # un statut explicite (rc=2) et un message qui nomme la cause.
        print(f"FAIL: {e}", file=sys.stderr)
        return 2
    except Exception as e:
        print(f"FAIL: impossible de parser {args.workflow}: {e}", file=sys.stderr)
        return 2

    violations = find_violations(collected)

    if args.json:
        out = {
            "workflow": str(args.workflow.resolve().relative_to(REPO_ROOT)),
            "collected_paths": collected,
            "violations": [str(v.relative_to(REPO_ROOT)) for v in violations],
            "ok": not violations,
        }
        print(json.dumps(out, indent=2, ensure_ascii=False))
    else:
        if violations:
            print(f"FAIL: {len(violations)} fichier(s) test_*.py a un niveau trop haut :")
            for v in violations:
                print(f"  - {v.relative_to(REPO_ROOT)}")
            print(f"\nChemins collectes (lus depuis le YAML) :")
            for c in collected:
                print(f"  - {c}")
            print(f"\nDeplacer dans le sous-dossier collecte adapte.")
            return 1
        print(f"OK: tous les test_*.py sont dans les chemins collectes.")
        try:
            wf_display = args.workflow.resolve().relative_to(REPO_ROOT)
        except ValueError:
            wf_display = args.workflow
        print(f"Chemins collectes (lus depuis {wf_display}) :")
        for c in collected:
            print(f"  - {c}")

    return 0 if not violations else 1


if __name__ == "__main__":
    sys.exit(main())