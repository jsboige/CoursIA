#!/usr/bin/env python3
"""Sélection des suites de tests par chemin touché.

P2 du plan « CI à deux étages » (#25510) : étant donné l'ensemble des fichiers
touchés par une PR, dire quelles suites de tests sont **concernées** par ce
changement, pour ne lancer que celles-là au lieu de la totalité.

Toutes les règles sont **dérivées du dépôt** — noms de fichiers, contenu des
fichiers de test, arborescence. Aucune table de correspondance n'est écrite à
la main, donc aucune ne peut dériver du code qu'elle décrit. C'est la réponse
à la question que pose la phase P0 : la carte « chemin touché → tests à
lancer » n'existait pas dans le dépôt ; elle se **reconstruit** à partir des
artefacts qui la décrivent déjà.

Règles de sélection (chacune porte une preuve : le fichier et la ligne) :

  R1 identité     — un fichier de test touché sélectionne sa suite locale
                    (les tests de son dossier), son fichier lui-même en tête.
  R2 convention   — un fichier source `X.py` sélectionne tout fichier de test
                    nommé `test_X.py` ou `X_test.py`.
  R3 référence    — un fichier touché sélectionne les tests dont le source le
                    cite (chemin relatif, chemin pointé, ou nom de fichier) ;
                    la preuve est la ligne de citation.
  R4 portée dépôt — un test qui parcourt une arborescence est **toujours**
                    sélectionné : par construction, il peut couvrir
                    n'importe quel changement. Deux variantes sont
                    distinguées : racine dépôt explicite (R4), ou racine non
                    identifiable (R4-bis, prudent). Le rapport donne le
                    plancher de sélection que cela représente.
  R5 suite locale — un fichier non-test posé dans un dossier de tests
                    sélectionne les tests de ce dossier (ils l'importent).
  R6 conftest     — un `conftest.py` touché sélectionne les tests de son
                    dossier et de ses sous-dossiers.

Usage :
    python scripts/ci/select_tests.py --diff origin/main...HEAD
    python scripts/ci/select_tests.py --changed scripts/ci/select_tests.py
    python scripts/ci/select_tests.py --diff origin/main...HEAD --json

Exit 0 = sélection produite. Exit 1 = `--fail-on-uncovered` et un fichier
touché n'est couvert par aucune règle. Exit 2 = instrument indisponible
(diff illisible, dépôt introuvable).

Ce que l'instrument ne fait pas : il ne décide pas de la bascule. La
sélection est **advisory** — elle est produite et mesurée pendant la phase
d'ombre, avant qu'une CI ne s'y fie (P4).
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path

# Dossiers Ignores lors du parcours de l'arborescence : ils ne portent pas de
# suites du depot et leur parcours dominerait le temps de l'instrument.
SKIP_DIRS = frozenset(
    {
        ".git",
        ".venv",
        "venv",
        "env",
        "node_modules",
        "__pycache__",
        ".mypy_cache",
        ".pytest_cache",
        ".ruff_cache",
        ".ipynb_checkpoints",
        "site-packages",
        "dist",
        "build",
        ".tmp",
        ".worktrees",
    }
)

# Marqueurs de parcours d'arborescence : un test qui les emploie avec une
# racine depot couvre tout changement (regle R4). Les motifs sont volontairement
# stricts -- un `rglob` sur le repertoire du test lui-meme ne parcourt pas le
# depot, et le distinguer evite de traiter comme toujours-selectionnes des
# suites qui ne le sont pas.
WALK_ROOT_RE = re.compile(
    r"(REPO_ROOT|repo_root|REPO_DIR|repo_dir|repo_path)\s*\.\s*(rglob|glob|iglob)\s*\("
    r"|os\.walk\s*\(\s*(REPO_ROOT|repo_root|REPO_DIR|repo_dir|repo_path)"
    r"|parents\[\d+\]\s*\.\s*(rglob|glob|iglob)\s*\("
)

# Parcours d'arborescence dont la racine n'est pas identifiable : le test peut
# parcourir le depot ou seulement son dossier. On le traite comme toujours
# selectionne (le cout est un plancher de selection, pas un risque de faux
# vert), et on le compte a part pour que le rapport dise quelle part du
# toujours-selectionne est stricte et laquelle est prudente.
WALK_ANY_RE = re.compile(r"(rglob|iglob)\s*\(|os\.walk\s*\(|\.glob\s*\(")


def is_test_file(path: Path) -> bool:
    """Vrai pour un fichier de test pytest (`test_*.py` ou `*_test.py`)."""
    name = path.name
    return name.startswith("test_") or name.endswith("_test.py")


def is_conftest(path: Path) -> bool:
    return path.name == "conftest.py"


def _git_tracked_files(root: Path) -> list[Path] | None:
    """Fichiers ``*.py`` suivis par git, ou None si git n'est pas disponible.

    #25510 annexe : le parcours ``os.walk`` enumere aussi les repertoires non
    suivis -- dans un checkout de developpement qui contient
    ``.claude/worktrees/``, la meme selection voit 250 fichiers de test la ou
    la CI en voit 126, et la mesure locale ne correspond plus a celle de la
    CI. ``git ls-files`` enumere exactement les fichiers suivis : c'est la
    source de verite du depot, et le repli ``os.walk`` ne sert qu'aux arbres
    sans git (fixtures de test).
    """
    proc = subprocess.run(
        ["git", "-C", str(root), "rev-parse", "--show-toplevel"],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
    )
    if proc.returncode != 0:
        return None
    # ``ls-files`` rend des chemins relatifs a la racine git : si ``root``
    # n'est PAS cette racine (un sous-dossier du depot, un scratch interne),
    # composer ``root / chemin`` fabriquerait des chemins faux. On ne garde
    # l'enumeration git que si les deux racines coincident.
    toplevel = Path(proc.stdout.strip().replace("\\", "/")).resolve()
    if toplevel != root.resolve():
        return None
    proc = subprocess.run(
        ["git", "-C", str(root), "ls-files", "--", "*.py"],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
    )
    if proc.returncode != 0:
        return None
    return [root / line.strip() for line in proc.stdout.splitlines()
            if line.strip().endswith(".py")]


def iter_all_files(root: Path) -> list[Path]:
    """Enumere les fichiers Python du depot : suivis git, sinon parcours."""
    tracked = _git_tracked_files(root)
    if tracked is not None:
        return tracked
    found: list[Path] = []
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d not in SKIP_DIRS and not d.startswith(".tox")]
        base = Path(dirpath)
        for name in filenames:
            if name.endswith(".py"):
                found.append(base / name)
    return found


def read_text(path: Path) -> str:
    """Contenu texte d'un fichier, tolérant aux erreurs d'encodage."""
    try:
        return path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return ""


def first_occurrence(text: str, token: str) -> int | None:
    """Numéro de ligne (1-based) de la première occurrence du token."""
    idx = text.find(token)
    if idx < 0:
        return None
    return text.count("\n", 0, idx) + 1


# Fonction de test : le compte des fonctions est une ESTIMATION du volume de
# tests -- la parametrisation en fait creaitre le nombre a l'execution -- mais
# c'est la seule mesure honnete disponible sans lancer pytest.
TEST_FUNCTION_RE = re.compile(r"^\s*(?:async\s+)?def\s+(test_\w+)", re.MULTILINE)


def count_test_functions(text: str) -> int:
    """Nombre de fonctions de test definies dans un fichier."""
    return len(TEST_FUNCTION_RE.findall(text))


@dataclass
class Reason:
    """Pourquoi un fichier de test est sélectionné."""

    rule: str
    source: str
    evidence: str

    def as_dict(self) -> dict[str, str]:
        return {"rule": self.rule, "source": self.source, "evidence": self.evidence}


@dataclass
class Selection:
    """Résultat de la sélection."""

    changed: list[str] = field(default_factory=list)
    selected: dict[str, list[Reason]] = field(default_factory=dict)
    uncovered: list[str] = field(default_factory=list)
    total_tests: int = 0
    repo_wide: list[str] = field(default_factory=list)
    parcours_non_racine: list[str] = field(default_factory=list)
    selected_test_functions: int = 0
    total_test_functions: int = 0
    all_suites: list[str] = field(default_factory=list)

    def suites(self) -> list[str]:
        """Dossiers de suites sélectionnés (unité de lancement pytest)."""
        return sorted({str(Path(p).parent).replace("\\", "/") for p in self.selected})

    def excluded_suites(self) -> list[str]:
        """Suites du dépôt que la sélection écarte."""
        kept = set(self.suites())
        return [s for s in self.all_suites if s not in kept]

    def as_dict(self) -> dict[str, object]:
        return {
            "changed": self.changed,
            "selected": {
                path: [r.as_dict() for r in reasons] for path, reasons in sorted(self.selected.items())
            },
            "selected_suites": self.suites(),
            "excluded_suites": self.excluded_suites(),
            "uncovered": self.uncovered,
            "repo_wide": self.repo_wide,
            "parcours_non_racine": self.parcours_non_racine,
            "stats": {
                "fichiers_touches": len(self.changed),
                "fichiers_de_test_selectionnes": len(self.selected),
                "fichiers_de_test_du_depot": self.total_tests,
                "fonctions_de_test_selectionnees": self.selected_test_functions,
                "fonctions_de_test_du_depot": self.total_test_functions,
                "reduction": (
                    round(1.0 - len(self.selected) / self.total_tests, 4) if self.total_tests else None
                ),
                "reduction_fonctions": (
                    round(1.0 - self.selected_test_functions / self.total_test_functions, 4)
                    if self.total_test_functions
                    else None
                ),
            },
        }


def repo_relative(root: Path, path: Path) -> str:
    try:
        return path.resolve().relative_to(root.resolve()).as_posix()
    except ValueError:
        return path.as_posix()


def reference_tokens(rel_path: str) -> list[str]:
    """Formes sous lesquelles un fichier peut être cité dans un test."""
    rel = rel_path.replace("\\", "/")
    tokens = [rel, Path(rel).name]
    if rel.endswith(".py"):
        dotted = rel[: -len(".py")].replace("/", ".")
        tokens.append(dotted)
        stem = Path(rel).stem
        tokens.append(stem)
    # Un chemin cite avec des antislashs (Windows) est aussi une mention.
    if "/" in rel:
        tokens.append(rel.replace("/", "\\"))
    return [t for t in dict.fromkeys(tokens) if len(t) > 3]


def select(root: Path, changed: list[str]) -> Selection:
    """Applique les règles R1-R6 aux fichiers touchés."""
    all_files = iter_all_files(root)
    test_files = [p for p in all_files if is_test_file(p)]
    by_dir: dict[str, list[Path]] = {}
    for p in test_files:
        by_dir.setdefault(str(p.parent), []).append(p)

    contents: dict[Path, str] = {}
    for p in test_files:
        contents[p] = read_text(p)

    functions_per_file = {p: count_test_functions(contents[p]) for p in test_files}
    selection = Selection(changed=sorted(changed), total_tests=len(test_files))
    selection.total_test_functions = sum(functions_per_file.values())
    selection.all_suites = sorted({repo_relative(root, p.parent) for p in test_files})

    def add(test_path: Path, rule: str, source: str, evidence: str) -> None:
        rel = repo_relative(root, test_path)
        bucket = selection.selected.setdefault(rel, [])
        if not any(r.rule == rule and r.source == source for r in bucket):
            bucket.append(Reason(rule=rule, source=source, evidence=evidence))

    covered_sources: set[str] = set()

    # R4 -- les tests qui parcourent une arborescence sont toujours
    # selectionnes : par construction, ils peuvent couvrir n'importe quel
    # changement. La variante stricte (racine depot explicite) et la variante
    # prudente (racine non identifiable) sont comptees separement.
    for p in test_files:
        text = contents[p]
        strict = WALK_ROOT_RE.search(text)
        broad = WALK_ANY_RE.search(text)
        if strict:
            line = text.count("\n", 0, strict.start()) + 1
            rel = repo_relative(root, p)
            selection.repo_wide.append(rel)
            add(p, "R4-portee-depot", rel, f"parcours de l'arborescence du depot (l. {line})")
        elif broad:
            line = text.count("\n", 0, broad.start()) + 1
            rel = repo_relative(root, p)
            selection.parcours_non_racine.append(rel)
            add(p, "R4-bis-parcours", rel, f"parcours d'arborescence, racine non identifiee (l. {line})")

    for rel in selection.changed:
        abs_path = root / rel
        parent = str(abs_path.parent)
        local_tests = by_dir.get(parent, [])

        if is_conftest(abs_path):
            # R6 -- le conftest agit sur tout son dossier et ses sous-dossiers.
            prefix = parent + os.sep
            for p in test_files:
                if str(p).startswith(prefix):
                    add(p, "R6-conftest", rel, "conftest.py du dossier")
            covered_sources.add(rel)
            continue

        if is_test_file(abs_path):
            # R1 -- un test touche selectionne sa suite locale, lui-meme en tete.
            for p in local_tests:
                add(p, "R1-identite", rel, "suite locale du fichier de test touche")
            add(abs_path, "R1-identite", rel, "fichier de test touche")
            covered_sources.add(rel)
            continue

        # R2 -- convention de nom : X.py -> test_X.py / X_test.py.
        stem = abs_path.stem
        for p in test_files:
            if p.stem in (f"test_{stem}", f"{stem}_test"):
                add(p, "R2-convention", rel, f"convention de nom ({p.name})")
                covered_sources.add(rel)

        # R3 -- reference textuelle, avec la ligne de citation en preuve.
        for token in reference_tokens(rel):
            for p in test_files:
                line = first_occurrence(contents[p], token)
                if line is None:
                    continue
                add(p, "R3-reference", rel, f"cite '{token}' (l. {line})")
                covered_sources.add(rel)

        # R5 -- fichier non-test pose dans un dossier de tests.
        if local_tests:
            for p in local_tests:
                add(p, "R5-suite-locale", rel, "fichier non-test dans un dossier de tests")
            covered_sources.add(rel)

    selection.uncovered = [rel for rel in selection.changed if rel not in covered_sources]
    selection.repo_wide.sort()
    counts_by_rel = {repo_relative(root, p): n for p, n in functions_per_file.items()}
    selection.selected_test_functions = sum(
        counts_by_rel.get(rel, 0) for rel in selection.selected
    )
    return selection


def changed_from_git(root: Path, diff_range: str) -> list[str]:
    """Fichiers modifies par la plage de commits donnee."""
    cmd = ["git", "-C", str(root), "diff", "--name-only", diff_range]
    proc = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8", errors="replace")
    if proc.returncode != 0:
        raise RuntimeError((proc.stderr or proc.stdout or "git diff a echoue").strip())
    return [line.strip() for line in proc.stdout.splitlines() if line.strip()]


def render_markdown(selection: Selection) -> str:
    """Rendu lisible pour un corps de PR ou un commentaire de revue."""
    stats = selection.as_dict()["stats"]  # type: ignore[index]
    lines = ["## Suites de tests concernees", ""]
    lines.append(f"- fichiers touches : **{stats['fichiers_touches']}**")
    lines.append(
        f"- fichiers de test selectionnes : **{stats['fichiers_de_test_selectionnes']}** "
        f"sur {stats['fichiers_de_test_du_depot']} dans le depot"
    )
    lines.append(
        f"- fonctions de test selectionnees : **{stats['fonctions_de_test_selectionnees']}** "
        f"sur {stats['fonctions_de_test_du_depot']} (estimation par lecture du source)"
    )
    reduction = stats["reduction"]
    if reduction is not None:
        lines.append(f"- reduction mesuree (fichiers) : **{round(reduction * 100)} %**")
    reduction_fonctions = stats["reduction_fonctions"]
    if reduction_fonctions is not None:
        lines.append(f"- reduction estimee (fonctions) : **{round(reduction_fonctions * 100)} %**")
    lines.append(f"- suites ecartees : **{len(selection.excluded_suites())}**")
    lines.append(
        f"- toujours selectionnes (parcours d'arborescence) : "
        f"**{len(selection.repo_wide)}** a racine depot explicite, "
        f"**{len(selection.parcours_non_racine)}** a racine non identifiee"
    )
    if selection.uncovered:
        lines.append("")
        lines.append("### Fichiers touches sans test selectionne")
        lines.append("")
        for rel in selection.uncovered:
            lines.append(f"- `{rel}`")
    lines.append("")
    lines.append("### Fichiers de test selectionnes")
    lines.append("")
    lines.append("| fichier de test | regle | fichier touche | preuve |")
    lines.append("|---|---|---|---|")
    for path, reasons in sorted(selection.selected.items()):
        for reason in reasons:
            lines.append(
                f"| `{path}` | {reason.rule} | `{reason.source}` | {reason.evidence} |"
            )
    return "\n".join(lines) + "\n"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--changed",
        action="append",
        default=[],
        metavar="PATH",
        help="fichier touche (repetable)",
    )
    parser.add_argument(
        "--diff",
        default=None,
        metavar="RANGE",
        help="plage de commits dont lire les fichiers touches (defaut : origin/main...HEAD)",
    )
    parser.add_argument("--repo-root", type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument("--json", action="store_true", help="sortie JSON")
    parser.add_argument(
        "--fail-on-uncovered",
        action="store_true",
        help="exit 1 si un fichier touche n'est couvert par aucune regle",
    )
    args = parser.parse_args(argv)

    root = args.repo_root.resolve()
    if not root.is_dir():
        print(f"racine de depot introuvable : {root}", file=sys.stderr)
        return 2

    changed = list(args.changed)
    if not changed:
        diff_range = args.diff or "origin/main...HEAD"
        try:
            changed = changed_from_git(root, diff_range)
        except RuntimeError as exc:
            print(f"lecture du diff impossible ({diff_range}) : {exc}", file=sys.stderr)
            return 2

    selection = select(root, changed)

    if args.json:
        print(json.dumps(selection.as_dict(), ensure_ascii=False, indent=2))
    else:
        print(render_markdown(selection), end="")

    if args.fail_on_uncovered and selection.uncovered:
        print(
            f"{len(selection.uncovered)} fichier(s) touche(s) sans test selectionne",
            file=sys.stderr,
        )
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
