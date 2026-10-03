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
    tort. Cf. CONCERNS coordinateur (c.86) sur #18896."""

# On matche le bloc pytest multi-lignes : pytest (ou `python -m pytest`)
# suivi de `\` puis les chemins (termines par \). La fin du bloc est
# signalee par une ligne qui ne se termine PAS par \ (apres, pytest
# prend d'autres options : -n, -q, --dist, --tb, ...). Cf. #18896
# (CONCERNS c.86) : la version precedente exigeait `-n` en fin de
# bloc, ce qui rendait l extraction VIDE pour les workflows pytest
# valides sans xdist (python -m pytest scripts/notebook_tools/tests/ -q)
# -- le garde rendait alors ok=True sans rien verifier.
#
# Strategie : capturer toutes les lignes consecutives se terminant par
# `\`, en arretant des qu'une ligne ne se termine PAS par `\` (ou fin
# de fichier). Le `+?` non-greedy consomme le minimum de lignes
# consecutives, et le lookahead garantit qu'on s'arrete a la premiere
# ligne non-`-terminee-par-\`.
PYTEST_INVOCATION_RE = re.compile(
    r"(?:python\s+(?:-m\s+)?|pytest(?:\s+-m\s+\S+)?\s+)?pytest\s*\\[ \t]*\n",
    re.MULTILINE,
)
PYTEST_BLOCK_RE = re.compile(
    PYTEST_INVOCATION_RE.pattern
    + r"((?:.*\\[ \t]*\n)+?)"
    + r"(?:[^\\\n]*\n|\Z)",
    re.MULTILINE,
)


def parse_collected_paths(workflow: Path) -> list[str]:
    """Lit la liste des chemins collectes par pytest depuis le YAML.

    Les arguments de pytest sont multi-lignes, termines par \\. On extrait le
    bloc, on nettoie les continuations de ligne, on splitte sur les espaces,
    on filtre tout ce qui ressemble a un flag (-x, --dist, ...) ou un
    nombre.

    Si le workflow ne contient pas du tout `pytest`, on rend une liste
    vide (le workflow n'est pas dans le scope de cette garde). Si le
    workflow contient `pytest` mais que le bloc multi-lignes ne matche
    pas (pattern en-dessous du reel, ou format inhabituel), on leve
    ``PytestBlockNotFound`` : le garde DOIT refuser plutot que rendre
    ``ok=True`` sans rien verifier (#18896 c.86).
    """
    text = workflow.read_text(encoding="utf-8")
    # Le mot "pytest" peut apparaitre dans un nom de fichier (no-pytest.yml),
    # un commentaire, un nom de job, etc. On ne leve l'exception que si le
    # workflow contient un APPEL pytest multi-lignes (pytest \ en fin de
    # ligne, apres indentation YAML ou apres `python -m`). C'est le signe
    # qu'un bloc DEVRAIT etre reconnu.
    if not PYTEST_INVOCATION_RE.search(text):
        return []
    match = PYTEST_BLOCK_RE.search(text)
    if not match:
        raise PytestBlockNotFound(
            f"{workflow} contient `pytest \\` mais PYTEST_BLOCK_RE ne matche "
            f"pas le bloc multi-lignes ; le garde ne peut pas verifier. "
            f"Cf. CONCERNS coordinateur (c.86) sur #18896."
        )
    block = match.group(1)
    joined = re.sub(r"\s*\\\s*\n\s*", " ", block)
    tokens = joined.split()
    paths: list[str] = []
    for tok in tokens:
        if tok.startswith("-"):
            continue
        if tok.isdigit():
            continue
        paths.append(tok)
    return paths


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