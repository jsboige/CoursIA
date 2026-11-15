#!/usr/bin/env python3
"""Plancher explicite des tests ``@requires_jvm`` — forme 2 de #23542.

Constat mesure le 2026-10-30 a la tete de #23279 : le dossier
``SymbolicAI/ArgumentAnalysis/tests/`` est collecte et execute par
``Scripts Tests (CPU)``, mais **aucun workflow n'installe ``jpype``** et les
jars Tweety sont gitignores. Tous les tests marques ``@requires_jvm`` sont donc
**sautes en CI** : la collecte est verte, la couverture semantique des ADF est
absente, et rien ne le dit.

Le plancher de collecte voisin (``ARGUMENT_ANALYSIS_TESTS_FLOOR``) ne voit pas
ce trou par construction : un test saute est un test **collecte**. Ce census
compte donc les marqueurs eux-memes, statiquement, et rougit dans les deux sens :

* **croissance non declaree** — un test ``@requires_jvm`` ajoute sans bumper
  ``--declared`` dans la meme PR : le trou s'agrandit en silence ;
* **baisse** — un marqueur retire ou un test supprime : c'est une perte de
  couverture, et elle doit etre un geste visible, pas un effet de bord.

L'egalite est le seul etat vert. Le nombre declare vit dans le workflow qui
appelle cet organe, a cote des autres planchers de collecte.

Usage :
    python scripts/ci/check_jvm_test_census.py --declared 8
    python scripts/ci/check_jvm_test_census.py --declared 8 --json
"""

from __future__ import annotations

import argparse
import ast
import json
import sys
from pathlib import Path

DEFAULT_TESTS_DIR = "MyIA.AI.Notebooks/SymbolicAI/ArgumentAnalysis/tests"

#: Nom du marqueur compte. La definition (`requires_jvm = pytest.mark.skipif(...)`)
#: est une affectation de module, pas un decorateur : elle n'est jamais comptee.
MARKER_NAME = "requires_jvm"


def _decorator_name(node: ast.expr) -> str | None:
    """Nom porte par un noeud de decorateur, appele ou non."""
    if isinstance(node, ast.Call):
        node = node.func
    if isinstance(node, ast.Attribute):
        return node.attr
    if isinstance(node, ast.Name):
        return node.id
    return None


def census_file(path: Path) -> list[str]:
    """Noms qualifies des objets decores par ``@requires_jvm`` dans un fichier."""
    try:
        tree = ast.parse(path.read_text(encoding="utf-8"))
    except (OSError, SyntaxError, UnicodeDecodeError):
        return []
    found: list[str] = []
    for node in ast.walk(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            continue
        if any(_decorator_name(d) == MARKER_NAME for d in node.decorator_list):
            found.append(node.name)
    return found


def census(tests_dir: Path) -> dict[str, list[str]]:
    """Census par fichier, trie, fichiers sans marqueur omis."""
    result: dict[str, list[str]] = {}
    for path in sorted(tests_dir.glob("test_*.py")):
        names = census_file(path)
        if names:
            result[path.name] = sorted(names)
    return result


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tests-dir", default=DEFAULT_TESTS_DIR)
    parser.add_argument(
        "--declared",
        type=int,
        required=True,
        help="Nombre de tests @requires_jvm declare dans le workflow appelant.",
    )
    parser.add_argument("--json", action="store_true", help="Verdict machine.")
    args = parser.parse_args(argv)

    tests_dir = Path(args.tests_dir)
    if not tests_dir.is_dir():
        print(f"::error::census impossible : {tests_dir} n'est pas un dossier.")
        return 1

    by_file = census(tests_dir)
    measured = sum(len(names) for names in by_file.values())

    if args.json:
        print(
            json.dumps(
                {
                    "tests_dir": str(tests_dir),
                    "declared": args.declared,
                    "measured": measured,
                    "by_file": by_file,
                    "verdict": (
                        "OK"
                        if measured == args.declared
                        else "GROWTH" if measured > args.declared else "SHRINK"
                    ),
                },
                indent=2,
                ensure_ascii=False,
            )
        )
        return 0 if measured == args.declared else 1

    for name, tests in by_file.items():
        print(f"  {len(tests):3d}  {name}  ({', '.join(tests)})")

    if measured == args.declared:
        print(
            f"OK: {measured} test(s) @requires_jvm (plancher declare {args.declared}) "
            "-- tous sautes en CI tant que jpype n'est pas installe (#23542)."
        )
        return 0

    if measured > args.declared:
        delta = measured - args.declared
        print(
            f"::error::Le trou @requires_jvm grandit sans declaration : "
            f"{measured} test(s), plancher declare {args.declared} (+{delta}). "
            "Bumper --declared dans la meme PR et le dire dans le body "
            "(ces tests ne tournent pas en CI, #23542)."
        )
        return 1

    print(
        f"::error::Perte de couverture @requires_jvm : {measured} test(s), "
        f"plancher declare {args.declared} ({measured - args.declared}). "
        "Un marqueur a ete retire ou un test supprime -- geste a declarer "
        "au meme titre qu'une hausse."
    )
    return 1


if __name__ == "__main__":
    sys.exit(main())
