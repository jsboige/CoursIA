#!/usr/bin/env python3
"""Detecteur : stub d'exercice qui rend une verite en dur (issue #14817).

Un stub d'exercice (cellule portant un marqueur ``TODO etudiant``) ne doit pas
rendre une valeur de verite affirmative -- la sortie committee affirmerait
alors quelque chose de faux sans aucun signe la distinguant d'un resultat
verifie (le cercle convexe, la fonction a saut continue, la solution unique).

Signature detectee : une ``def`` dont le corps (hors docstring) se reduit a des
``return`` d'expressions LITTERALES contenant un ``True``. Une implementation
reelle calcule avant de retourner (Assign/For/If/Call...) et n'est jamais
flaggee ; un stub neutre (``None``/``False``/``[]``/``0``) ne contient pas de
``True`` et n'est jamais flagge.

Controles embarques (--self-check) :
 - positif : les quatre cellules pre-correction de #14817 doivent rougir ;
 - negatif : stubs neutres et implementations reelles (retour conditionnel,
   calcul puis ``return True``) ne doivent pas rougir.
"""

from __future__ import annotations

import argparse
import ast
import json
import sys
from pathlib import Path

TODO_MARKERS = ("TODO etudiant",)

LITERAL_CONTAINERS = (ast.Dict, ast.List, ast.Set, ast.Tuple)


def _is_literal_expr(expr: ast.AST) -> bool:
    """True si l'expression ne contient que des constantes et des conteneurs."""
    if isinstance(expr, ast.Constant):
        return True
    if isinstance(expr, LITERAL_CONTAINERS):
        return all(
            _is_literal_expr(e)
            for e in ast.iter_child_nodes(expr)
            if not isinstance(e, ast.expr_context)
        )
    return False


def _contains_true(expr: ast.AST) -> bool:
    return any(
        isinstance(n, ast.Constant) and n.value is True
        for n in ast.walk(expr)
    )


def _body_without_docstring(fn: ast.FunctionDef | ast.AsyncFunctionDef) -> list[ast.stmt]:
    body = list(fn.body)
    if (
        body
        and isinstance(body[0], ast.Expr)
        and isinstance(body[0].value, ast.Constant)
        and isinstance(body[0].value.value, str)
    ):
        body = body[1:]
    return body


def find_stub_truths(source: str) -> list[str]:
    """Rend les noms des fonctions-stubs fautives du source Python."""
    try:
        tree = ast.parse(source)
    except SyntaxError:
        return []
    hits = []
    for node in ast.walk(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        body = _body_without_docstring(node)
        if not body or not all(isinstance(s, ast.Return) and s.value is not None for s in body):
            continue
        if all(_is_literal_expr(s.value) for s in body) and any(_contains_true(s.value) for s in body):
            hits.append(node.name)
    return hits


def scan_notebook(path: Path) -> list[dict]:
    findings = []
    try:
        nb = json.loads(path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, UnicodeDecodeError):
        return findings
    for i, cell in enumerate(nb.get("cells", [])):
        if cell.get("cell_type") != "code":
            continue
        src = "".join(cell.get("source", []))
        if not any(m in src for m in TODO_MARKERS):
            continue
        for fn in find_stub_truths(src):
            findings.append(
                {"notebook": str(path), "cell": i, "function": fn}
            )
    return findings


POSITIVE_FIXTURES = [
    (
        "GT-04c pre-fix",
        'def verify_brouwer_hypotheses(domain_points, function_values):\n'
        '    """Doc."""\n'
        '    # TODO etudiant : implementer la verification\n'
        '    return {"compact": True, "convex": True, "continuous": True, "all_satisfied": True}  # TODO etudiant\n',
        ["verify_brouwer_hypotheses"],
    ),
    (
        "Sudoku-18 pre-fix",
        'def has_unique_solution(grid):\n'
        '    """Doc."""\n'
        '    # TODO etudiant : implementez la verification d\'unicite\n'
        '    return True  # TODO\n',
        ["has_unique_solution"],
    ),
    (
        "GT-04 pre-fix",
        'def exercice_nash_3x3_rps_biaise() -> dict:\n'
        '    """Doc."""\n'
        '    return {"A_biased": None, "sigma_row": None, "sigma_col": None, "is_uniform": True}  # TODO etudiant\n',
        ["exercice_nash_3x3_rps_biaise"],
    ),
    (
        "SC-22 pre-fix",
        'def analyze_parallelism(transactions: list) -> dict:\n'
        '    """Doc."""\n'
        '    # TODO etudiant : implementez analyze_parallelism\n'
        '    return {"parallelizable_pairs": [], "conflicts": [], "max_parallel": 0, "sequential_only": True}\n',
        ["analyze_parallelism"],
    ),
    (
        "SK-04 pre-fix",
        'def is_allowed(self) -> bool:\n'
        '    """Doc."""\n'
        '    # TODO etudiant : implementer la logique de rate limiting\n'
        '    return True  # TODO etudiant : remplacer par la vraie logique\n',
        ["is_allowed"],
    ),
    (
        "App-16 pre-fix",
        'def validate_solution(grid, dictionary, words):\n'
        '    """Doc."""\n'
        '    # TODO etudiant : implementer la validation\n'
        '    return True, []  # TODO etudiant : remplacer par la vraie validation\n',
        ["validate_solution"],
    ),
]

NEGATIVE_FIXTURES = [
    (
        "stub None",
        'def f(x):\n    """Doc."""\n    # TODO etudiant\n    return None  # TODO etudiant\n',
    ),
    (
        "stub False",
        'def f(x):\n    # TODO etudiant\n    return False\n',
    ),
    (
        "stub liste vide",
        'def f(x):\n    # TODO etudiant\n    return []\n',
    ),
    (
        "stub dict sans True",
        'def f(x):\n    # TODO etudiant\n    return {"a": None, "b": 0, "c": []}\n',
    ),
    (
        "post-fix App-16 : tuple neutre",
        'def f(x):\n    # TODO etudiant : implementer la validation\n    return None, []  # TODO etudiant : remplacer par la vraie validation\n',
    ),
    (
        "post-fix GT-04c : marker print puis dict neutre",
        'def f(x):\n    # TODO etudiant : implementer la verification\n    print("Exercice a completer")\n    return {"compact": None, "convex": None, "continuous": None, "all_satisfied": None}\n',
    ),
    (
        "implementation reelle puis return True",
        'def f(x):\n    # TODO etudiant : note dans une AUTRE fonction\n'
        '    y = sum(x)\n    return y > 0 or True\n',
    ),
    (
        "retour conditionnel (IfExp)",
        'def f(x):\n    # TODO etudiant\n    return True if x else False\n',
    ),
    (
        "implementation qui appelle",
        'def f(x):\n    # TODO etudiant\n    return bool(check(x))\n',
    ),
    (
        "pass seul",
        'def f(x):\n    # TODO etudiant\n    pass\n',
    ),
]


def self_check() -> int:
    failures = 0
    for name, src, expected in POSITIVE_FIXTURES:
        got = find_stub_truths(src)
        ok = got == expected
        failures += 0 if ok else 1
        print(f"  POSITIF {name:<42} {'OK' if ok else f'ECHEC (rendu {got})'}")
    for name, src in NEGATIVE_FIXTURES:
        got = find_stub_truths(src)
        ok = got == []
        failures += 0 if ok else 1
        print(f"  NEGATIF {name:<42} {'OK' if ok else f'ECHEC (rendu {got})'}")
    print(f"self-check: {'PASS' if failures == 0 else f'{failures} ECHEC(S)'}")
    return 1 if failures else 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paths", nargs="*", help="notebooks ou repertoires a scanner")
    parser.add_argument("--self-check", action="store_true", help="executer les controles embarques")
    parser.add_argument("--json", action="store_true", help="sortie JSON")
    args = parser.parse_args()

    if args.self_check:
        return self_check()

    findings: list[dict] = []
    for p in args.paths:
        path = Path(p)
        if path.is_dir():
            notebooks = path.rglob("*.ipynb")
        else:
            notebooks = [path]
        for nb_path in notebooks:
            if any(part in {"_archive", ".ipynb_checkpoints", ".lake", "node_modules"} for part in nb_path.parts):
                continue
            findings.extend(scan_notebook(nb_path))

    if args.json:
        print(json.dumps(findings, ensure_ascii=False, indent=1))
    else:
        for f in findings:
            print(f"{f['notebook']} cell {f['cell']}: fonction-stub '{f['function']}' rend un literal True")
        print(f"{len(findings)} stub(s) fautif(s)")
    return 1 if findings else 0


if __name__ == "__main__":
    sys.exit(main())
