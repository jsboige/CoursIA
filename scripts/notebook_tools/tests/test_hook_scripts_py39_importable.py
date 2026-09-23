"""Garde : les scripts de hook pre-commit restent importables sous Python 3.9.

Contexte (#17264). Les hooks `repo: local` de ce depot sont lances via
`entry: python <script>` — donc avec le `python` **du shell**, pas celui de la CI.
Or un env Python 3.9 y est legitime : c'est la contrainte de PyPhi 1.2.0 pour la
serie IIT/ICT, et il se retrouve en tete de `PATH` des qu'une lane re-execute un
notebook ICT. Le 2026-09-21, **deux** scripts de hook ont crashe a l'import :

    validate_pr_notebooks.py:128   def get_changed_notebooks(base: str, paths: list[str] | None = None)
    check_subprocess_encoding.py:133   def git_out(*args: str) -> str | None
    -> TypeError: unsupported operand type(s) for |: ...

Une union PEP 604 dans une annotation est evaluee **au moment du `def`**, donc a
l'import du module, donc au premier `git commit` de la lane. Trois commits de
notebooks valides ont echoue d'affilee pour cette raison, et un `git commit | tail`
a masque leur code de retour.

Ce que ce garde verifie, pour chaque script de hook **et** pour sa cloture d'import :

1. la grammaire est acceptee par un analyseur 3.9 (`ast.parse(feature_version=(3, 9))`)
   — attrape `match`, les f-strings `=`, etc. ;
2. aucune annotation n'utilise `X | Y` sans `from __future__ import annotations`.

LIMITE, ecrite ici pour ne pas etre surinterpretee : ces controles sont
**necessaires mais pas suffisants**. Un module peut encore echouer a l'import sous
3.9 pour une cause que le garde ne couvre pas (union PEP 604 au *runtime* dans un
`isinstance`, API 3.10+, dependance tierce absente). Il couvre les **deux mecanismes
qui ont effectivement casse**, pas l'importabilite 3.9 en general.

Perimetre volontairement etroit : les autres modules qui portent une annotation
PEP 604 sans future-import ne sont **pas** des hooks et tournent sous le `python`
de la CI — hors scope. La mesure est jointe au body de la PR (#17264) :

    scripts/** hors tests   32 offender(s) / 478 module(s), dont 0 dans la cloture
    scripts/** tests inclus 55 offender(s) / 969 module(s), dont 0 dans la cloture

**Zero dans la cloture** est le resultat qui compte : le garde couvre exactement
la ou le defaut casse en production, et n'impose rien ailleurs. Reproduire cette
mesure avec les deux helpers de ce fichier (`_has_future_annotations`,
`_pep604_annotation_lines`) sur un `rglob("*.py")`.
"""

import ast
import pathlib
import re

import pytest

REPO_ROOT = pathlib.Path(__file__).resolve().parents[3]
CONFIG = REPO_ROOT / ".pre-commit-config.yaml"
SEARCH_DIRS = (REPO_ROOT / "scripts" / "notebook_tools", REPO_ROOT / "scripts")


def _entry_scripts() -> list[pathlib.Path]:
    """Les `<script>.py` cites dans une ligne `entry:` du config pre-commit.

    Lus depuis le config, jamais ecrits en dur : un hook ajoute demain entre
    automatiquement dans le perimetre.
    """
    text = CONFIG.read_text(encoding="utf-8")
    paths = []
    for line in re.findall(r"entry:\s*(.+)", text):
        for token in line.split():
            if token.endswith(".py"):
                candidate = REPO_ROOT / token.replace("\\", "/")
                if candidate.exists():
                    paths.append(candidate)
    assert paths, f"aucun script de hook trouve dans {CONFIG}"
    return sorted(set(paths))


def _resolve(module: str) -> pathlib.Path | None:
    parts = module.split(".")
    for directory in SEARCH_DIRS:
        candidate = directory.joinpath(*parts).with_suffix(".py")
        if candidate.exists():
            return candidate
        candidate = directory.joinpath(*parts) / "__init__.py"
        if candidate.exists():
            return candidate
    return None


def _imported_modules(path: pathlib.Path) -> set[str]:
    tree = ast.parse(path.read_text(encoding="utf-8", errors="replace"))
    found: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            found.update(alias.name for alias in node.names)
        elif isinstance(node, ast.ImportFrom) and node.module and node.level == 0:
            found.add(node.module)
            found.update(f"{node.module}.{alias.name}" for alias in node.names)
    return found


def _closure() -> list[pathlib.Path]:
    """Scripts de hook + tout module atteignable par import au chargement.

    C'est la cloture qui compte, pas la liste d'entree : le script fautif de
    #17264 (`validate_pr_notebooks.py`) n'est lui-meme cite dans aucune ligne
    `entry:` — il est importe par `check_null_exec.py`.
    """
    seen: set[pathlib.Path] = set()
    queue = list(_entry_scripts())
    while queue:
        path = queue.pop()
        if path in seen:
            continue
        seen.add(path)
        for module in _imported_modules(path):
            resolved = _resolve(module)
            if resolved is not None and resolved not in seen:
                queue.append(resolved)
    return sorted(seen)


def _has_future_annotations(tree: ast.Module) -> bool:
    return any(
        isinstance(node, ast.ImportFrom)
        and node.module == "__future__"
        and any(alias.name == "annotations" for alias in node.names)
        for node in tree.body
    )


def _pep604_annotation_lines(tree: ast.Module) -> list[int]:
    """Lignes des unions `X | Y` rencontrees dans une annotation."""
    lines: list[int] = []
    for node in ast.walk(tree):
        if isinstance(node, (ast.arg, ast.AnnAssign)):
            annotation = node.annotation
        elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            annotation = node.returns
        else:
            continue
        if annotation is None:
            continue
        lines.extend(
            sub.lineno for sub in ast.walk(annotation)
            if isinstance(sub, ast.BinOp) and isinstance(sub.op, ast.BitOr)
        )
    return sorted(lines)


CLOSURE = _closure()
_IDS = [str(p.relative_to(REPO_ROOT)) for p in CLOSURE]


def test_closure_is_measured():
    """Sans cette borne, un config illisible rendrait la parametrisation vide."""
    assert len(CLOSURE) >= 5, f"cloture suspicieusement petite : {_IDS}"


def test_detector_flags_a_known_violation():
    """Controle positif de l'instrument : un detecteur casse passerait vert."""
    source = "def f(x: list[str] | None = None) -> None:\n    pass\n"
    tree = ast.parse(source)
    assert not _has_future_annotations(tree)
    assert _pep604_annotation_lines(tree) == [1]

    shielded = ast.parse("from __future__ import annotations\n" + source)
    assert _has_future_annotations(shielded)


def test_control_negative_plain_annotation_is_not_flagged():
    """Une annotation sans union ne doit pas etre signalee (anti-sur-accusation)."""
    tree = ast.parse("def f(x: list[str]) -> None:\n    pass\n")
    assert _pep604_annotation_lines(tree) == []


@pytest.mark.parametrize("path", CLOSURE, ids=_IDS)
def test_grammar_parses_under_py39(path: pathlib.Path):
    source = path.read_text(encoding="utf-8", errors="replace")
    try:
        ast.parse(source, feature_version=(3, 9))
    except SyntaxError as exc:
        pytest.fail(f"{path.name} : grammaire refusee par un analyseur 3.9 -- {exc}")


@pytest.mark.parametrize("path", CLOSURE, ids=_IDS)
def test_no_pep604_annotation_without_future_import(path: pathlib.Path):
    tree = ast.parse(path.read_text(encoding="utf-8", errors="replace"))
    if _has_future_annotations(tree):
        pytest.skip("from __future__ import annotations : annotations paresseuses")
    lines = _pep604_annotation_lines(tree)
    assert not lines, (
        f"{path.name} : annotation(s) PEP 604 ligne(s) {lines} sans "
        f"`from __future__ import annotations` — evaluee(s) a l'import, donc "
        f"TypeError sous Python 3.9 au premier commit d'une lane (#17264)"
    )
