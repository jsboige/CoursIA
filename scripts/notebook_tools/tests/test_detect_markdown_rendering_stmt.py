"""Tests for the CODE-STATEMENT-IN-MARKDOWN rule (#12064).

A stub MOVED from a code cell into a markdown cell renders as prose, is
invisible to count_exercises.py (it counts code cells), and escapes the H.3
pre-commit (a markdown cell has neither execution_count nor outputs to fail
on) -- the move does not satisfy H.3, it makes it inapplicable. Observed on
PR #11952 (Console.WriteLine exercise stubs, cells 15/17/19) and on main as
PT_11 cell 5 (a Papermill `parameters` anchor that never executes).

Locks in, for detect_markdown_rendering.py (rule code_stmt_in_markdown):
  - true positives: the cell-15 fixture of #11952 verbatim; the PT_11
    parameters-anchor form
  - true negatives: the two LEGITIMATE renderings of the same code
    (indented-4 block, fenced block) and plain prose -- the acceptance's
    false-negative game, without which a pattern set validates on its hits
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from detect_markdown_rendering import scan_cell  # noqa: E402


def _rules(source: str) -> list[str]:
    return [f["rule"] for f in scan_cell({"cell_type": "markdown", "source": source})]


# ---------------------------------------------------------------------------
# True positives -- the two observed forms (#12064 acceptance)
# ---------------------------------------------------------------------------

def test_pr11952_cell15_fixture_fires():
    """Controle positif prescrit par l'acceptance : la cellule 15 de #11952
    (stub d'exercice Console.WriteLine deplace en markdown sans fence)."""
    src = ("Exercice 5 -- affichez la valeur.\n"
           'Console.WriteLine("Exercice 5 a completer");\n')
    assert "code_stmt_in_markdown" in _rules(src)


def test_pt11_parameters_anchor_fires():
    """Instance (A) mesuree sur main : l'ancre Papermill en markdown."""
    src = ("# Set True for real training on GPU.\n"
           "LOAD_MODEL_AND_TRAIN = False\n"
           'print(f"LOAD_MODEL_AND_TRAIN = {LOAD_MODEL_AND_TRAIN}")\n')
    assert "code_stmt_in_markdown" in _rules(src)


def test_python_statement_forms_fire():
    for line in ("import numpy as np\n", "return 42\n", "def solve(x):\n"):
        assert "code_stmt_in_markdown" in _rules(line), line


def test_csharp_statement_forms_fire():
    for line in ("using System;\n", "var q = new Queue();\n", '#r "nuget: ...\n'):
        assert "code_stmt_in_markdown" in _rules(line), line


# ---------------------------------------------------------------------------
# True negatives -- the legitimate renderings (acceptance: jeu de
# faux-negatifs cote a cote, pas seulement les hits)
# ---------------------------------------------------------------------------

def test_indented_block_is_silent():
    """Non-regression prescrite : un bloc indente 4 espaces est du code
    markdown legitime (l'exclusion qui fait tomber le bruit corpus d'un
    facteur ~3)."""
    src = ("Exercice 5 -- affichez la valeur.\n\n"
           '    Console.WriteLine("Exercice 5 a completer");\n')
    assert "code_stmt_in_markdown" not in _rules(src)


def test_fenced_block_is_silent():
    src = ("Exercice 5 -- affichez la valeur.\n\n"
           '```csharp\nConsole.WriteLine("Exercice 5 a completer");\n```\n')
    assert "code_stmt_in_markdown" not in _rules(src)


def test_plain_prose_is_silent():
    src = "# Titre\n\nUn paragraphe qui parle de print() sans commencer par lui.\n"
    assert "code_stmt_in_markdown" not in _rules(src)


def test_prose_mentioning_print_midline_is_silent():
    """`print(` mid-ligne n'est pas un statement nu : l'ancre ^ le garantit."""
    src = "On utilisera print(...) pour afficher, puis return pour renvoyer.\n"
    assert "code_stmt_in_markdown" not in _rules(src)
