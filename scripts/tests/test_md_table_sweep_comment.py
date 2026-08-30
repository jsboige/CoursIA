"""Tests for scripts/notebook_tools/md_table_sweep_comment.py (#13660).

L'organe est la DISTRIBUTION du verdict nocturne du garde markdown-table : le
scanner `scan_md_table_syntax.py` (non modifie ici) est juste, mais son verdict
tombait dans un log planifie que personne n'ouvre -- un organe muet. Ce module
construit le commentaire marker-garde (`MD-TABLE-SWEEP`) et l'upserte sur une
issue de rendez-vous OUVERTE (patron GRAIN-ORPHANS-SWEEP, #13086).

Ce qui doit rester stable pour que l'upsert fonctionne (un seul commentaire
remplace, jamais un flot) :
  - la paire de marqueurs ``MD-TABLE-SWEEP:START`` / ``:END`` borne le bloc --
    l'upsert le retrouve par START et remplace TOUT le bloc ;
  - le corps porte le millesime (date + fenetre) pour ne pas se lire comme
    courant ;
  - le corps ecrit ce qu'il ne couvre pas (syntaxe source, pas rendu) ;
  - le cas vide s'ecrit AUSSI (un balayage muet est indiscernable d'un balayage
    mort), MAIS sans lister les notebooks sains -- un rapport qui listerait tout
    ne mesure rien.
"""

import importlib.util
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
MOD_PATH = HERE.parent / "notebook_tools" / "md_table_sweep_comment.py"

spec = importlib.util.spec_from_file_location("md_table_sweep_comment", MOD_PATH)
mod = importlib.util.module_from_spec(spec)
sys.modules["md_table_sweep_comment"] = mod
spec.loader.exec_module(mod)

STAMP = "2026-08-30T11:00Z"
WINDOW = "cc4d59e1bf..cafe1234 (24 h de main)"


def test_positive_lists_defects_with_locations():
    files = [{
        "path": "MyIA.AI.Notebooks/Sudoku/Sudoku-05-PSO-Csharp.ipynb",
        "findings": [
            {"pathology": "CODE_SPAN_PIPE", "cell_index": 40, "line": 17,
             "detail": "x", "snippet": "| `a|b` | c |"},
            {"pathology": "NO_BLANK_BEFORE", "line": 8,
             "detail": "x", "snippet": "glued paragraph"},
        ],
    }]
    body = mod.build_comment(files, 2, WINDOW, STAMP)
    assert mod.MARKER_START in body and mod.MARKER_END in body
    assert "2 défaut(s)" in body
    assert "Sudoku-05-PSO-Csharp.ipynb" in body
    assert "cellule 40" in body
    assert "ligne 8" in body
    assert "CODE_SPAN_PIPE" in body
    assert "glued paragraph" in body
    assert STAMP in body and WINDOW in body


def test_negative_control_does_not_list_clean_notebook():
    files = [
        {"path": "clean_a.ipynb", "findings": []},
        {"path": "clean_b.ipynb", "findings": []},
    ]
    body = mod.build_comment(files, 0, WINDOW, STAMP)
    assert mod.MARKER_START in body and mod.MARKER_END in body
    assert "0" in body and "défaut" in body
    # Un notebook sans defaut n'apparait PAS : un rapport qui listerait tout ne
    # mesure rien.
    assert "clean_a.ipynb" not in body
    assert "clean_b.ipynb" not in body


def test_marker_guards_brace_the_whole_block():
    files = [{"path": "n.ipynb", "findings": [
        {"pathology": "COL_MISMATCH", "line": 3, "detail": "x", "snippet": "| a |"},
    ]}]
    body = mod.build_comment(files, 1, WINDOW, STAMP)
    lines = [l for l in body.split("\n")]
    assert lines[0] == mod.MARKER_START
    assert lines[-1] == mod.MARKER_END


def test_coverage_note_states_what_it_does_not_cover():
    files = [{"path": "n.ipynb", "findings": []}]
    body = mod.build_comment(files, 0, WINDOW, STAMP)
    # La portee (syntaxe source, pas rendu) doit etre ecrite explicitement.
    assert "syntaxe SOURCE" in body
    assert "pas le rendu" in body
    assert "choix d'auteur" in body


def test_backtick_in_snippet_gets_safe_fence():
    files = [{"path": "n.ipynb", "findings": [
        {"pathology": "CODE_SPAN_PIPE", "cell_index": 40, "line": 17,
         "detail": "x", "snippet": "| `a|b` | c |"},
    ]}]
    body = mod.build_comment(files, 1, WINDOW, STAMP)
    # Un CODE_SPAN_PIPE a un backtick litteral : le delimiter doit etre plus long
    # que la course interne, sinon le rendu du commentaire casse.
    assert "``| `a|b` | c |``" in body
