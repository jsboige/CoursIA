#!/usr/bin/env python3
"""Tests de `scripts/notebook_tools/check_series_denominator.py` (#23678).

Le critere d'acceptation 3 de l'issue exige un **controle negatif rouge** : un
carnet portant un denominateur de serie doit etre detecte sur un cas construit,
pas seulement « l'organe passe au vert sur `main` ». Un organe qui ne rougit
jamais n'est pas un organe, c'est une decoration -- et c'est exactement le
defaut que #23678 corrige (un champ accuse de compter la serie, que rien ne
verifiait).

Cas couverts :

1. les **deux formes** d'en-tete rencontrees dans la serie RL sont detectees
   (`**Notebook** : 6f/13` et `**Notebook : 10/26`) ;
2. un carnet **sans** denominateur rend `[]` (pas de faux positif sur
   `**Notebook : 6f**`, qui est la forme canonique visee) ;
3. le **numero seul** ne suffit pas a declencher : `**Notebook : 7**` est vert ;
4. une **fraction d'un autre champ** n'est pas confondue (`**Duree** : 45/50`) ;
5. `main()` rend **1** sur un dossier rouge et **0** sur un dossier vert ;
6. un chemin **inexistant** rend **2** (un perimetre muet ne passe jamais pour
   un vert) ;
7. les cellules de **code** sont ignorees, meme si elles contiennent la chaine.

Le module est charge **par chemin** : `scripts/notebook_tools/` n'est pas un
paquet importable depuis la racine du depot.

Usage : python scripts/tests/test_check_series_denominator.py
"""
import importlib.util
import json
import sys
import tempfile
from pathlib import Path

TOOL = Path(__file__).resolve().parents[1] / "notebook_tools" / "check_series_denominator.py"


def load_tool():
    spec = importlib.util.spec_from_file_location("check_series_denominator", TOOL)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def make_notebook(path, cells):
    """Ecrit un carnet minimal : `cells` est une liste de (cell_type, texte)."""
    notebook = {
        "cells": [
            {
                "cell_type": kind,
                "metadata": {},
                "source": [text],
                **({"outputs": [], "execution_count": None} if kind == "code" else {}),
            }
            for kind, text in cells
        ],
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    Path(path).write_text(json.dumps(notebook), encoding="utf-8")


def test_detects_both_header_forms():
    tool = load_tool()
    with tempfile.TemporaryDirectory() as tmp:
        bold_closed = Path(tmp) / "RL-06f.Deep.ipynb"
        make_notebook(bold_closed, [("markdown", "**Notebook** : 6f/13 | **Duree** : 45 min")])
        findings, error = tool.scan_notebook(bold_closed)
        assert error is None, error
        assert findings == [(0, "**Notebook** : 6f/13")], findings

        bold_all = Path(tmp) / "RL-10.Multi.ipynb"
        make_notebook(bold_all, [("markdown", "**Notebook : 10/26** | **Duree** : 45-50 min")])
        findings, error = tool.scan_notebook(bold_all)
        assert error is None, error
        assert findings == [(0, "**Notebook : 10/26**")], findings


def test_canonical_form_is_clean():
    """La forme visee par le fix (#23678) ne doit PAS etre signalee."""
    tool = load_tool()
    with tempfile.TemporaryDirectory() as tmp:
        clean = Path(tmp) / "RL-07.Deep.ipynb"
        make_notebook(clean, [("markdown", "**Notebook : 7** | **Duree** : 45 min | **Niveau** : avance")])
        findings, error = tool.scan_notebook(clean)
        assert error is None, error
        assert findings == [], findings


def test_bare_number_without_slash_is_clean():
    tool = load_tool()
    with tempfile.TemporaryDirectory() as tmp:
        clean = Path(tmp) / "RL-12.GridWorld.ipynb"
        make_notebook(clean, [("markdown", "**Notebook** : 12")])
        findings, _ = tool.scan_notebook(clean)
        assert findings == [], findings


def test_foreign_fraction_is_clean():
    """Une fraction d'un autre champ (`**Duree** : 45/50`) n'est pas un denominateur."""
    tool = load_tool()
    with tempfile.TemporaryDirectory() as tmp:
        clean = Path(tmp) / "RL-13.DQN.ipynb"
        make_notebook(clean, [("markdown", "**Duree** : 45/50 min\n\n**Notebook** : 13")])
        findings, _ = tool.scan_notebook(clean)
        assert findings == [], findings


def test_code_cells_are_ignored():
    tool = load_tool()
    with tempfile.TemporaryDirectory() as tmp:
        notebook = Path(tmp) / "RL-14.PPO.ipynb"
        make_notebook(notebook, [("code", "# **Notebook** : 14/26 dans un commentaire")])
        findings, _ = tool.scan_notebook(notebook)
        assert findings == [], findings


def test_main_returns_one_on_red_directory():
    """CONTROLE NEGATIF : le dossier rouge fait rougir l'organe (sortie 1)."""
    tool = load_tool()
    with tempfile.TemporaryDirectory() as tmp:
        make_notebook(Path(tmp) / "RL-01.Bandits.ipynb", [("markdown", "**Notebook** : 1/26")])
        make_notebook(Path(tmp) / "RL-02.MDP.ipynb", [("markdown", "**Notebook** : 2")])
        assert tool.main([tmp]) == 1, "un denominateur present doit rendre 1"


def test_main_returns_zero_on_green_directory():
    tool = load_tool()
    with tempfile.TemporaryDirectory() as tmp:
        make_notebook(Path(tmp) / "RL-01.Bandits.ipynb", [("markdown", "**Notebook** : 1")])
        make_notebook(Path(tmp) / "RL-02.MDP.ipynb", [("markdown", "**Notebook** : 2")])
        assert tool.main([tmp]) == 0


def test_main_returns_two_without_path():
    """Un perimetre vide n'est pas un vert : sans chemin, l'organe refuse."""
    tool = load_tool()
    assert tool.main([]) == 2
    assert tool.main(["chemin/qui/n/existe/pas.ipynb"]) == 2


def test_collect_reports_cell_index_and_path():
    tool = load_tool()
    with tempfile.TemporaryDirectory() as tmp:
        notebook = Path(tmp) / "RL-03.Tabular.ipynb"
        make_notebook(
            notebook,
            [
                ("markdown", "# Titre"),
                ("code", "print(1)"),
                ("markdown", "**Notebook : 3/13**"),
            ],
        )
        report = tool.collect([tmp])
        assert len(report) == 1, report
        assert report[0]["cell"] == 2, report
        assert report[0]["match"] == "**Notebook : 3/13**", report
        assert report[0]["error"] is None


def main():
    tests = [value for name, value in sorted(globals().items()) if name.startswith("test_")]
    failures = 0
    for test in tests:
        try:
            test()
        except AssertionError as exc:
            failures += 1
            print("FAIL %s: %s" % (test.__name__, exc))
        else:
            print("ok   %s" % test.__name__)
    print("%d/%d tests passes" % (len(tests) - failures, len(tests)))
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
