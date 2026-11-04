"""Detecteur de sorties de flux sans fin de ligne (#22181).

Trois cas distincts sont couverts :

1. le **defaut reel** : un rapport multiligne dont les fins de ligne ont ete
   perdues (l'executeur faisait ``text.split("\\n")``) ;
2. le **faux positif** que la mesure initiale de #22181 comptait : une barre
   de progression ``tqdm`` / ``yfinance``, dont les cadres se terminent par
   ``\\r`` -- c'est du texte legitime, pas un rapport aplati ;
3. le **controle negatif** : un flux correctement newline-terminé n'est
   jamais compté, et une sortie qui n'est pas un ``stream`` n'est jamais
   comptée.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[3]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.notebook_tools.scan_stream_newline_loss import (  # noqa: E402
    count_defects_in_notebook,
    is_defective_stream,
    scan_path,
)


def _stream(text):
    return {"output_type": "stream", "name": "stdout", "text": text}


def test_flattened_report_is_a_defect():
    """Le cas de #21836 : les fins de ligne ont disparu."""
    out = _stream(["ligne 1", "ligne 2", "ligne 3"])
    assert is_defective_stream(out) is True


def test_progress_bar_is_not_a_defect():
    """Faux positif de la mesure initiale : une barre de progression \\r.

    Les cadres d'une barre se terminent par ``\\r`` (retour chariot) : le
    terminal les redessine sur place. Ce n'est pas un rapport aplati.
    """
    out = _stream(["\r", "[###   ] 27% completed\r", "[###   ] 27% completed"])
    assert is_defective_stream(out) is False


def test_newline_terminated_stream_is_not_a_defect():
    out = _stream(["ligne 1\n", "ligne 2\n", "ligne 3\n"])
    assert is_defective_stream(out) is False


def test_two_elements_are_never_a_defect():
    """Le seuil de la mesure : il faut plus de deux elements."""
    assert is_defective_stream(_stream(["ligne 1", "ligne 2"])) is False
    assert is_defective_stream(_stream("texte simple")) is False


def test_non_stream_output_is_never_a_defect():
    out = {"output_type": "execute_result", "data": {"text/plain": "42"},
           "execution_count": 1}
    assert is_defective_stream(out) is False


def test_mixed_output_endings_count_only_the_defective_ones():
    out = _stream(["a", "b", "c"])
    assert is_defective_stream(out) is True
    # une seule sortie avec un \n quelque part suffit a la blanchir
    out = _stream(["a\n", "b", "c"])
    assert is_defective_stream(out) is False


def _write_nb(path: Path, outputs):
    nb = {"cells": [{"cell_type": "code", "execution_count": 1,
                      "source": ["print('x')"], "outputs": outputs}],
          "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
    path.write_text(json.dumps(nb), encoding="utf-8")


def test_scan_path_reports_only_defective_notebooks(tmp_path):
    good = tmp_path / "good.ipynb"
    bad = tmp_path / "bad.ipynb"
    _write_nb(good, [_stream(["ligne 1\n", "ligne 2\n", "ligne 3\n"])])
    _write_nb(bad, [_stream(["ligne 1", "ligne 2", "ligne 3"]),
                     _stream(["\r", "[#] 27%\r", "[#] 27%"])])

    findings = scan_path(tmp_path)
    assert list(findings) == ["bad.ipynb"]
    assert findings["bad.ipynb"] == 1


def test_scan_path_on_a_single_file(tmp_path):
    target = tmp_path / "one.ipynb"
    _write_nb(target, [_stream(["a", "b", "c"])])
    assert scan_path(target) == {"one.ipynb": 1}


def test_count_defects_ignores_markdown_cells():
    nb = {"cells": [
        {"cell_type": "markdown", "source": ["# titre"]},
        {"cell_type": "code", "execution_count": 1, "source": ["x"],
         "outputs": [_stream(["a", "b", "c"])]},
    ]}
    assert count_defects_in_notebook(nb) == 1
