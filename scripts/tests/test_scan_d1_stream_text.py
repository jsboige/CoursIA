"""Regression : extract_output_numbers doit lire les sorties stream en LISTE.

Bug (EPIC #9768, tranche GameTheory 2026-08-23) : nbformat stocke le texte
des sorties ``stream`` en LISTE de str, mais extract_output_numbers ne lisait
que le cas ``str``. Tout notebook dont les valeurs numeriques vivent dans
stdout etait donc vu comme "0 nombre dans les outputs" -> faux D1+ "notebook
non execute ?" (37/37 verdicts D1+ de GameTheory etaient des faux positifs).
"""

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "notebook_tools"))

from scan_d1_d3_d4_d5 import extract_output_numbers, extract_prose_numbers


def _nb_stream(text_repr):
    """Notebook minimal : 1 cellule code avec 1 sortie stream, 1 cellule md."""
    return json.dumps({
        "cells": [
            {"cell_type": "code", "outputs": [
                {"output_type": "stream", "name": "stdout", "text": text_repr},
            ]},
            {"cell_type": "markdown", "source": "Phi = 0.69 et Gain = 12.5"},
        ],
    })


def test_stream_text_liste_est_lue():
    _, nums = extract_output_numbers(_nb_stream(["Phi = 0.69\n", "Gain = 12.5\n"]))
    assert 0.69 in nums
    assert 12.5 in nums


def test_stream_text_str_reste_lu():
    _, nums = extract_output_numbers(_nb_stream("Phi = 0.69\n"))
    assert 0.69 in nums


def test_data_text_plain_liste_reste_lu():
    nb = json.dumps({"cells": [
        {"cell_type": "code", "outputs": [
            {"output_type": "execute_result", "data": {"text/plain": ["42"]}},
        ]},
    ]})
    _, nums = extract_output_numbers(nb)
    assert 42.0 in nums


def test_prose_et_stream_liste_se_repondent():
    """Le pairing D1 : chaque nombre de prose a un candidat dans les outputs."""
    nb = _nb_stream(["Phi = 0.69\n", "Gain = 12.5\n"])
    prose = [v for _, v in extract_prose_numbers(nb)]
    _, outputs = extract_output_numbers(nb)
    for v in prose:
        assert any(abs(v - ov) / abs(ov) <= 0.05 for ov in outputs if abs(ov) > 1e-6), v
