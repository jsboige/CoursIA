"""Regression : les scanners D1/D5 doivent lire les sorties text/html.

Bug (EPIC #9768, moitie text/html du finding instrument du 2026-08-19,
#9790) : ``extract_output_numbers`` (scan_d1_d3_d4_d5) et
``_extract_output_numbers`` (scan_d5_prose_outputs_alignment) ne
lisaient que ``text`` et ``data['text/plain']``. Or les familles .NET
Interactive (Infer/DecInfer, ML/, Search C#) deposent leurs valeurs
mesurees dans ``data['text/html']`` -- tables rendues, valeurs formatees
en culture FR. La comparaison prose<->outputs etait vide par
construction pour ces familles (faux D1+ "0 nombre dans les outputs").

La moitie stream-list du meme finding a ete livree en #12633.
"""

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "notebook_tools"))

from scan_d1_d3_d4_d5 import extract_output_numbers
from scan_d5_prose_outputs_alignment import _extract_output_numbers


def _nb_html(html_repr):
    """Notebook minimal : 1 cellule code avec 1 sortie execute_result text/html."""
    return json.dumps({
        "cells": [
            {"cell_type": "code", "outputs": [
                {"output_type": "execute_result",
                 "data": {"text/html": html_repr}},
            ]},
            {"cell_type": "markdown",
             "source": "moyenne 15,33 et sigma 1,32"},
        ],
    })


# ---------------------------------------------------------------- v1 (D1) -- #12633 pattern


def test_html_liste_est_lue():
    _, nums = extract_output_numbers(
        _nb_html(["<td>Phi = 0.69</td>", "<td>Gain = 12.5</td>"]))
    assert 0.69 in nums
    assert 12.5 in nums


def test_html_str_est_lu():
    _, nums = extract_output_numbers(_nb_html("<td>42</td>"))
    assert 42.0 in nums


def test_virgule_decimale_fr_pas_coupee():
    """Gaussian(15,33, 1,32) = deux nombres FR, pas quatre entiers."""
    _, nums = extract_output_numbers(
        _nb_html("<div>Gaussian(15,33, 1,32)</div>"))
    assert 15.33 in nums
    assert 1.32 in nums
    assert 15.0 not in nums
    assert 33.0 not in nums


def test_separateur_liste_avec_espace_pas_fusionne():
    """10, 11, 12 : virgule + espace = separateur, pas decimale."""
    _, nums = extract_output_numbers(_nb_html("<div>10, 11, 12</div>"))
    assert sorted(n for n in nums if n in (10.0, 11.0, 12.0)) == [10.0, 11.0, 12.0]


def test_balises_retirees():
    _, nums = extract_output_numbers(
        _nb_html("<table><tr><th>Sharpe</th><td>0.787</td></tr></table>"))
    assert 0.787 in nums


def test_text_plain_reste_lu():
    nb = json.dumps({"cells": [
        {"cell_type": "code", "outputs": [
            {"output_type": "execute_result",
             "data": {"text/plain": ["42"], "text/html": "<td>0.5</td>"}},
        ]},
    ]})
    _, nums = extract_output_numbers(nb)
    assert 42.0 in nums and 0.5 in nums


def test_prose_en_et_html_fr_se_repondent():
    """Pairing D1 cross-culture : prose EN (15.33) <-> output html FR (15,33).

    Le cote PROSE du v1 reste EN-only (scope de ce grain : le canal OUTPUTS,
    cf #9790). Les valeurs identiques s'apparient malgre l'ecart de format.
    """
    from scan_d1_d3_d4_d5 import extract_prose_numbers
    nb = _nb_html("<div>Gaussian(15,33, 1,32)</div>")
    nb = nb.replace("moyenne 15,33 et sigma 1,32", "moyenne 15.33 et sigma 1.32")
    prose = [v for _, v in extract_prose_numbers(nb)]
    _, outputs = extract_output_numbers(nb)
    assert prose
    for v in prose:
        assert any(abs(v - ov) <= 0.01 for ov in outputs), v


# ---------------------------------------------------------------- v3 (D5)


def test_v3_html_liste_fr():
    o = {"output_type": "execute_result",
         "data": {"text/html": ["<td>Gaussian(15,33, 1,32)</td>"]}}
    nums = _extract_output_numbers(o)
    assert 15.33 in nums and 1.32 in nums


def test_v3_html_str_table():
    o = {"output_type": "execute_result",
         "data": {"text/html": "<table><td>0.787</td></table>"}}
    assert 0.787 in _extract_output_numbers(o)


def test_v3_sans_data_inchange():
    assert _extract_output_numbers({"output_type": "stream", "text": "x 7"}) == [7.0]
