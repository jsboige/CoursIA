# -*- coding: utf-8 -*-
"""Tests du garde d'ancrage des cellules de densite.

Les deux premiers tests sont les **controles positifs** : un garde qui ne peut
pas echouer ne prouve rien quand il rend vert.
"""
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from check_density_anchor import MIN_OUTPUT_BYTES, audit, output_size  # noqa: E402


def md(text):
    return {"cell_type": "markdown", "source": [text]}


def code(text, out_text=None):
    cell = {"cell_type": "code", "source": [text], "outputs": [], "execution_count": 1}
    if out_text is not None:
        cell["outputs"] = [{"output_type": "stream", "text": [out_text]}]
    return cell


# --- controles positifs : le garde DOIT mordre ---------------------------------

def test_mord_sur_lecture_ancree_sur_stub_sans_output():
    cells = [code("# TODO : votre code ici\npass"),
             md("### Lecture du resultat\nOn observe une convergence nette.")]
    findings = audit(cells, base_cells=[])
    assert len(findings) == 1
    assert findings[0]["anchor"] == 0
    assert findings[0]["stub"] is True
    assert "stub" in findings[0]["reason"]


def test_mord_sur_stub_a_output_residuel():
    cells = [code("# TODO : completer\nprint('a faire')", out_text="a faire\n"),
             md("### Interpretation\nLe score atteint 0.94.")]
    findings = audit(cells, base_cells=[])
    assert len(findings) == 1
    assert 0 < findings[0]["output_bytes"] < MIN_OUTPUT_BYTES


def test_mord_sur_lecture_sans_aucune_cellule_de_code_amont():
    findings = audit([md("### Lecture du resultat\nvoir plus haut.")], base_cells=[])
    assert len(findings) == 1
    assert findings[0]["anchor"] is None


# --- verts legitimes -----------------------------------------------------------

def test_vert_quand_l_ancre_porte_un_vrai_output():
    cells = [code("print(score)", out_text="x" * (MIN_OUTPUT_BYTES + 50)),
             md("### Lecture du resultat\nLe score atteint 0.94.")]
    assert audit(cells, base_cells=[]) == []


def test_vert_sur_un_stub_sans_cellule_de_lecture():
    """Un stub non commente est normal : c'est un exercice."""
    cells = [code("# TODO : votre code ici\npass"),
             md("## Exercice 2\nCompleter la fonction ci-dessus.")]
    assert audit(cells, base_cells=[]) == []


def test_ignore_les_cellules_deja_presentes_dans_la_base():
    """Le verdict est borne au diff : une lecture preexistante n'est pas jugee."""
    lecture = "### Lecture du resultat\nconvergence nette."
    cells = [code("# TODO\npass"), md(lecture)]
    assert audit(cells, base_cells=[md(lecture)]) == []


def test_ancre_saute_les_markdown_intercales():
    cells = [code("print(x)", out_text="y" * 400),
             md("Transition sans lecture."),
             md("### Interpretation\nLe resultat est stable.")]
    assert audit(cells, base_cells=[]) == []


def test_output_size_compte_les_donnees_riches():
    cell = {"cell_type": "code", "source": [""],
            "outputs": [{"output_type": "display_data",
                         "data": {"image/png": "iVBOR" + "A" * 300}}]}
    assert output_size(cell) > MIN_OUTPUT_BYTES


def test_notebook_sans_cellule_de_lecture_est_vert():
    cells = [code("import numpy", out_text="ok"), md("## Titre")]
    assert audit(cells, base_cells=[]) == []


def test_serialisation_json_du_verdict():
    cells = [code("# TODO\npass"), md("### Lecture du resultat\nfoo.")]
    json.dumps(audit(cells, base_cells=[]))
