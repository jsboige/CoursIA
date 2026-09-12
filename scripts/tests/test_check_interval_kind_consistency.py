"""Tests du garde d'accord intervalle declare <-> intervalle affiche (#15592).

L'instance fondatrice est le defaut de #15156 : `hdi_prob=0.89` remplace par
`ci_prob=0.89` **sans `ci_kind`**, sans re-execution -- la source redescend
donc au defaut de la bibliotheque (`eti`) tandis que la sortie committée garde
des colonnes `hdi89_*`. Le test `test_instance_fondatrice_est_attrapee`
reconstruit cet etat, il ne le decrit pas.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "notebook_tools"))

from check_interval_kind_consistency import (  # noqa: E402
    examine,
    declared_kinds,
    main,
    output_kinds,
)


def _out(*cols: str) -> dict:
    """Sortie de cellule portant des noms de colonnes, comme un `az.summary`."""
    hdr = " ".join(cols)
    return {"output_type": "execute_result",
            "data": {"text/plain": [hdr + "\n0 1.0 2.0"]}}


def _nb(tmp: Path, cells: list[dict], name: str = "Nb.ipynb") -> Path:
    p = tmp / name
    p.write_text(json.dumps({"cells": cells, "nbformat": 4, "nbformat_minor": 5}),
                 encoding="utf-8")
    return p


def _code(src: str, *cols: str) -> dict:
    cell = {"cell_type": "code", "source": src.splitlines(keepends=True),
            "metadata": {}, "execution_count": 1, "outputs": []}
    if cols:
        cell["outputs"] = [_out(*cols)]
    return cell


# --- lecture des deux cotes -------------------------------------------------

def test_declared_kinds_lit_ci_kind_hdi():
    assert declared_kinds('az.summary(t, ci_prob=0.89, ci_kind="hdi")') == {"hdi"}


def test_declared_kinds_lit_le_legacy_hdi_prob():
    assert declared_kinds("az.summary(t, hdi_prob=0.89)") == {"hdi"}


def test_declared_kinds_ne_devine_rien_sans_declaration():
    """`ci_prob=` seul ne demande RIEN d'explicite : c'est le defaut de la
    bibliotheque qui tranche, et il est encode ailleurs."""
    assert declared_kinds("az.summary(t, ci_prob=0.89)") == set()
    assert declared_kinds("az.summary(t, var_names=['theta'])") == set()


def test_output_kinds_lit_les_colonnes():
    assert output_kinds(_code("x", "hdi89_lb", "hdi89_ub")) == {"hdi"}
    assert output_kinds(_code("x", "eti89_lb", "eti94_ub")) == {"eti"}
    assert output_kinds(_code("x", "mean", "sd")) == set()


# --- l'invariant -----------------------------------------------------------

def test_instance_fondatrice_est_attrapee(tmp_path: Path):
    """Reconstruit l'etat d'APRES #15156 et AVANT correctif : source sans
    `ci_kind` (donc `eti` par defaut), sortie committée restee en `hdi`."""
    nb = _nb(tmp_path, [
        _code('az.summary(trace_rho, var_names=["rho"], ci_prob=0.89)',
              "hdi89_lb", "hdi89_ub")])
    issues, counts = examine(nb)
    assert len(issues) == 1
    assert issues[0]["expected"] == "eti"
    assert issues[0]["shown"] == ["hdi"]
    assert issues[0]["basis"] == "library-default"
    assert counts["default"] == 1


def test_desaccord_inverse_source_hdi_sortie_eti(tmp_path: Path):
    nb = _nb(tmp_path, [
        _code('az.summary(t, ci_kind="hdi")', "eti89_lb", "eti89_ub")])
    issues, _ = examine(nb)
    assert len(issues) == 1
    assert issues[0]["expected"] == "hdi"
    assert issues[0]["basis"] == "explicit"


def test_accord_explicite_passe(tmp_path: Path):
    nb = _nb(tmp_path, [
        _code('az.summary(t, ci_prob=0.89, ci_kind="hdi")',
              "hdi89_lb", "hdi89_ub")])
    assert examine(nb) == ([], {"cells": 1, "explicit": 1, "default": 0,
                                "ambiguous": 0})


def test_accord_par_defaut_passe(tmp_path: Path):
    """Le cas le plus frequent du depot (16 des 18 cellules) : aucun argument
    d'intervalle, sortie `eti` -- le defaut de la bibliotheque, coherent."""
    nb = _nb(tmp_path, [_code("az.summary(t)", "eti89_lb", "eti89_ub")])
    issues, counts = examine(nb)
    assert issues == [] and counts["default"] == 1


def test_defaut_eti_avec_sortie_hdi_rougit(tmp_path: Path):
    nb = _nb(tmp_path, [_code("az.summary(t)", "hdi89_lb", "hdi89_ub")])
    issues, _ = examine(nb)
    assert len(issues) == 1 and issues[0]["expected"] == "eti"


def test_cellule_mixte_est_ecartee_pas_jugee(tmp_path: Path):
    """Une cellule qui demande explicitement les DEUX types est ambigue par
    construction : elle est denombrée, jamais condamnee."""
    nb = _nb(tmp_path, [
        _code('az.summary(t, ci_kind="hdi")\naz.plot_dist(t, ci_kind="eti")',
              "eti89_lb")])
    issues, counts = examine(nb)
    assert issues == []
    assert counts["ambiguous"] == 1 and counts["cells"] == 1


def test_cellule_sans_colonne_d_intervalle_est_ignoree(tmp_path: Path):
    nb = _nb(tmp_path, [_code('az.summary(t, ci_kind="hdi")', "mean", "sd")])
    issues, counts = examine(nb)
    assert issues == [] and counts["cells"] == 0


def test_notebook_illisible_ne_fait_pas_tomber_le_garde(tmp_path: Path):
    bad = tmp_path / "bad.ipynb"
    bad.write_text("{ pas du json", encoding="utf-8")
    issues, counts = examine(bad)
    assert issues == [] and counts.get("unreadable") == 1


# --- CLI -------------------------------------------------------------------

def test_main_arbre_sans_colonne_rend_0(tmp_path: Path, capsys):
    _nb(tmp_path, [_code("print(1)", "mean")])
    assert main(["--root", str(tmp_path)]) == 0
    assert "rien a verifier" in capsys.readouterr().out


def test_main_rougit_et_nomme_la_cellule(tmp_path: Path, capsys):
    _nb(tmp_path, [_code('az.summary(t, ci_prob=0.89)', "hdi89_lb")])
    assert main(["--root", str(tmp_path)]) == 1
    out = capsys.readouterr().out
    assert "cellule 0" in out and "ETI" in out and "HDI" in out


def test_json_shape(tmp_path: Path, capsys):
    _nb(tmp_path, [_code('az.summary(t, ci_prob=0.89)', "hdi89_lb")])
    assert main(["--root", str(tmp_path), "--json"]) == 1
    payload = json.loads(capsys.readouterr().out)
    assert payload["totals"]["cells"] == 1
    assert payload["issues"][0]["expected"] == "eti"


# --- verrou de baseline ----------------------------------------------------
#
# La portee du garde est l'arbre ENTIER et il est bloquant : ce n'est legitime
# que si la baseline est verte. Ces deux tests verrouillent la baseline sur les
# deux seuls notebooks du depot qui declarent explicitement un HDI. Si l'un
# d'eux rederive, le garde rougit -- et ce test dit lequel.

REAL = Path(__file__).resolve().parents[2] / "MyIA.AI.Notebooks" / "Probas"


@pytest.mark.parametrize("rel", [
    "DecisionTheory/PyMC/DecPyMC-2-Utility-Money.ipynb",
    "DecisionTheory/PyMC/DecPyMC-8-Actuarial-Credibility.ipynb",
])
def test_baseline_hdi_reelle_est_coherente(rel: str):
    nb = REAL / rel
    if not nb.exists():
        pytest.skip("notebook absent de cet arbre")
    issues, counts = examine(nb)
    assert issues == [], issues
    assert counts["explicit"] >= 1, (
        "le notebook ne declare plus de HDI explicite -- le verrou de "
        "baseline ne teste plus rien")
