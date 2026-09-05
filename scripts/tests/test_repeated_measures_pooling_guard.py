"""Tests du garde pooling de mesures repetees (#14827).

Les cas sont les formes REELLES de la fondation #14816 (cellules 8 et 12
de Sudoku-18b pre-fix) et de leur correction (commit 9efda30f9d), plus
les formes legitimes voisines. Un detecteur se valide par ses faux
negatifs : chaque forme qui DOIT etre attrapee a son test, chaque forme
legitime qui DOIT passer a le sien.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "notebook_tools"))

from check_repeated_measures_pooling import (  # noqa: E402
    CORRECTED_CELL_12_CORE,
    CORRECTED_CELL_8_CORE,
    COMPREHENSION_POOLED,
    FOUNDING_CELL_12_CORE,
    FOUNDING_CELL_8_CORE,
    LEGIT_ARRAY_WRAPPER_ON_AGGREGATED,
    LEGIT_BOOTSTRAP_SINGLE_LOOP,
    TTEST_INDEPENDANT_POOLED,
    analyze_cell,
    is_demo_cell,
    scan_notebook,
    self_test,
    sweep,
)


# ---------------------------------------------------------------------------
# Faux negatifs -- les formes qui DOIVENT etre attrapees
# ---------------------------------------------------------------------------

def test_fondation_cellule_8_pooling_direct():
    defects, _ = analyze_cell(FOUNDING_CELL_8_CORE)
    assert len(defects) == 1
    assert defects[0]["test"] == "mannwhitneyu"
    assert set(defects[0]["pooled"]) == {"naive_times", "mrv_times"}


def test_fondation_cellule_12_table_de_paires_et_etat_cross_cell():
    # l'etat pooled de la cellule 8 doit traverser la frontiere de cellule
    _, pooled = analyze_cell(FOUNDING_CELL_8_CORE)
    defects, _ = analyze_cell(FOUNDING_CELL_12_CORE, pooled, cell_index=1)
    assert len(defects) == 1
    assert defects[0]["test"] == "mannwhitneyu"
    # le test ne nomme jamais les accumulateurs : a/b passent par la table
    assert set(defects[0]["pooled"]) == {
        "naive_times", "mrv_times", "reverse_times"}
    assert defects[0]["append_cell"] in (0, 1)


def test_fondation_cellule_12_sans_etat_prealable_rate_les_noms_importes():
    # sans la cellule 8 en amont, seuls les noms pools LOCALEMENT
    # (reverse_times) sont attribuables -- la detection reste honnete
    # sur ce qu'elle peut prouver dans cette cellule
    defects, _ = analyze_cell(FOUNDING_CELL_12_CORE)
    assert len(defects) == 1
    assert set(defects[0]["pooled"]) == {"reverse_times"}


def test_variant_ttest_ind():
    defects, _ = analyze_cell(TTEST_INDEPENDANT_POOLED)
    assert len(defects) == 1
    assert defects[0]["test"] == "ttest_ind"
    assert set(defects[0]["pooled"]) == {"scores_a", "scores_b"}


def test_pooling_en_comprehension_double_generateur():
    defects, _ = analyze_cell(COMPREHENSION_POOLED)
    assert len(defects) == 1
    assert set(defects[0]["pooled"]) == {"flat", "other"}


# ---------------------------------------------------------------------------
# Faux positifs -- les formes legitimes qui DOIVENT passer
# ---------------------------------------------------------------------------

def test_cellule_corrigee_8_mediane_par_puis_wilcoxon():
    defects, pooled = analyze_cell(CORRECTED_CELL_8_CORE)
    assert defects == []
    # les medianes agregees (une par unite) ne sont pas des accumulations
    # de repetitions ; seules les listes brutes jamais testees le sont
    assert "naive_times" not in pooled
    assert "mrv_times" not in pooled
    assert {"ts_naive", "ts_mrv"} <= set(pooled)


def test_cellule_corrigee_12_wilcoxon_apparie_via_table():
    _, pooled = analyze_cell(CORRECTED_CELL_8_CORE)
    defects, _ = analyze_cell(CORRECTED_CELL_12_CORE, pooled, cell_index=1)
    assert defects == []


def test_bootstrap_boucle_simple():
    defects, _ = analyze_cell(LEGIT_BOOTSTRAP_SINGLE_LOOP)
    assert defects == []


def test_arrays_agregees_avec_wrapper():
    defects, _ = analyze_cell(LEGIT_ARRAY_WRAPPER_ON_AGGREGATED)
    assert defects == []


def test_demo_marquee_est_sautee():
    src = FOUNDING_CELL_8_CORE + "\n# pooled-demo"
    assert is_demo_cell(src)
    defects, pooled_after = analyze_cell(src, {"naive_times": 0})
    assert defects == []
    # une cellule demo n'accumule pas non plus dans l'etat notebook
    assert pooled_after == {"naive_times": 0}


def test_cellule_non_parsable_ne_plante_pas():
    defects, pooled = analyze_cell("def f(:\n  pass", {"x": 0}, 3)
    assert defects == []
    assert pooled == {"x": 0}


# ---------------------------------------------------------------------------
# Notebook reel (tmp) -- le chemin scan_notebook de bout en bout
# ---------------------------------------------------------------------------

def _write_nb(tmp_path: Path, sources: list[str]) -> Path:
    nb = {
        "cells": [{"cell_type": "code", "metadata": {}, "outputs": [],
                   "execution_count": 1, "source": src.splitlines(keepends=True)}
                  for src in sources],
        "metadata": {}, "nbformat": 4, "nbformat_minor": 5,
    }
    p = tmp_path / "Sudoku-99-X.ipynb"
    p.write_text(json.dumps(nb, ensure_ascii=False), encoding="utf-8")
    return p


def test_scan_notebook_attrape_les_deux_cellules_fondatrices(tmp_path):
    p = _write_nb(tmp_path, [FOUNDING_CELL_8_CORE, FOUNDING_CELL_12_CORE])
    defects = scan_notebook(p)
    cells = {d["cell"] for d in defects}
    assert cells == {0, 1}
    assert all(d["test"] == "mannwhitneyu" for d in defects)


def test_scan_notebook_notebook_corrigee_est_propre(tmp_path):
    p = _write_nb(tmp_path, [CORRECTED_CELL_8_CORE, CORRECTED_CELL_12_CORE])
    assert scan_notebook(p) == []


# ---------------------------------------------------------------------------
# La garde elle-meme -- la famille Sudoku doit etre propre
# ---------------------------------------------------------------------------

def test_self_test_embarque():
    assert self_test() is True


def test_famille_sudoku_sans_pooling():
    """Le garde #14827 : echoue si un test non apparie s'applique a des
    mesures repetees poolees dans la famille Sudoku."""
    defects = [d for d in sweep("Sudoku") if not d.get("skipped_demo")]
    assert defects == [], (
        "pooling de mesures repetees vers un test non apparie : "
        f"{defects}")
