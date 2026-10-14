"""Tests pytest pour fairness_organs.py -- Causal-Fairness (Epic #16620 P3).

Même stratégie que test_dowhy_organs.py : on exécute réellement le SCM
(pas de mock, H.1) et on vérifie que :

(a) le monde générateur répond aux nombres du notebook : TE/NDE/NIE
    correspondent à la théorie linéaire (0.5 / 0.3 / -0.2) à la
    tolérance Monte-Carlo près ;
(b) les deux identités de la famille TV (Lem 4.1 et Thm 4.2,
    Plecko-Bareinboim R-90) tiennent à la précision machine -- elles
    sont algébriques une fois les six mesures calculées sur les mêmes
    bruits partagés ;
(c) le naïf observationnel (TV) surestime le TE (le chemin Z -> A
    existe), signe et ordre de grandeur contrôlés ;
(d) la règle des 80 % rend le bon verdict sur un petit tableau croisé
    synthétique (ratio exact, disparate impact au seuil) ;
(e) reproductibilité par seed local -- deux appels retournent le même
    DataFrame.
"""

from __future__ import annotations

import sys
from pathlib import Path

import numpy as np
import pandas as pd
import pytest

_PARENT_DIR = Path(__file__).resolve().parent.parent
if str(_PARENT_DIR) not in sys.path:
    sys.path.insert(0, str(_PARENT_DIR))

import fairness_organs as fo


def test_theorie_lineaire_mesures():
    m = fo.mesures_equite(fo.generer_monde(200_000, seed=42))
    assert m["TE"] == pytest.approx(fo.TE_THEORIQUE, abs=0.01)
    assert m["NDE"] == pytest.approx(fo.NDE_THEORIQUE, abs=0.01)
    assert m["NIE"] == pytest.approx(fo.NIE_THEORIQUE, abs=0.01)


def test_identites_famille_tv_exactes():
    m = fo.mesures_equite(fo.generer_monde(50_000, seed=7))
    assert m["residu_lemme_4_1"] < 1e-9
    assert m["residu_thm_4_2"] < 1e-9


def test_naif_surestime_le_causal():
    m = fo.mesures_equite(fo.generer_monde(100_000, seed=0))
    assert m["TV"] > m["TE"] + 0.05          # le chemin spurious gonfle le naïf
    assert m["ExpSE1"] > 0.05 and m["ExpSE0"] < -0.05  # sélection dans les deux sens


def test_regle_80():
    df = pd.DataFrame({
        "groupe": ["a"] * 50 + ["b"] * 50,
        "ok": [True] * 40 + [False] * 10 + [True] * 20 + [False] * 30,
    })
    r = fo.regle_80(df, "groupe", "ok", defavorise="b")
    assert r["taux_defavorise"] == pytest.approx(0.40)
    assert r["taux_reference"] == pytest.approx(0.80)
    assert r["ratio"] == pytest.approx(0.50)
    assert r["disparate_impact"] is True
    r2 = fo.regle_80(df, "groupe", "ok", defavorise="a")
    assert r2["ratio"] == pytest.approx(2.0)
    assert r2["disparate_impact"] is False


def test_seed_local_reproductible():
    d1 = fo.generer_monde(2_000, seed=11)
    d2 = fo.generer_monde(2_000, seed=11)
    pd.testing.assert_frame_equal(d1, d2)
    d3 = fo.generer_monde(2_000, seed=12)
    assert not np.allclose(d1["Y"], d3["Y"])
