# -*- coding: utf-8 -*-
"""Tests de la courbe de puissance du seuil ``|z| > 3`` (ICT-35, #11690).

La courbe repond a une question que l'instrument ne repondait pas : quelle
taille d'effet faudrait-il pour que la regle ``>= 3 features |z| > 3 du meme
cote`` s'ecole ? Les tests verifient trois choses :

1. la **coherence** du module avec l'instrument natif (``ict/humor_pairs.py``) :
   la dispersion nulle exacte du module est la meme que celle que
   l'instrument estime par 2048 tirages de signes ;
2. l'**integrite du null** : sous ``delta = 0`` la regle ne s'ecole pas, et la
   queue nulle mesuree reste celle que l'organe natif publie (ICT-35d,
   « Lecture 5 bis ») ;
3. la **monotonie et le plafond** de la courbe : la puissance croît avec
   l'effet, la regle exige bien trois features du meme cote, et le z d'une
   feature reste borne par ``sqrt(n)``.
"""
from __future__ import annotations

from pathlib import Path

import numpy as np
import pytest

from ict.humor_power import (
    null_norms,
    observed_z,
    power_curve,
    z_ceiling,
)

_ICT_SERIES = Path(__file__).resolve().parents[2]
_TRACE_MID_TRAINED = _ICT_SERIES / "traces" / "humor35b_qwen35-2b-base_layer12of24_trained.npz"

# Ancre publiee par l'organe natif (PR #27208, ICT-35d « Lecture 5 bis ») :
# sous null, 96,7 % des tirages ne produisent AUCUNE feature au-dela de 3
# sigma, soit P(au moins une feature au-dela) = 3,3 %. La mesure ci-dessous
# est une estimation de Monte-Carlo (1000 replicats, erreur type ~0,5
# point) : la bande de 3 points couvre l'ecart mesure/tire sans masquer une
# derive de construction.
_NULL_TAIL_NATIVE = 0.033
_NULL_TAIL_BAND = 0.03


def _synthetic_diffs(n_pairs: int = 12, n_features: int = 400, seed: int = 7) -> np.ndarray:
    rng = np.random.default_rng(seed)
    return rng.normal(size=(n_pairs, n_features))


# --------------------------------------------------------------------------- #
# Coherence avec l'instrument natif
# --------------------------------------------------------------------------- #


def test_null_norms_match_empirical_sign_flip_std() -> None:
    # La dispersion nulle exacte est ||diffs_f||_2 / n ; l'instrument
    # l'estime par l'ecart-type empirique de 2048 tirages de signes. Les
    # deux doivent coincider a moins de 5 % pres (erreur type de l'estimateur
    # empirique : 1/sqrt(2*2048) = 1,6 %).
    diffs = _synthetic_diffs(n_pairs=12, n_features=60)
    n = diffs.shape[0]
    rng = np.random.default_rng(3)
    draws = np.empty((400, diffs.shape[1]))
    for d in range(400):
        signs = rng.choice(np.array([-1.0, 1.0]), size=(n, 1))
        draws[d] = (diffs * signs).mean(axis=0)
    empirical = draws.std(axis=0)
    exact = null_norms(diffs) / n
    rel = np.abs(empirical - exact) / exact
    assert np.median(rel) < 0.05
    assert np.max(rel) < 0.15


def test_observed_z_matches_instrument_ratio() -> None:
    # Le z de l'instrument est (moyenne par paire) / (dispersion nulle) ; les
    # deux facteurs portent le meme 1/n, donc z = somme(diffs) / ||diffs||.
    diffs = _synthetic_diffs(n_pairs=30, n_features=200)
    n = diffs.shape[0]
    norms = null_norms(diffs)
    instrument = diffs.mean(axis=0) / (norms / n)
    assert np.allclose(observed_z(diffs), instrument, rtol=1e-9, atol=1e-12)


def test_z_ceiling_is_sqrt_n() -> None:
    assert z_ceiling(30) == pytest.approx(np.sqrt(30))
    # Le z d'une feature est un produit scalaire normalise : Cauchy-Schwarz
    # le borne par sqrt(n), et une feature alignee l'atteint.
    diffs = np.ones((16, 1))
    assert abs(observed_z(diffs)[0]) == pytest.approx(z_ceiling(16))


def test_observed_z_bounded_by_ceiling() -> None:
    diffs = _synthetic_diffs(n_pairs=30, n_features=500)
    assert np.max(np.abs(observed_z(diffs))) <= z_ceiling(30) + 1e-9


# --------------------------------------------------------------------------- #
# Integrite de la courbe
# --------------------------------------------------------------------------- #


def test_power_curve_null_state_does_not_fire() -> None:
    diffs = _synthetic_diffs()
    res = power_curve(diffs, [0.0], n_planted=3, n_replicates=200, seed=1)
    row = res["rows"][0]
    assert row["p_rule"] == 0.0
    assert row["p_any"] < 0.10


def test_power_curve_requires_three_features_on_one_side() -> None:
    # Une seule feature plantee ne peut pas satisfaire la regle « 3 du meme
    # cote » : c'est un temoin de la forme de la regle, pas de l'effet.
    diffs = _synthetic_diffs()
    res = power_curve(diffs, [3.0, 5.0], n_planted=1, n_replicates=200, seed=1)
    assert all(row["p_rule"] == 0.0 for row in res["rows"])
    assert res["rows"][-1]["p_any"] > 0.5


def test_power_curve_is_monotone_in_delta() -> None:
    diffs = _synthetic_diffs()
    res = power_curve(
        diffs, [0.0, 1.0, 2.0, 3.0, 4.0, 5.0], n_planted=3, n_replicates=200, seed=5
    )
    p_rule = [row["p_rule"] for row in res["rows"]]
    assert p_rule == sorted(p_rule)
    assert p_rule[-1] > p_rule[0]


def test_power_curve_reports_its_contract() -> None:
    diffs = _synthetic_diffs()
    res = power_curve(diffs, [0.0, 3.0], n_planted=3, n_replicates=50, seed=2)
    assert res["threshold"] == 3.0
    assert res["min_same_side"] == 3
    assert res["n_planted"] == 3
    assert res["n_pairs"] == diffs.shape[0]
    assert res["z_ceiling"] == pytest.approx(np.sqrt(diffs.shape[0]))
    assert len(res["rows"]) == 2


def test_power_curve_rejects_impossible_plant() -> None:
    diffs = _synthetic_diffs(n_features=4)
    with pytest.raises(ValueError):
        power_curve(diffs, [0.0], n_planted=9, n_replicates=10)


# --------------------------------------------------------------------------- #
# Ancre sur les traces reelles (integration) -- le temoin de coherence
# --------------------------------------------------------------------------- #


@pytest.mark.skipif(
    not _TRACE_MID_TRAINED.exists(),
    reason="traces humor35b absentes du depot",
)
def test_real_traces_null_tail_matches_native_organ() -> None:
    """L'ancre : la queue nulle du module est celle de l'organe natif.

    ICT-35d (« Lecture 5 bis ») publie que la jambe agregee ne produit
    AUCUNE feature au-dela de 3 sigma, et que le null en produit rarement
    (96,7 % des tirages a zero). Le module doit retrouver cette queue, et
    la regle de detection ne doit pas s'ecoler sous l'effet nul.
    """
    from ict.humor_pairs import build_pairs, load_corpus_dur
    from ict.humor_power import zone_diffs

    pairs = build_pairs(load_corpus_dur())
    diffs = zone_diffs(_TRACE_MID_TRAINED, pairs)
    assert diffs.shape[0] == 30

    # L'observation elle-meme : aucune feature au-dela du seuil sur la jambe
    # agregee (le resultat d'ICT-35b/35d).
    assert int((np.abs(observed_z(diffs)) > 3).sum()) == 0

    res = power_curve(diffs, [0.0], n_planted=3, n_replicates=500, seed=42)
    row = res["rows"][0]
    assert row["p_rule"] == 0.0
    assert abs(row["p_any"] - _NULL_TAIL_NATIVE) <= _NULL_TAIL_BAND
