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
   feature reste borne par ``sqrt(n)`` ;
4. la **quatrieme lecture** (``power_by_trace``) : la puissance est-elle la
   meme sur toutes les jambes du protocole ? L'echelle par paire est
   relative a la jambe, donc les jambes bruyantes et les jambes calmes
   sont directement comparables dans l'unite ``d``.
"""
from __future__ import annotations

from pathlib import Path

import numpy as np
import pytest

from ict.humor_power import (
    exact_null_rates,
    n_for_power,
    null_norms,
    observed_z,
    per_pair_rms,
    power_by_trace,
    power_curve,
    power_vs_pairs,
    power_vs_threshold,
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
# Puissance en fonction du nombre de paires
# --------------------------------------------------------------------------- #


def test_per_pair_rms_is_n_independent_scale() -> None:
    # L'echelle par paire est ||diffs_f||_2 / sqrt(n) : elle vaut la
    # dispersion du bruit d'une seule paire, donc elle ne depend pas du
    # nombre de paires une fois normalisee.
    diffs = _synthetic_diffs(n_pairs=20, n_features=30)
    rms = per_pair_rms(diffs)
    assert rms.shape == (30,)
    assert np.all(rms > 0)
    # Coherence : rms * sqrt(n) == ||diffs_f||_2
    assert np.allclose(rms * np.sqrt(20), null_norms(diffs))


def test_power_vs_pairs_reports_z_shift_scaling() -> None:
    # Le deplacement du z vaut d * sqrt(n) : le gain d'une paire vaut
    # sqrt(n), pas n. C'est la loi de la puissance, verifiee ici sur la
    # sortie de l'organe (pas seulement sur le papier).
    diffs = _synthetic_diffs(n_pairs=20, n_features=60)
    res = power_vs_pairs(diffs, [10, 20], [0.5], n_bootstraps=2, n_replicates=30, seed=3)
    shifts = {row["n_pairs"]: row["z_shift"] for row in res["rows"]}
    assert shifts[10] == pytest.approx(0.5 * np.sqrt(10))
    assert shifts[20] == pytest.approx(0.5 * np.sqrt(20))
    assert shifts[20] / shifts[10] == pytest.approx(np.sqrt(2))


def test_power_vs_pairs_null_effect_never_fires_the_rule() -> None:
    # d = 0 : aucune feature plantee ne bouge, la regle ne s'ecole pas.
    diffs = _synthetic_diffs(n_pairs=16, n_features=80)
    res = power_vs_pairs(diffs, [16], [0.0], n_bootstraps=3, n_replicates=60, seed=11)
    row = res["rows"][0]
    assert row["p_rule"] == 0.0
    assert row["p_any"] < 0.15


def test_power_vs_pairs_grows_with_more_pairs() -> None:
    # A effet par paire constant, plus de paires = plus de puissance :
    # c'est la question a laquelle la fonction repond.
    diffs = _synthetic_diffs(n_pairs=30, n_features=200)
    res = power_vs_pairs(
        diffs, [10, 20, 30], [0.6], n_bootstraps=4, n_replicates=60, seed=13
    )
    p_by_n = {row["n_pairs"]: row["p_rule"] for row in res["rows"]}
    assert p_by_n[30] >= p_by_n[20] >= p_by_n[10]


def test_power_vs_pairs_rejects_too_few_pairs() -> None:
    diffs = _synthetic_diffs(n_pairs=10, n_features=20)
    with pytest.raises(ValueError):
        power_vs_pairs(diffs, [1], [0.5], n_bootstraps=1, n_replicates=5)


def test_power_vs_pairs_reports_its_contract() -> None:
    diffs = _synthetic_diffs(n_pairs=12, n_features=40)
    res = power_vs_pairs(diffs, [6, 12], [0.2, 0.4], n_bootstraps=1, n_replicates=20, seed=2)
    assert res["threshold"] == 3.0
    assert res["min_same_side"] == 3
    assert res["source_pairs"] == 12
    assert len(res["rows"]) == 4


# --------------------------------------------------------------------------- #
# Puissance jambe par jambe (quatrieme lecture)
# --------------------------------------------------------------------------- #


def test_n_for_power_returns_smallest_satisfying_n() -> None:
    # La reponse est le plus petit n mesure qui atteint la cible, pas le
    # plus grand ni une interpolation.
    rows = [
        {"n_pairs": 30, "effect_size": 0.5, "p_rule": 0.10},
        {"n_pairs": 60, "effect_size": 0.5, "p_rule": 0.55},
        {"n_pairs": 90, "effect_size": 0.5, "p_rule": 0.95},
        {"n_pairs": 30, "effect_size": 0.3, "p_rule": 0.02},
    ]
    assert n_for_power(rows, 0.5) == 90
    assert n_for_power(rows, 0.3) is None


def test_n_for_power_is_none_when_target_unreachable() -> None:
    # Aucune valeur balayee n'atteint la cible : la reponse est None
    # (« meme le plus grand n mesure ne suffit pas »), pas un n fantaisiste.
    rows = [{"n_pairs": n, "effect_size": 0.2, "p_rule": 0.1} for n in (30, 60)]
    assert n_for_power(rows, 0.2, target=0.8) is None


def test_power_by_trace_contract_on_real_traces() -> None:
    # La quatrieme lecture : la puissance est-elle la meme sur toutes les
    # jambes ? Le contrat doit exposer, par jambe, l'echelle de bruit
    # (relative a la jambe) et les lignes de puissance.
    traces = sorted(_ICT_SERIES.glob("traces/humor35b_*.npz"))
    if not traces:
        pytest.skip("traces humor35b absentes du depot")
    from ict.humor_pairs import build_pairs, load_corpus_dur

    res = power_by_trace(
        traces[:2],
        build_pairs(load_corpus_dur()),
        [30, 90],
        [0.5],
        n_bootstraps=2,
        n_replicates=20,
        seed=42,
    )
    assert len(res["legs"]) == 2
    assert res["threshold"] == 3.0
    assert res["min_same_side"] == 3
    for leg in res["legs"]:
        assert leg["n_active_features"] > 0
        assert leg["per_pair_rms_median"] > 0
        assert leg["z_ceiling"] == pytest.approx(np.sqrt(30))
        assert len(leg["rows"]) == 2


def test_power_by_trace_null_effect_never_fires_the_rule() -> None:
    # Temoin negatif de la quatrieme lecture : sous effet nul, la regle ne
    # s'ecole sur aucune jambe.
    traces = sorted(_ICT_SERIES.glob("traces/humor35b_*.npz"))
    if not traces:
        pytest.skip("traces humor35b absentes du depot")
    from ict.humor_pairs import build_pairs, load_corpus_dur

    res = power_by_trace(
        traces[:1],
        build_pairs(load_corpus_dur()),
        [30],
        [0.0],
        n_bootstraps=2,
        n_replicates=20,
        seed=42,
    )
    row = res["legs"][0]["rows"][0]
    assert row["p_rule"] == 0.0
    assert row["p_any"] < 0.15


# --------------------------------------------------------------------------- #
# Le seuil : ce que la convention pre-enregistree coute
# --------------------------------------------------------------------------- #


def test_power_vs_threshold_contract() -> None:
    diffs = _synthetic_diffs(n_pairs=12, n_features=200)
    res = power_vs_threshold(
        diffs, [2.0, 3.0], [0.0, 0.5], n_values=[10], n_bootstraps=2,
        n_replicates=20, seed=4,
    )
    assert res["min_same_side"] == 3
    assert res["source_pairs"] == 12
    assert len(res["rows"]) == 4          # 1 n x 2 seuils x 2 effets
    for row in res["rows"]:
        assert 0.0 <= row["p_rule"] <= 1.0
        assert 0.0 <= row["p_any"] <= 1.0
        assert row["z_shift"] == pytest.approx(row["effect_size"] * np.sqrt(10))


def test_power_vs_threshold_false_positives_rise_as_threshold_falls() -> None:
    # Baisser le seuil fait s'ecoler la regle **sous null** : le seuil
    # pre-enregistre n'est pas un detail de forme, c'est ce qui tient la
    # specificite.
    diffs = _synthetic_diffs(n_pairs=12, n_features=400)
    res = power_vs_threshold(
        diffs, [1.5, 2.0, 3.0, 4.0], [0.0], n_values=[12], n_bootstraps=3,
        n_replicates=40, seed=6,
    )
    fpr = {row["threshold"]: row["p_rule"] for row in res["rows"]}
    assert fpr[1.5] >= fpr[2.0] >= fpr[3.0] >= fpr[4.0]
    assert fpr[4.0] == 0.0


def test_power_vs_threshold_effect_adds_power_over_the_null() -> None:
    # A seuil fixe, l'effet doit augmenter la frequence d'ecol de la regle
    # par rapport au null : sinon la mesure ne mesure rien.
    diffs = _synthetic_diffs(n_pairs=12, n_features=300)
    res = power_vs_threshold(
        diffs, [3.0], [0.0, 0.8], n_values=[12], n_bootstraps=3,
        n_replicates=40, seed=8,
    )
    p = {row["effect_size"]: row["p_rule"] for row in res["rows"]}
    assert p[0.8] > p[0.0]


def test_n_for_power_refuses_mixed_thresholds() -> None:
    # Des lignes portant plusieurs seuils sans seuil demande : l'appel
    # echoue plutot que de melanger des seuils en silence.
    rows = [
        {"n_pairs": 30, "threshold": 2.0, "effect_size": 0.5, "p_rule": 0.9},
        {"n_pairs": 30, "threshold": 3.0, "effect_size": 0.5, "p_rule": 0.1},
    ]
    with pytest.raises(ValueError):
        n_for_power(rows, 0.5, 0.8)
    assert n_for_power(rows, 0.5, 0.8, threshold=2.0) == 30
    assert n_for_power(rows, 0.5, 0.8, threshold=3.0) is None


# --------------------------------------------------------------------------- #
# La reference qui ne degrade pas : null exact (sixieme lecture)
# --------------------------------------------------------------------------- #


def test_exact_null_rates_contract() -> None:
    diffs = _synthetic_diffs(n_pairs=16, n_features=300)
    res = exact_null_rates(diffs, [2.0, 3.0], n_flips=200, seed=5)
    assert res["n_flips"] == 200
    assert res["n_pairs"] == 16
    assert res["min_same_side"] == 3
    assert len(res["rows"]) == 2
    for row in res["rows"]:
        assert 0.0 <= row["p_any"] <= 1.0
        assert 0.0 <= row["p_rule"] <= row["p_any"] + 1e-12
        assert row["n_over_mean"] >= 0.0


def test_exact_null_rates_matches_power_curve_null_row() -> None:
    # Les deux procedures mesurent le meme objet (la queue nulle exacte) par
    # des chemins differents : `power_curve` en rangant les nulls par
    # replicat, `exact_null_rates` par blocs de retournements. Elles doivent
    # s'accorder sur la meme queue.
    diffs = _synthetic_diffs(n_pairs=16, n_features=400)
    exact = exact_null_rates(diffs, [3.0], n_flips=2000, seed=9)
    curve = power_curve(diffs, [0.0], n_replicates=2000, seed=9)
    assert abs(exact["rows"][0]["p_any"] - curve["rows"][0]["p_any"]) <= 0.03
    assert exact["rows"][0]["p_rule"] <= exact["rows"][0]["p_any"] + 1e-12


def test_exact_null_rates_never_exceeds_threshold_rate() -> None:
    # Baisser le seuil ne peut pas diminuer le taux de faux positifs : le
    # seuil pre-enregistre (3) est celui qui tient la specificite.
    diffs = _synthetic_diffs(n_pairs=16, n_features=400)
    rows = exact_null_rates(diffs, [2.0, 2.5, 3.0, 3.5], n_flips=600, seed=13)["rows"]
    p_any = [row["p_any"] for row in rows]
    p_rule = [row["p_rule"] for row in rows]
    assert p_any == sorted(p_any, reverse=True)
    assert p_rule == sorted(p_rule, reverse=True)
    assert rows[-1]["p_rule"] < 0.02


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
