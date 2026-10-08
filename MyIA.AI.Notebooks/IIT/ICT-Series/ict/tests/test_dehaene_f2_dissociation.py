"""Tests unitaires pour ``ict.dehaene_f2_dissociation`` — volet direct A/B/C.

Case F2 (Dehaene, Global Neuronal Workspace) — test direct issu de #19343,
mesuré le 2026-10-08 sur les graines pré-enregistrées {0, 1, 7, 42}
(dissociations-matrix.md, ligne F2 ; carnet
``ICT-Dissociation-DehaeneF2-SelfReport.ipynb``) :

  1. (appariement) Deux agents d'une même paire partagent leur **spectre**
     (mêmes valeurs propres) et different par leur base propre — condition de
     « capacité égale, identité distincte » de l'issue.
  2. (lésion) Avec ``store_active=False``, le store est nul **partout** : le
     régime B est une lésion, pas un aveuglement.
  3. (contrôle C) Des prédicteurs non entraînés rendent un score **exactement
     nul** : c'est le contrôle de non-dégénérescence (il a rejeté la première
     version du protocole, où il valait -0,99).
  4. (verdict) La règle pré-enregistrée ``|A - B| < 2*sigma_B`` classe en
     ``F2_FALSIFIED_SELF_PERSISTS``, et ``delta >= 2*sigma_B`` en
     ``F2_CONFIRMED_EXTENDED_REQUIRED``.
  5. (bout en bout) ``run_abc_regimes`` sur deux graines courtes rend les clés
     attendues, un verdict valide et ``sanity_C_near_zero`` vrai.
"""

from __future__ import annotations

import numpy as np

from ict import dehaene_f2_dissociation as f2


def test_paired_agents_share_spectrum_but_not_eigenbasis():
    d = 8
    scales = 0.65 + 0.25 * np.random.default_rng(1001).random(d)
    p_self = f2._agent_params(1002, d, scales=scales)
    p_other = f2._agent_params(1003, d, scales=scales)

    ev_self = np.sort(np.linalg.eigvals(p_self.A).real)
    ev_other = np.sort(np.linalg.eigvals(p_other.A).real)

    assert np.abs(ev_self - ev_other).max() < 1e-10
    assert np.linalg.norm(p_self.A - p_other.A) > 0.1


def test_lesion_zeroes_the_store_everywhere():
    p = f2._agent_params(1002, d=8)
    _, h = f2._simulate(p, T=200, rng=np.random.default_rng(0),
                        store_active=False)
    assert np.all(h == 0.0)


def test_untrained_model_has_zero_recognition():
    p_self = f2._agent_params(1002, d=8)
    x_s, h_s = f2._simulate(p_self, T=600, rng=np.random.default_rng(4))
    x_o, h_o = f2._simulate(p_self, T=600, rng=np.random.default_rng(5))

    score, _ = f2._regime_score(x_s, h_s, x_o, h_o,
                                np.random.default_rng(1), use_store=True,
                                untrained=True, n_shuffles=10)
    assert abs(score) < 1e-9


def test_verdict_rule_follows_the_preregistration():
    falsified, _ = f2._abc_verdict([0.30, 0.28, 0.31, 0.29],
                                   [0.29, 0.30, 0.28, 0.30])
    assert falsified == "F2_FALSIFIED_SELF_PERSISTS"

    confirmed, details = f2._abc_verdict([0.80, 0.90, 0.85, 0.88],
                                         [0.10, 0.11, 0.09, 0.10])
    assert confirmed == "F2_CONFIRMED_EXTENDED_REQUIRED"
    assert any("delta" in d for d in details)


def test_run_abc_regimes_end_to_end():
    out = f2.run_abc_regimes(seed_bases=(0, 1), T=800, n_shuffles=10)

    assert out["case"] == "F2_dehaene_abc"
    assert len(out["scores_by_seed"]) == 2
    assert out["sanity_C_near_zero"] is True
    assert out["verdict"] in {
        "F2_CONFIRMED_EXTENDED_REQUIRED",
        "F2_FALSIFIED_SELF_PERSISTS",
        "F2_INVERTED_STORE_HURTS",
    }
    for row in out["scores_by_seed"]:
        assert abs(row["C"]) < 1e-9
        assert 0.0 <= row["store_share_A"] <= 1.0
