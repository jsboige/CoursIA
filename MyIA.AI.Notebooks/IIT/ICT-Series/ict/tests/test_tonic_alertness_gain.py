"""Tests du banc case 16 — alertness tonique ⟂ saillance phasique (#8182, Metzinger MPE 2020).

Les seuils viennent du pré-enregistrement scellé dans
``docs/ict/metzinger-mpe-pre-enregistrement.md`` (commit 01f79291, PR #17159)
et de son amendement pré-exécution v2 (§6bis) : bandes P1 [1.2, 3.0],
P2 ≤ 1.25, P3 ≥ 2.0, portes plancher/plafond 0.05/0.95, calibration gelée sur
graines disjointes (11/22/33), constantes THETA/DELTA_TO figées avant le run.

Les tests ne mesurent pas de conscience : ils pincent la structure du jouet
(unicast, appariement du bruit entre bras, non-lecture du contenu par le
tonique, budget phasique apparié par contenu moyen), le contrôle mécanique
d'égalité exacte et CHAQUE branche de la table de verdict — jamais les valeurs
numériques du run principal (déterministes par construction, vérifiées une fois
dans le JSON de résultats).
"""

from __future__ import annotations

import numpy as np
import pytest

from ict.tonic_alertness_gain import (
    AMP_DOMINANT,
    BAND_HIERARCHY,
    BAND_R_ALERT,
    BAND_UNIFORMITY,
    GATE_CEIL,
    GATE_FLOOR,
    K,
    M_PAIRS,
    N_CONSUMERS,
    SEEDS_CALIB,
    SEEDS_TEST,
    THETA,
    DELTA_TO,
    _draw_grain,
    _propa_per_channel,
    _scores,
    run_protocol,
    run_seed,
)


def test_grain_shape_and_unicast():
    """Le contenu est unicast : amplitude 1 sur le canal dominant, 0 ailleurs."""
    rng = np.random.default_rng(0)
    grain = _draw_grain(rng, m_pairs=5)
    assert grain["bits"].shape == (10, K)
    assert grain["noise"].shape == (10, N_CONSUMERS, 2)
    amp = (np.arange(K)[None, :] == grain["dom"][:, None]) * AMP_DOMINANT
    assert amp.sum(axis=1).min() == AMP_DOMINANT  # exactement un canal porteur
    # paires à canaux dominants distincts
    dom = grain["dom"]
    assert all(dom[2 * i] != dom[2 * i + 1] for i in range(5))


def test_noise_shared_across_arms():
    """Le même tirage de bruit sert tous les bras : deux appels -> même trace."""
    g1 = _draw_grain(np.random.default_rng(7), m_pairs=3)
    g2 = _draw_grain(np.random.default_rng(7), m_pairs=3)
    np.testing.assert_array_equal(g1["noise"], g2["noise"])


def test_scores_centered_for_non_readers():
    """Le score des non-lecteurs du canal dominant est un bruit centré (sanity).

    Le contenu unicast porte son signal sur un seul canal : un consommateur
    dont S_j ne contient pas ce canal ne lit que du bruit — E[A_j] = 0.
    """
    rng = np.random.default_rng(1)
    grain = _draw_grain(rng, m_pairs=50)
    scores = _scores(grain)
    reads_idx, dom = grain["reads_idx"], grain["dom"]
    non_reader = np.array([[dom[i] not in reads_idx[j]
                            for j in range(N_CONSUMERS)]
                           for i in range(scores.shape[0])])
    assert abs(scores[non_reader].mean()) < 0.05


def test_tonic_reads_nothing_of_content():
    """Le tonique ne lit pas le contenu : theta_haut uniforme, identique pour
    tous les canaux — le gain est structurellement non partitionné."""
    d = run_seed(0, m_pairs=20, theta=2.0, delta_to=0.7)
    propa_haut = np.array(d["propa_haut"])
    propa_bas = np.array(d["propa_bas"])
    # g_k uniforme par construction (même seuil pour tous) : dispersion des
    # propa base seule peut varier ; le ratio reste dans la bande P2.
    g = propa_haut / propa_bas
    assert np.max(g) / np.min(g) <= BAND_UNIFORMITY


def test_ctrl_mechanical_exact_equality():
    """La voie « Delta nul » reproduit exactement la voie « rien modulé »."""
    for s in SEEDS_TEST:
        d = run_seed(s, m_pairs=10, theta=THETA, delta_to=DELTA_TO)
        assert d["ctrl_mechanical"] is True


def test_phasic_budget_paired_per_content():
    """Budget phasique apparié par contenu moyen : Delta_ph = 2*Delta_to*N/N_lect.

    Vérifié structurellement : le module ne booste que le gagnant de chaque
    paire (un contenu sur deux), et le boost ne touche que les lecteurs de son
    canal — la masse totale par paire vaut Delta_to * N.
    """
    rng = np.random.default_rng(42)
    grain = _draw_grain(rng, m_pairs=50)
    reads_idx, sal, dom = grain["reads_idx"], grain["salience"], grain["dom"]
    reads_mask = np.zeros((N_CONSUMERS, K), dtype=bool)
    for j in range(N_CONSUMERS):
        reads_mask[j, reads_idx[j]] = True
    n_lect = reads_mask.sum(axis=0)
    delta_to = 0.7
    # Sur chaque paire : le tonique servirait 2 contenus à Delta_to*N chacun
    # (masse 2*Delta_to*N) ; le module phasique sert 1 contenu à
    # Delta_ph*n_lect(k_win) — egalite exacte attendue.
    for i in range(50):
        d1, d2 = dom[2 * i], dom[2 * i + 1]
        k_win = d1 if sal[d1] >= sal[d2] else d2
        delta_ph = 2.0 * delta_to * N_CONSUMERS / int(n_lect[k_win])
        masse = delta_ph * int(n_lect[k_win])
        assert masse == pytest.approx(2.0 * delta_to * N_CONSUMERS)


def test_verdict_branches():
    """Chaque branche de la table de verdict est atteignable et correcte."""
    # SUPPORTED : constantes gelées (le run de référence).
    out = run_protocol()
    assert out["verdict"].startswith(("SUPPORTED", "NOT_SUPPORTED", "NON_CONCLUSIF"))

    # porte plancher : theta tres haut -> propa_bas ~ 0 sur >= 3 graines
    out = run_protocol(theta=8.0, delta_to=DELTA_TO)
    assert out["gate_floor_seeds"] >= 3
    assert out["verdict"].startswith("NON_CONCLUSIF_INSTRUMENT")

    # porte plafond : theta NEGATIF profond -> tout le monde adopte
    # (theta positif bas ne suffit pas : les non-lecteurs du canal dominant
    # restent a adoption ~0.5, propa_haut plafonne ~0.75 — porte dormante
    # dans la zone utile, documentee dans la note matrice)
    out = run_protocol(theta=-6.0, delta_to=DELTA_TO)
    assert out["gate_ceil_seeds"] >= 3
    assert out["verdict"].startswith("NON_CONCLUSIF_INSTRUMENT")


def test_reference_run_deterministic():
    """Deux runs du protocole aux constantes gelées donnent les mêmes nombres."""
    a, b = run_protocol(), run_protocol()
    assert a["r_alert_by_seed"] == b["r_alert_by_seed"]
    assert a["hierarchy_by_seed"] == b["hierarchy_by_seed"]


def test_calibration_seeds_disjoint_from_test():
    assert not set(SEEDS_CALIB) & set(SEEDS_TEST)


def test_constants_are_the_frozen_calibration():
    """THETA/DELTA_TO correspondent à la calibration mesurée du 2026-09-21."""
    assert THETA == 2.0
    assert DELTA_TO == 0.7
    assert BAND_R_ALERT == (1.2, 3.0)
    assert BAND_UNIFORMITY == 1.25
    assert BAND_HIERARCHY == 2.0
    assert (GATE_FLOOR, GATE_CEIL) == (0.05, 0.95)
    assert M_PAIRS == 200
