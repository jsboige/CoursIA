# -*- coding: utf-8 -*-
"""Tests du module ict.goedel_machine -- gates G1-G4 + OOPS + mesures.

Chaque gate confronte une claim du papier (Schmidhuber 2006, arXiv:cs/0309048)
a une mesure mecanique sur le jouet. Les valeurs attendues (phase 27, marge 14,
ecart de phases 8...) sont calculees a la main dans le carnet ICT-49 et
reprises ici comme constantes : un changement de comportement du module doit
faire echouer le test correspondant, pas glisser silencieusement.
"""

from __future__ import annotations

from ict.goedel_machine import (
    DEFAULT_TABLE,
    EXPENSIVE_TABLE,
    L_MAX,
    W_LEVER,
    LeverWorld,
    biops,
    enumerate_techniques,
    g1_lever,
    g2_bogus_exhaustive,
    g3_th51_cost_scaling,
    g4_greedy_global,
    oops_reuse,
    run_technique,
    short_technique_long_proof,
    technique_cost,
)


def test_espace_borne_est_complet_et_croissant():
    """L'espace enumere : 6 symboles, L_MAX 5 -> 9331 techniques, tries par cout."""
    space = enumerate_techniques()
    attendu = sum(len(DEFAULT_TABLE) ** L for L in range(L_MAX + 1))
    assert len(space) == attendu == 9331
    couts = [c for _w, c in space]
    assert couts == sorted(couts)
    assert technique_cost((), DEFAULT_TABLE) == 7  # HALT seul


def test_g1_levier_feu_marge_egale_gain():
    """G1 (par. 4.4) : feu sur la technique du levier, marge prouvee == gain realise."""
    m = g1_lever()
    res = m["biops"]
    assert res.fired, "BIOPS doit trouver le switchprog du levier"
    assert res.technique == W_LEVER
    assert res.switchprog == "lever"
    assert res.code_cost == 21  # 1+2+6+2+3 + HALT(7)
    assert res.phase == 27      # budget 2^(27-21)=64 >= cout de feu 54
    assert res.margin == m["u_lever"] - m["u_keep"] == 14
    assert m["margin_equals_gain"] is True
    assert m["u_keep"] == 0


def test_g2_bogus_jamais_feu():
    """G2 (FAQ 7) : zero feu boge, exhaustif sur tout l'espace borne."""
    m = g2_bogus_exhaustive()
    assert m["bogus_fires_in_biops"] == 0
    assert m["w_bogus_fires"] is False
    assert m["w_bogus_outcome"] == "end"
    assert m["techniques_with_bogus_that_fire"] == 0
    assert m["space_size"] == 9331


def test_g3_th51_ecart_de_phases_exact():
    """G3 (Th. 5.1) : ecart de phases == Delta c (8) ; travaux croissent sous 2^8."""
    m = g3_th51_cost_scaling()
    cheap, expensive = m["cheap"], m["expensive"]
    assert cheap.fired and expensive.fired
    assert cheap.code_cost == 21
    assert expensive.code_cost == 29
    assert m["delta_cost"] == 8
    assert m["phase_gap"] == 8  # la prediction 1/P(w), lue sur les phases, exacte
    assert m["work_ratio"] > 1.0
    # saturation straight-line : le rapport reste sous la borne 2^Delta_c
    assert m["work_ratio"] < m["predicted_ratio_bound"]
    assert cheap.margin == expensive.margin == 14
    assert cheap.switchprog == expensive.switchprog == "lever"


def test_g4_greedy_est_global_et_stationnaire():
    """G4 (Th. 4.1) : feu = argmax des candidats futurs ; aucun second switch prouvable."""
    m = g4_greedy_global()
    assert m["fired_is_argmax"] is True
    assert dict(m["candidates"]) == {"keep": 0, "lever": 14, "setup_forever": 0}
    assert m["best"] == ("lever", 14)
    assert m["second_switch_fires"] is False


def test_oops_transfert_et_acceleration():
    """OOPS (par. 5.2) : la technique gelee transfere sur k=3 et feutre sans re-chercher."""
    m = oops_reuse()
    assert m["fresh"].fired and m["with_frozen"].fired
    assert m["expected_margin_b"] == 13  # presses 8..20 (k=3 : setups en 5,6,7)
    assert m["transfers"] is True
    assert m["margin_b"] == 13
    # la passe gelee en tete evite la re-recherche : ordres de grandeur
    assert m["speedup"] > 100.0


def test_technique_courte_preuve_longue():
    """Mesure cle : 5 symboles / 21 bits produisent une preuve de 50 applications de regles."""
    m = short_technique_long_proof()
    res = m["biops"]
    assert res.fired
    assert m["technique_symbols"] == 5
    assert m["technique_bits"] == 21
    assert m["proof_rule_applications"] == 50  # 3 x (20-4) + CMP + cible
    assert m["ratio_log2"] == 29


def test_determinisme_biops():
    """Deux passes identiques -> mesures byte-identiques (aucun aleatoire)."""
    a = biops(LeverWorld(), i_max=30)
    b = biops(LeverWorld(), i_max=30)
    assert a.total_steps == b.total_steps
    assert a.technique == b.technique
    assert a.phase == b.phase


def test_budget_insuffisant_tue_la_technique():
    """Sous budget BIOPS trop bas, la technique du levier avorte (outcome budget)."""
    monde = LeverWorld()
    out = run_technique(W_LEVER, monde, DEFAULT_TABLE, budget=10)
    assert not out.fired
    assert out.outcome == "budget"
    # avec le budget de phase 27 (2^6 = 64), elle feutre
    out64 = run_technique(W_LEVER, monde, DEFAULT_TABLE, budget=64)
    assert out64.fired and out64.fire_cost is not None and out64.fire_cost <= 64
