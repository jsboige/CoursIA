"""Tests unitaires pour ``ict.extended_mind_store`` (case 9, #8182 iceberg L4).

Pins des prédictions pré-enregistrées (dissociations-matrix.md, case 9 —
parité esprit étendu, Clark & Chalmers 1998), mesurées le 2026-08-25 :

  1. (P1) parité de performance sous glue : R_p = err_Otto/err_Inga à
     baseline dans [0.80, 1.20] (mesuré : médiane ≈ 1.04).
  2. (P2) double dissociation : rho_split_Otto >= 3 sur >= 4/5 seeds
     **FALSIFIÉ au seuil** — mesuré 2.24-2.97, 0/5 >= 3. La
     localisation EST présente (rho_O >= 2.2 sur 5/5, au-dessus du
     null-a < 2) mais l'épinglage adaptatif absorbe ~35 % de la
     signature (estimé ~3.9 sans adaptation) : zone grise [2, 3).
     Le contrôle passe : rho_split_Inga sous budget apparié ≈ 1.0
     (dégradation uniforme, pas de localisation).
  3. (P3) saturation de l'adaptation : w3/w1 dans [0.7, 1.6]
     (mesuré : médiane 1.14).
  4. (Sanity) déterminisme par seed ; budget apparié Inga dans
     [0.85, 1.15] ; l'erreur consult-store double au shift ; l'erreur
     cache-hit reste stable ; le gating p_read fonctionne ; la
     partition hot = 6 clés distinctes récentes ; l'épinglage
     s'incrémente sur échec de consultation.
"""

from __future__ import annotations

import numpy as np
import pytest

from ict.extended_mind_store import (
    CompositeAgent,
    ExtendedAgent,
    FactWorld,
    _mean_err,
    _run_arm,
    run_case9,
)


@pytest.fixture(scope="module")
def case9() -> dict:
    """Protocole complet 5 seeds — déterministe, partagé entre gates."""
    return run_case9()


class TestP1Parite:
    def test_r_p_dans_bande_predit(self, case9):
        med = case9["summary"]["r_p_median"]
        assert 0.80 <= med <= 1.20, f"P1 rompu : R_p = {med}"

    def test_r_p_pin_mesure(self, case9):
        # Anti-dérive : la mesure honnête est ≈ 1.04 (5/5 seeds dans
        # [0.95, 1.15] au cas par cas).
        for r in case9["rows"]:
            assert 0.95 <= r["r_p"] <= 1.15, (
                f"seed {r['seed']} : R_p = {r['r_p']} hors plage mesurée"
            )


class TestP2Dissociation:
    def test_seuil_3_non_atteint_mesure(self, case9):
        # Prédiction : >= 3 sur >= 4/5. Mesure honnête : 0/5 — le
        # test PIN le verdict enregistré (anti-rétrodict°).
        n = case9["summary"]["rho_otto_ge3_count"]
        assert n == 0, (
            f"Le verdict enregistré (0/5 >= 3) ne correspond plus à la "
            f"mesure ({n}/5) — le jouet a dérivé, ré-enregistrer"
        )

    def test_rho_otto_zone_grise(self, case9):
        # Localisation présente (>= 2.2 par seed) mais sous la barre
        # de confirmation : zone grise [2, 3), ni null-a ni confirmé.
        med = case9["summary"]["rho_otto_median"]
        assert 2.0 <= med < 3.0, (
            f"rho_otto_median = {med} hors de la zone grise mesurée"
        )

    def test_null_a_rejete_par_seed(self, case9):
        # Le null adversarial (a) exigeait rho_O < 2 : rejeté 5/5.
        for r in case9["rows"]:
            assert r["rho_split_otto"] >= 2.0, (
                f"seed {r['seed']} : rho_O = {r['rho_split_otto']} "
                f"< 2 — le null-a se réaliserait, verdict à ré-enregistrer"
            )

    def test_controle_inga_sans_localisation(self, case9):
        assert case9["summary"]["rho_inga_lt2"], "rho_inga >= 2 inattendu"
        med = case9["summary"]["rho_inga_median"]
        assert 0.5 <= med <= 1.5, (
            f"rho_inga_median = {med} hors plage mesurée (≈ 1.0)"
        )


class TestP3Saturation:
    def test_w3_w1_dans_bande_predit(self, case9):
        med = case9["summary"]["w3_w1_median"]
        assert 0.7 <= med <= 1.6, f"P3 rompu : w3/w1 = {med}"

    def test_w3_w1_pin_mesure(self, case9):
        for r in case9["rows"]:
            assert 0.8 <= r["w3_over_w1"] <= 1.5, (
                f"seed {r['seed']} : w3/w1 = {r['w3_over_w1']} "
                f"hors plage mesurée"
            )


class TestSanity:
    def test_determinisme_seed(self):
        a = run_case9(n_seeds=1)["summary"]
        b = run_case9(n_seeds=1)["summary"]
        assert a == b

    def test_budget_apparie_inga(self, case9):
        for r in case9["rows"]:
            assert 0.85 <= r["matched_budget_ratio"] <= 1.15, (
                f"seed {r['seed']} : match = {r['matched_budget_ratio']} "
                f"— l'appariement en budget d'erreur a dérivé"
            )

    def test_err_consult_double_au_shift(self, case9):
        for r in case9["rows"]:
            assert r["consult_after"] > 2.0 * r["consult_before"], (
                f"seed {r['seed']} : la disruption ne se lit pas sur "
                f"le canal externe"
            )

    def test_gate_lecture_store(self):
        otto = ExtendedAgent(seed=0)
        otto.p_read = 0.0
        otto.store[3] = 5.0
        answers = [otto.answer(3) for _ in range(20)]
        assert all(a == 0.0 for a in answers), (
            "p_read=0 doit fermer le canal : réponse 0.0 partout"
        )
        assert otto.pins[3] == 20, "chaque échec doit épingler"

    def test_partition_hot_six_cles_recentes(self):
        w = FactWorld(seed=0)
        inga = CompositeAgent(seed=0)
        rows = _run_arm(inga, w, t_base=5, t_shift=50, t_end=60)
        hot = {r["key"] for r in rows if r["qclass"] == "hot"}
        assert len(hot) == 6
        # les 6 hot = les 6 clés distinctes les plus récentes du
        # préfixe de requêtes
        seen: list[int] = []
        for k in w.queries[:50]:
            k = int(k)
            if k in seen:
                seen.remove(k)
            seen.insert(0, k)
        assert hot == set(seen[:6])

    def test_lecture_store_reussie_bruitee(self):
        otto = ExtendedAgent(seed=1)
        otto.p_read = 1.0
        otto.store[7] = 2.0
        vals = [otto.answer(7) for _ in range(200)]
        assert all(abs(v - 2.0) < 1.0 for v in vals)
        assert np.std(vals) > 0.01, "sigma_e doit bruiter la lecture"

    def test_verdict_coherent_avec_predicats(self, case9):
        s = case9["summary"]
        if s["verdict"] == "CONFIRMED":
            assert s["P1_pass"] and s["P2_pass"] and s["P3_pass"]
        else:
            assert not (s["P1_pass"] and s["P2_pass"] and s["P3_pass"])
        assert s["verdict"] == "INCONCLUSIF"
