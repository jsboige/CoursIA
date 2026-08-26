"""Tests unitaires pour ``ict.strange_loop_selfmodel`` (case 8, #8182 iceberg L4).

Pins des prédictions pré-enregistrées (dissociations-matrix.md, case 8 —
fermeture du lacet, Hofstadter strange loops), mesurées le 2026-08-25 :

  1. (P1) fermeture : médiane d* <= 12 itérations, >= 4/5 seeds
     (mesuré : médiane 4.0, 5/5).
  2. (P2) double dissociation : rho_beta >= 3 sur >= 4/5 seeds
     (mesuré : 1/5, médiane 1.0) ET rho_alpha < 2 (mesuré : 1.0).
     **Dissociation FALSIFIÉE** — le canal d'action réductible à
     l'état ne porte aucune information indépendante : l'avantage
     d'auto-connaissance n'existe pas à ce régime.
  3. (P3) kink : gain au-delà du point fixe < 10% du gain initial
     (mesuré : 5/5 saturation, la fermeture ne régresse pas).
  4. (Sanity) fermeture/itération déterministes par seed ; le
     surrogate n'utilise jamais le canal action ; l'horizon de
     rattrapage est mesuré (aucune censure au cap sur le bras beta).
"""

from __future__ import annotations

import numpy as np
import pytest

from ict.strange_loop_selfmodel import (
    CompositeSurrogate,
    LoopPolicy,
    LoopSystem,
    SelfLoopModel,
    adaptation_horizon,
    closure_depth,
    closure_kink,
    run_case8,
)


@pytest.fixture(scope="module")
def case8() -> dict:
    """Protocole complet 5 seeds — déterministe, partagé entre gates."""
    return run_case8()


class TestP1Fermeture:
    def test_d_star_mediane_basse(self, case8):
        med = case8["summary"]["d_star_median"]
        assert med <= 12.0, f"P1 rompu : médiane d* = {med}"

    def test_d_star_4_sur_5(self, case8):
        n = case8["summary"]["d_star_le12_count"]
        assert n >= 4, f"P1 rompu : {n}/5 seeds seulement sous 12"


class TestP2Dissociation:
    def test_rho_beta_ge3_count_mesure(self, case8):
        # Prédiction : >= 4/5. Mesure honnête : 1/5 — FALSIFIÉ.
        # Le test PIN le résultat mesuré (anti-rétrodict°) :
        n = case8["summary"]["rho_beta_ge3_count"]
        assert n == 1, (
            f"Le verdict enregistré (1/5) ne correspond plus à la "
            f"mesure ({n}/5) — le jouet a dérivé, ré-enregistrer"
        )

    def test_rho_beta_mediane_mesuree(self, case8):
        med = case8["summary"]["rho_beta_median"]
        assert 0.5 < med < 3.0, (
            f"rho_beta_median = {med} hors de la plage mesurée (≈1.0)"
        )

    def test_rho_alpha_lt2(self, case8):
        assert case8["summary"]["rho_alpha_lt2"], "rho_alpha >= 2 inattendu"

    def test_aucune_censure_bras_beta(self, case8):
        for r in case8["rows"]:
            assert r["loop_beta"]["caught_up"], (
                f"seed {r['seed']} : horizon loop au cap — censure"
            )
            assert r["surrogate_beta"]["caught_up"], (
                f"seed {r['seed']} : horizon surrogate au cap — censure"
            )


class TestP3Kink:
    def test_saturation_4_sur_5(self, case8):
        n = case8["summary"]["kink_saturation_count"]
        assert n >= 4, f"P3 rompu : {n}/5 seeds seulement saturés"

    def test_kink_local(self):
        pol = LoopPolicy(seed=3)
        m = SelfLoopModel(seed=3)
        sys_ = LoopSystem(shift_kind="beta", seed=3)
        x = sys_.x
        for _ in range(2000):
            a = pol.act(x)
            x_next = sys_.step(a)
            m.update(x, a, x_next)
            x = x_next
        k = closure_kink(m, x, pol)
        assert k["finite"], "fermeture divergente"
        assert k["gain_beyond_fixpoint"] < 0.10 * max(
            k["gain_to_fixpoint"], 1e-9)


class TestSanity:
    def test_determinisme_seed(self):
        a = closure_depth(SelfLoopModel(seed=2), 0.5, LoopPolicy(seed=2))
        b = closure_depth(SelfLoopModel(seed=2), 0.5, LoopPolicy(seed=2))
        assert a == b

    def test_surrogate_aveugle_a_l_action(self):
        s = CompositeSurrogate(seed=0)
        s.v[:] = 1.0
        assert s.predict(0.3, 0.0) == s.predict(0.3, 5.0)

    def test_shift_beta_change_la_dynamique(self):
        pol = LoopPolicy(seed=0)
        sys_ = LoopSystem(shift_step=10, shift_kind="beta", seed=1)
        xs = []
        for _ in range(12):
            xs.append(sys_.step(pol.act(sys_.x)))
        assert not np.isclose(xs[8], xs[11])

    def test_horizon_mesure_non_censure(self):
        pol = LoopPolicy(seed=1)
        r = adaptation_horizon(SelfLoopModel(seed=1), pol,
                               shift_kind="beta", seed=1)
        assert r["caught_up"], "horizon au cap : mesure censurée"
        assert 0 < r["adaptation_horizon"] < 2000

    def test_shift_kind_invalide_rejete(self):
        with pytest.raises(ValueError):
            LoopSystem(shift_kind="gamma")
