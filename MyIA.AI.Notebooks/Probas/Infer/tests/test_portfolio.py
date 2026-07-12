# -*- coding: utf-8 -*-
"""
Tests pour `exercice_portfolio.py` (Probas/Infer, CoursIA-2).

Module Python (numpy/scipy) traduisant le notebook Infer-3-Utility-Money
(C#/Infer.NET) : optimisation d'un portefeuille 3 actifs sous contrainte de
risque VaR/CVaR a 95 %.

Les tests assertent des INVARIANTS FINANCIERS et des resultats ANALYTIQUES
CONNUS, pas seulement l'absence de crash :
  - Constantes du module coherentes avec scipy.stats.norm (z_{0.95}, phi(z)).
  - Distribution du portefeuille : mu_p = w.mux (lineaire), sigma_p = sqrt(w².sig²)
    sous hypothese d'independance — verifie sur single-asset et melanges.
  - VaR_95 et CVaR_95 : formule correcte, recalulee de facon independante.
  - INVARIANT FONDAMENTAL : CVaR >= VaR (la perte moyenne au-dela de VaR domine
    toujours VaR) — la difference vaut sigma * (phi(z)/(1-alpha) - z) > 0.
  - Effet de diversification : sous independance, sigma_p <= moyenne ponderee
    des sigmas (sous-additivite, inegalite L2 <= L1).
  - analyse_portfolio : dict complet, drapeau `ok` = (CVaR < 5%), assertion sur
    la somme des poids = 1.
  - PRESETS : 7 allocations valides (somme=1, >= 0).
  - optimize_portfolio (scipy SLSQP) : solution realisable (CVaR <= 5%, poids >= 0,
    somme=1), bat le baseline 100% Obligataire, deterministe.
  - grid_search : solution admissible sur la grille, poids multiples du pas,
    determinisme, grille fine >= grille grossiere.

Run with: pytest tests/test_portfolio.py -v
"""

import math
import sys
from pathlib import Path

import numpy as np
import pytest
from scipy.stats import norm

# Ajoute Probas/Infer/ au path pour importer le module.
sys.path.insert(0, str(Path(__file__).parent.parent))

import exercice_portfolio as ep  # noqa: E402


# ============================================================================
# Constantes du module : coherentes avec scipy.stats.norm.
# ============================================================================

class TestConstants:
    def test_confidence_and_constraint(self):
        assert ep.CONFIDENCE == 0.95
        assert ep.CVAR_CONSTRAINT == 0.05

    def test_z_matches_scipy_ppf(self):
        """Z = norm.ppf(0.95) (quantile de la normale standard)."""
        assert ep.Z == pytest.approx(norm.ppf(0.95), abs=1e-12)

    def test_z_value_1_645(self):
        assert ep.Z == pytest.approx(1.6449, abs=1e-3)

    def test_phi_z_matches_scipy_pdf(self):
        assert ep.PHI_Z == pytest.approx(norm.pdf(norm.ppf(0.95)), abs=1e-12)

    def test_phi_z_value(self):
        assert ep.PHI_Z == pytest.approx(0.1031, abs=1e-3)

    def test_assets_definition(self):
        """3 actifs avec les parametres pedagogiques attendus."""
        assert set(ep.ASSETS.keys()) == {"Obligataire", "Actions", "Immobilier"}
        assert ep.ASSETS["Obligataire"] == {"mu": 0.03, "sigma": 0.02}
        assert ep.ASSETS["Actions"] == {"mu": 0.08, "sigma": 0.15}
        assert ep.ASSETS["Immobilier"] == {"mu": 0.05, "sigma": 0.08}

    def test_assets_returns_positive(self):
        for a in ep.ASSETS.values():
            assert a["mu"] > 0 and a["sigma"] > 0
            # Actions = rendement ET risque les plus eleves.
        assert ep.ASSETS["Actions"]["mu"] > ep.ASSETS["Obligataire"]["mu"]


# ============================================================================
# portfolio_distribution : combinaison lineaire de gaussiennes independantes.
# ============================================================================

class TestPortfolioDistribution:
    def test_single_asset_obligataire(self):
        mu, sigma = ep.portfolio_distribution(np.array([1.0, 0.0, 0.0]))
        assert mu == pytest.approx(0.03)
        assert sigma == pytest.approx(0.02)

    def test_single_asset_actions(self):
        mu, sigma = ep.portfolio_distribution(np.array([0.0, 1.0, 0.0]))
        assert mu == pytest.approx(0.08)
        assert sigma == pytest.approx(0.15)

    def test_single_asset_immobilier(self):
        mu, sigma = ep.portfolio_distribution(np.array([0.0, 0.0, 1.0]))
        assert mu == pytest.approx(0.05)
        assert sigma == pytest.approx(0.08)

    def test_equal_thirds(self):
        w = np.array([1 / 3, 1 / 3, 1 / 3])
        mu, sigma = ep.portfolio_distribution(w)
        assert mu == pytest.approx(0.16 / 3)
        expected_sigma = math.sqrt(((1 / 3) ** 2) * (0.0004 + 0.0225 + 0.0064))
        assert sigma == pytest.approx(expected_sigma)

    def test_mu_is_linear_in_weights(self):
        """mu_p = somme(w_i * mu_i) : doubler les poids double mu_p."""
        w = np.array([0.4, 0.4, 0.2])
        mu1, _ = ep.portfolio_distribution(w)
        mu2, _ = ep.portfolio_distribution(2 * w)
        assert mu2 == pytest.approx(2 * mu1)

    def test_sigma_formula_sqrt_weighted_variances(self):
        """sigma_p = sqrt(sum(w_i^2 * sigma_i^2)) sous independance."""
        w = np.array([0.5, 0.3, 0.2])
        _, sigma = ep.portfolio_distribution(w)
        mus = np.array([a["mu"] for a in ep.ASSETS.values()])
        sigmas = np.array([a["sigma"] for a in ep.ASSETS.values()])
        expected = math.sqrt((w ** 2) @ (sigmas ** 2))
        assert sigma == pytest.approx(expected)

    def test_deterministic(self):
        w = np.array([0.4, 0.4, 0.2])
        a = ep.portfolio_distribution(w)
        b = ep.portfolio_distribution(w)
        assert a == b


# ============================================================================
# compute_var / compute_cvar : formules + invariant CVaR >= VaR.
# ============================================================================

class TestVarCvar:
    def test_var_formula(self):
        """VaR = -(mu - z*sigma), recalcule independamment."""
        for mu, sigma in [(0.03, 0.02), (0.08, 0.15), (0.0, 0.10), (-0.02, 0.05)]:
            expected = -(mu - ep.Z * sigma)
            assert ep.compute_var(mu, sigma) == pytest.approx(expected)

    def test_cvar_formula(self):
        for mu, sigma in [(0.03, 0.02), (0.08, 0.15), (0.0, 0.10)]:
            expected = -(mu - sigma * ep.PHI_Z / (1 - ep.CONFIDENCE))
            assert ep.compute_cvar(mu, sigma) == pytest.approx(expected)

    def test_var_actions_hand_value(self):
        """100% Actions : VaR_95 ~= 16.67% (perte probable)."""
        mu, sigma = ep.portfolio_distribution(np.array([0.0, 1.0, 0.0]))
        assert ep.compute_var(mu, sigma) == pytest.approx(0.1667, abs=1e-3)

    def test_cvar_actions_hand_value(self):
        """100% Actions : CVaR_95 ~= 22.94% (perte moyenne au-dela de VaR)."""
        mu, sigma = ep.portfolio_distribution(np.array([0.0, 1.0, 0.0]))
        assert ep.compute_cvar(mu, sigma) == pytest.approx(0.2294, abs=1e-3)

    @pytest.mark.parametrize("w", [
        [1.0, 0.0, 0.0], [0.0, 1.0, 0.0], [0.0, 0.0, 1.0],
        [0.5, 0.5, 0.0], [1 / 3, 1 / 3, 1 / 3], [0.6, 0.2, 0.2],
        [0.2, 0.3, 0.5], [0.5, 0.0, 0.5],
    ])
    def test_cvar_dominates_var(self, w):
        """INVARIANT : CVaR_95 >= VaR_95 pour tout portefeuille (sigma > 0).

        La perte moyenne conditionnee au-dela du quantile 95% ne peut pas etre
        inferieure au quantile lui-meme. C'est un theoreme de la theorie du risque.
        """
        mu, sigma = ep.portfolio_distribution(np.array(w))
        var = ep.compute_var(mu, sigma)
        cvar = ep.compute_cvar(mu, sigma)
        assert cvar >= var - 1e-12

    def test_cvar_var_gap_positive_and_proportional_to_sigma(self):
        """CVaR - VaR = sigma * (phi(z)/(1-alpha) - z), et le facteur est > 0."""
        factor = ep.PHI_Z / (1 - ep.CONFIDENCE) - ep.Z
        assert factor > 0  # ~0.418
        for sigma in [0.02, 0.08, 0.15]:
            gap = ep.compute_cvar(0.0, sigma) - ep.compute_var(0.0, sigma)
            assert gap == pytest.approx(sigma * factor)


# ============================================================================
# analyse_portfolio : dict complet + drapeau ok + assertion somme = 1.
# ============================================================================

class TestAnalysePortfolio:
    def test_returns_all_keys(self):
        r = ep.analyse_portfolio(np.array([0.4, 0.4, 0.2]), "test")
        for key in ["label", "w_oblig", "w_act", "w_immo", "mu_p",
                    "sigma_p", "VaR_95", "CVaR_95", "ok"]:
            assert key in r

    def test_weights_stored(self):
        r = ep.analyse_portfolio(np.array([0.5, 0.3, 0.2]), "lbl")
        assert r["w_oblig"] == pytest.approx(0.5)
        assert r["w_act"] == pytest.approx(0.3)
        assert r["w_immo"] == pytest.approx(0.2)
        assert r["label"] == "lbl"

    def test_ok_flag_matches_constraint(self):
        """ok = (CVaR_95 < 5%)."""
        for w in ep.PRESETS:
            r = ep.analyse_portfolio(np.array(w[1]), w[0])
            assert r["ok"] == (r["CVaR_95"] < ep.CVAR_CONSTRAINT)

    def test_actions_not_ok(self):
        """100% Actions : CVaR ~22.9% >> 5% -> ok=False.

        (ok est un numpy.bool_ car issu de cvar < threshold ; on test la
        faussete via `not`, pas `is False`.)"""
        r = ep.analyse_portfolio(np.array([0.0, 1.0, 0.0]), "100% Act")
        assert not r["ok"]
        assert r["CVaR_95"] > ep.CVAR_CONSTRAINT

    def test_obligataire_ok(self):
        """100% Obligataire : CVaR ~1.1% < 5% -> ok=True."""
        r = ep.analyse_portfolio(np.array([1.0, 0.0, 0.0]), "100% Oblig")
        assert r["ok"]
        assert r["CVaR_95"] < ep.CVAR_CONSTRAINT

    def test_asserts_weights_sum_to_one(self):
        with pytest.raises(AssertionError):
            ep.analyse_portfolio(np.array([0.5, 0.4, 0.2]), "bad")  # somme 1.1

    def test_metrics_consistent_with_distribution(self):
        w = np.array([0.4, 0.4, 0.2])
        mu, sigma = ep.portfolio_distribution(w)
        r = ep.analyse_portfolio(w, "")
        assert r["mu_p"] == pytest.approx(mu)
        assert r["sigma_p"] == pytest.approx(sigma)
        assert r["VaR_95"] == pytest.approx(ep.compute_var(mu, sigma))
        assert r["CVaR_95"] == pytest.approx(ep.compute_cvar(mu, sigma))


# ============================================================================
# Diversification : sous independance, sigma_p <= moyenne ponderee des sigmas.
# ============================================================================

class TestDiversification:
    def test_mix_less_risky_than_weighted_avg(self):
        """Un portefeuille 50/50 Oblig/Actions a un sigma < (0.02+0.15)/2.

        C'est l'effet de diversification : la variance est sous-additive sous
        l'hypothese d'independance (inegalite L2 <= L1)."""
        mu, sigma = ep.portfolio_distribution(np.array([0.5, 0.5, 0.0]))
        assert sigma < (0.02 + 0.15) / 2

    @pytest.mark.parametrize("w", [
        [0.5, 0.5, 0.0], [1 / 3, 1 / 3, 1 / 3], [0.6, 0.2, 0.2],
        [0.2, 0.4, 0.4], [0.5, 0.0, 0.5],
    ])
    def test_sigma_subadditive(self, w):
        """Pour tout portefeuille long-only : sigma_p <= sum(w_i * sigma_i)."""
        w = np.array(w)
        _, sigma_p = ep.portfolio_distribution(w)
        sigmas = np.array([a["sigma"] for a in ep.ASSETS.values()])
        weighted_avg = w @ sigmas
        assert sigma_p <= weighted_avg + 1e-12

    def test_no_diversification_single_asset(self):
        """Cas d'egalite : 100% un actif -> sigma_p == sigma de l'actif."""
        _, sigma = ep.portfolio_distribution(np.array([0.0, 1.0, 0.0]))
        assert sigma == pytest.approx(0.15)  # == weighted_avg (w=[0,1,0])


# ============================================================================
# PRESETS : 7 allocations valides.
# ============================================================================

class TestPresets:
    def test_seven_presets(self):
        assert len(ep.PRESETS) == 7

    def test_all_presets_valid_weights(self):
        for label, w in ep.PRESETS:
            assert abs(sum(w) - 1.0) < 1e-9
            assert all(x >= -1e-9 for x in w)
            assert isinstance(label, str) and label

    def test_all_presets_analysable(self):
        for label, w in ep.PRESETS:
            r = ep.analyse_portfolio(np.array(w), label)
            assert r is not None


# ============================================================================
# optimize_portfolio : realisabilite, bat le baseline, determinisme.
# ============================================================================

class TestOptimizePortfolio:
    def test_returns_feasible_solution(self):
        """L'optimum est realisable : CVaR <= 5% (a la tolerance SLSQP pres).

        Note : l'optimiseur pousse le rendement jusqu'a ce que la contrainte
        CVaR soit ACTIVE (CVaR ~= 5% a la frontiere). Le drapeau strict `ok`
        (cvar < 0.05) vaut donc souvent False a l'optimum — la realisabilite
        se verifie via CVaR <= contrainte, pas via le drapeau strict."""
        opt = ep.optimize_portfolio()
        assert opt["CVaR_95"] <= ep.CVAR_CONSTRAINT + 1e-4
        assert opt["CVaR_95"] >= ep.CVAR_CONSTRAINT - 5e-3  # contrainte active (frontiere)

    def test_weights_long_only_and_sum_to_one(self):
        opt = ep.optimize_portfolio()
        w = np.array([opt["w_oblig"], opt["w_act"], opt["w_immo"]])
        assert all(x >= -1e-6 for x in w)
        assert w.sum() == pytest.approx(1.0, abs=1e-6)

    def test_beats_bond_baseline(self):
        """L'optimum (max rendement s.c. CVaR<=5%) bat le 100% Obligataire
        (qui est realisable avec CVaR ~1.1% < 5%, mu=3%)."""
        opt = ep.optimize_portfolio()
        assert opt["mu_p"] >= 0.03 - 1e-6

    def test_deterministic(self):
        """SLSQP multi-start deterministe : 2 appels -> meme mu_p."""
        a = ep.optimize_portfolio()
        b = ep.optimize_portfolio()
        assert a["mu_p"] == pytest.approx(b["mu_p"])


# ============================================================================
# grid_search : solution admissible sur la grille, determinisme, monotonie.
# ============================================================================

class TestGridSearch:
    def test_returns_admissible(self):
        best = ep.grid_search(step=0.05)
        assert best is not None
        assert best["ok"]  # numpy.bool_ truthy (grille discrete -> point interieur strict)
        assert best["CVaR_95"] < ep.CVAR_CONSTRAINT

    def test_weights_on_grid(self):
        """Les poids sont des multiples du pas (0.05)."""
        best = ep.grid_search(step=0.05)
        for w in [best["w_oblig"], best["w_act"], best["w_immo"]]:
            assert abs(w / 0.05 - round(w / 0.05)) < 1e-6

    def test_deterministic(self):
        a = ep.grid_search(step=0.05)
        b = ep.grid_search(step=0.05)
        assert a["mu_p"] == b["mu_p"]

    def test_finer_grid_at_least_as_good(self):
        """Grille fine (pas 0.02) >= grille grossiere (pas 0.05) en rendement."""
        coarse = ep.grid_search(step=0.05)
        fine = ep.grid_search(step=0.02)
        assert fine["mu_p"] >= coarse["mu_p"] - 1e-9

    def test_grid_le_optimum(self):
        """La grille (discerte) ne bat pas l'optimum continu SLSQP."""
        grid_best = ep.grid_search(step=0.05)
        opt = ep.optimize_portfolio()
        assert grid_best["mu_p"] <= opt["mu_p"] + 1e-6
