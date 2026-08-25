"""Tests unitaires pour ``ict.cemi_field`` (case 7, #8182 iceberg L4).

Pins des prédictions pré-enregistrées (dissociations-matrix.md, case 7 —
fenêtre de synchronie, McFadden CEMI), mesurées le 2026-08-24 :

  1. (P1) R_E décroît **monotone** de f_sync=1 vers f_sync=0, avec
     R_E(1.0) >> 100 (mesuré 581) : le tir synchrone intègre le champ.
  2. (P2) au crossover f* = 1/sqrt(N), R_E tombe dans la bande
     **[1.2, 3.0]** (mesuré 1.86 +- 0.62, 5 seeds ; bande recalibrée
     sur 40 seeds : mean 1.55, IQR [1.02, 1.90]).
  3. (P3) sous f*/2, R_E < 1.2 (mesuré 1.15 à f*/2, 1.02 à f*/4) :
     le groupe synchrone est indiscernable du bruit incohérent.
  4. (CTRL) doubler la puissance en asynchrone : ×4 exact contre base
     ×1 (trivial), ratio 1.0 exact contre base même-puissance — l'effet
     CEMI du jouet est structurel, pas énergétique.
  5. (Sanity) f* théorique = 1/sqrt(N) ; la fraction synchronisée
     mesurée suit la fraction demandée ; déterminisme seed.
"""

from __future__ import annotations

import numpy as np
import pytest

from ict.cemi_field import (
    DipoleField,
    coherence_energy_ratio,
    negative_control_power,
    sync_window_sweep,
)

N_SIDE = 32
N_EMITTERS = N_SIDE * N_SIDE  # 1024
F_STAR = 1.0 / np.sqrt(N_EMITTERS)  # ~0.03125


@pytest.fixture(scope="module")
def sweep() -> list[dict]:
    """Balayage standard (5 seeds) — déterministe, partagé entre gates."""
    return sync_window_sweep(n_side=N_SIDE)


class TestP1Monotone:
    def test_decroissance_stricte(self, sweep):
        means = [row["R_E_mean"] for row in sweep]
        for hi, lo in zip(means, means[1:]):
            assert hi > lo, (
                f"P1 rompu : R_E non monotone ({[round(m, 3) for m in means]})"
            )

    def test_full_sync_amplification(self, sweep):
        full = sweep[0]
        assert full["f_sync"] == 1.0
        assert full["R_E_mean"] > 100.0, (
            f"R_E(f=1) = {full['R_E_mean']:.1f} — attendu >> 100 (mesuré 581)"
        )

    def test_async_floor(self, sweep):
        floor = sweep[-1]
        assert floor["f_sync"] == 0.0
        assert abs(floor["R_E_mean"] - 1.0) < 1e-9


class TestP2Crossover:
    def test_R_E_dans_la_bande(self, sweep):
        at_fstar = next(r for r in sweep if abs(r["f_sync"] - F_STAR) < 1e-12)
        assert 1.2 <= at_fstar["R_E_mean"] <= 3.0, (
            f"R_E @f* = {at_fstar['R_E_mean']:.3f} hors bande [1.2, 3.0]"
        )

    def test_f_star_porte_par_le_sweep(self, sweep):
        assert any(abs(r["f_star"] - F_STAR) < 1e-12 for r in sweep)
        assert any(abs(r["f_sync"] - F_STAR) < 1e-12 for r in sweep)


class TestP3UnderCrossover:
    def test_sous_f_star_sur_deux(self, sweep):
        half = next(r for r in sweep if abs(r["f_sync"] - 0.5 * F_STAR) < 1e-12)
        assert half["R_E_mean"] < 1.2, (
            f"R_E (f*/2) = {half['R_E_mean']:.3f} — attendu < 1.2"
        )

    def test_sous_f_star_sur_quatre(self, sweep):
        quarter = next(r for r in sweep if abs(r["f_sync"] - 0.25 * F_STAR) < 1e-12)
        assert quarter["R_E_mean"] < 1.2, (
            f"R_E (f*/4) = {quarter['R_E_mean']:.3f} — attendu < 1.2"
        )


class TestControleNegatif:
    def test_effet_structurel_pas_energetique(self):
        ctrl = negative_control_power(n_side=N_SIDE, power_gain=2.0, seed=0)
        # volet trivial : l'énergie monte comme le carré de l'amplitude (exact,
        # mêmes phases => même somme complexe, amplitude doublée)
        assert ctrl["R_E_async_boost_vs_base1"] == pytest.approx(4.0, abs=1e-9)
        # volet décisif : à structure de phase égale (asynchrone), doubler la
        # puissance ne déplace pas le ratio cohérent/incohérent (exact : les
        # deux champs de coherence_energy_ratio sont bit-identiques)
        assert ctrl["R_E_async_boost_vs_same_power"] == pytest.approx(1.0, abs=1e-9)


class TestSanity:
    def test_f_star_theorique(self):
        res = coherence_energy_ratio(n_side=N_SIDE, f_sync=1.0, seed=0)
        assert res["n_emitters"] == N_EMITTERS
        assert res["f_star_theoretical"] == pytest.approx(F_STAR)

    def test_fraction_synchronisee_mesuree(self):
        res = coherence_energy_ratio(n_side=N_SIDE, f_sync=1.0, seed=0)
        assert res["f_sync_measured"] == pytest.approx(1.0)
        half = coherence_energy_ratio(n_side=N_SIDE, f_sync=0.5, seed=0)
        assert abs(half["f_sync_measured"] - 0.5) < 0.05  # binomial, N=1024

    def test_determinisme_seed(self):
        a = coherence_energy_ratio(n_side=N_SIDE, f_sync=0.5, seed=3)
        b = coherence_energy_ratio(n_side=N_SIDE, f_sync=0.5, seed=3)
        assert a["R_E"] == b["R_E"]

    def test_f_sync_hors_domaine_rejete(self):
        with pytest.raises(ValueError):
            DipoleField(n_side=8, f_sync=1.5)
