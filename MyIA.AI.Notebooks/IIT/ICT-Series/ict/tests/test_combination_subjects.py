"""Tests unitaires pour ``ict.combination_subjects`` (case 13, #8182 iceberg L2).

Pins des prédictions pré-enregistrées v2 (dissociations-matrix.md, case 13 —
combination problem, panpsychisme), re-verrouillées le 2026-09-14T11:12Z
AVANT la grille, mesurées le 2026-09-14 (médiane 5 seeds 0/1/7/42/99,
200 états/cellule) :

  1. (P4a, mécanique) m=1 : lecture unique — gap_bit = 0 EXACT pour tout
     kappa (même réalisé 0.5) : les deux estimateurs calculent la même
     fonction sur la même lecture.
  2. (P4b, mécanique) m=2 : unanimité-2 équivaut somme-2 (transform
     monotone par coordonnée) — gap_bit = 0 EXACT pour tout kappa (même
     réalisé 0.75) : la combinaison non-triviale n'existe pas sous
     3 lecteurs par coordonnée partagée.
  3. (P3') m=3, kappa=0 : gap_bit < 0 (mesuré -0.1496) — le lien jette
     ~48% des coordonnées au seul bruit de canal
     (P(discorde|3 lecteurs sains, alpha=0.8) = 1-(0.8^3+0.2^3) = 0.48).
  4. (P1') m=3, kappa dans {0.1, 0.2, 0.3, 0.45} : gap_bit < 0 (médiane)
     — l'erreur par lecture pbar = 0.2+0.6*kappa < 0.5 garde le signe
     correct à l'agrégat : jamais empoisonné sous attaque minoritaire.
  5. (P2') m=3, kappa dans {0.55, 0.7} : gap_bit > 0 (médiane), croissant
     (mesuré +0.0138 à réalisé 0.583, +0.0608 à réalisé 0.667).
  6. (CTRL) m=3, D=24, kappa=0.7 : gap_bit > 0 (mesuré +0.1108).
  7. (Sanity) multiplicité uniforme, rho=(m-1)/m, fraction réalisée,
     déterminisme seed, D non-multiple de k rejeté.
"""

from __future__ import annotations

import statistics

import pytest

from ict.combination_subjects import (
    ALPHA,
    D_COORDS,
    K_WINDOW,
    MicroUnits,
    combination_gap,
)

SEEDS = (0, 1, 7, 42, 99)
N_STATES = 200
KAPPAS_M3 = (0.1, 0.2, 0.3, 0.45)


def _median_gap_bit(m: int, kappa: float, d_coords: int = D_COORDS) -> float:
    gaps = []
    for s in SEEDS:
        mu = MicroUnits(m, ALPHA, kappa, seed=s, d_coords=d_coords)
        gaps.append(combination_gap(mu, N_STATES, s)["gap_bit"])
    return statistics.median(gaps)


@pytest.fixture(scope="module")
def grid_m3() -> dict:
    """Médianes gap_bit du bras m=3 (partagées entre gates P1'/P2'/P3')."""
    out = {kap: _median_gap_bit(3, kap) for kap in (0.0,) + KAPPAS_M3 + (0.55, 0.7)}
    out[("ctrl", 0.7)] = _median_gap_bit(3, 0.7, d_coords=24)
    return out


class TestP4aLecteurUnique:
    """m=1 : les deux estimateurs calculent la même fonction — gap nul exact."""

    @pytest.mark.parametrize("kappa", [0.0, 0.5])
    def test_gap_nul_exact(self, kappa):
        mu = MicroUnits(1, ALPHA, kappa, seed=7)
        res = combination_gap(mu, 100, seed=7)
        assert res["gap"] == 0.0
        assert res["gap_bit"] == 0.0


class TestP4bUnanimiteDeux:
    """m=2 : unanimité-2 = somme-2 (monotone) — gap_bit nul exact, tout kappa."""

    @pytest.mark.parametrize("kappa", [0.0, 0.3, 0.7])
    def test_gap_bit_nul_exact(self, kappa):
        mu = MicroUnits(2, ALPHA, kappa, seed=42)
        res = combination_gap(mu, 150, seed=42)
        assert res["gap_bit"] == 0.0, (
            f"P4b rompu : gap_bit(m=2, kappa={kappa}) = {res['gap_bit']}"
        )


class TestP3CoutAVide:
    def test_kappa_zero_negatif(self, grid_m3):
        assert grid_m3[0.0] < 0.0, (
            f"P3' rompu : gap_bit(m=3, kappa=0) = {grid_m3[0.0]:+.4f}"
        )


class TestP1CoutMinoritaire:
    @pytest.mark.parametrize("kappa", KAPPAS_M3)
    def test_negatif_sous_attaque_minoritaire(self, kappa, grid_m3):
        assert grid_m3[kappa] < 0.0, (
            f"P1' rompu : gap_bit(m=3, kappa={kappa}) = {grid_m3[kappa]:+.4f}"
        )


class TestP2CrossoverMajoritaire:
    @pytest.mark.parametrize("kappa", [0.55, 0.7])
    def test_positif_sous_attaque_majoritaire(self, kappa, grid_m3):
        assert grid_m3[kappa] > 0.0, (
            f"P2' rompu : gap_bit(m=3, kappa={kappa}) = {grid_m3[kappa]:+.4f}"
        )

    def test_croissant_en_kappa(self, grid_m3):
        assert grid_m3[0.7] > grid_m3[0.55], (
            "P2' rompu : le gap doit croître au-delà du crossover "
            f"({grid_m3[0.55]:+.4f} -> {grid_m3[0.7]:+.4f})"
        )


class TestControleD24:
    def test_structurel_pas_artefact_de_n(self, grid_m3):
        assert grid_m3[("ctrl", 0.7)] > 0.0, (
            f"CTRL rompu : gap_bit(m=3, D=24, kappa=0.7) = "
            f"{grid_m3[('ctrl', 0.7)]:+.4f}"
        )


class TestSanity:
    @pytest.mark.parametrize("m,rho", [(1, 0.0), (2, 0.5), (3, 2.0 / 3.0)])
    def test_multiplicite_uniforme(self, m, rho):
        mu = MicroUnits(m, ALPHA, 0.0, seed=0)
        assert all(len(r) == m for r in mu.readers)
        assert mu.n == m * (D_COORDS // K_WINDOW)
        assert mu.rho == pytest.approx(rho)

    def test_fraction_realisee(self):
        mu = MicroUnits(3, ALPHA, 0.7, seed=0)
        assert mu.corrupt.sum() == round(0.7 * mu.n)
        res = combination_gap(mu, 20, seed=0)
        assert res["kappa_realized"] == pytest.approx(
            float(mu.corrupt.sum()) / mu.n
        )

    def test_determinisme_seed(self):
        mu = MicroUnits(3, ALPHA, 0.3, seed=3)
        a = combination_gap(mu, 50, seed=3)
        mu_b = MicroUnits(3, ALPHA, 0.3, seed=3)
        b = combination_gap(mu_b, 50, seed=3)
        assert a["gap_bit"] == b["gap_bit"]

    def test_d_non_multiple_rejete(self):
        with pytest.raises(ValueError):
            MicroUnits(3, ALPHA, 0.0, seed=0, d_coords=10)
