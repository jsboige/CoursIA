# -*- coding: utf-8 -*-
"""Tests pour le module examples/stackelberg_leader_follower.py.

Module companion du notebook GameTheory-13-DifferentialGames.ipynb : duopole
a la Stackelberg (leader/follower en quantites) compare au duopole a la Cournot.

Modele (demande lineaire P = a - Q, cout marginal constant c) :
  - cournot_reaction_curve(rival_q)    : meilleure reponse q_i = (a - c - q_j) / 2
  - cournot_equilibrium(a, c)          : q* = (a - c) / 3 (symetrique)
  - stackelberg_equilibrium(a, c_L, c_F) : q_L = (a - 2 c_L + c_F) / 2,
                                            q_F = reaction curve (a - c_F - q_L) / 2
                                            (closed form (a + 2 c_L - 3 c_F) / 4)
  - calculate_profits(q1, q2, a, c1, c2) : pi_i = (a - q1 - q2 - c_i) * q_i

Les tests assertent des INVARIANTS (forme close + proprietes economiques),
pas seulement l'absence de crash :
  - **Forme close** : valeurs exactes pour (a=100, c=10) — Cournot (30, 30),
    Stackelberg (45, 22.5), reaction(0)=45 (monopole), profits (30,30)->900.
  - **Cournot = Nash** : la reaction a la quantite de Cournot est Cournot lui-meme
    (point fixe / meilleure reponse mutuelle).
  - **Avantage du premier mover** : le leader Stackelberg produit ET gagne plus
    qu'en Cournot ; le suiveur produit moins et gagne moins.
  - **Bien-etre** : Stackelberg > Cournot en quantite totale -> prix plus bas
    (surplus consommateur plus eleve).
  - **Couts asymetriques** : cout plus bas -> quantite plus haute (leader ou
    suiveur). Clamp a 0 quand la forme close sort negatif.
"""

import sys
from pathlib import Path

import numpy as np
import pytest

sys.path.insert(0, str(Path(__file__).parent.parent))

from examples.stackelberg_leader_follower import (  # noqa: E402
    calculate_profits,
    compare_equilibria,
    cournot_equilibrium,
    cournot_reaction_curve,
    plot_equilibria,
    stackelberg_equilibrium,
)


# ── cournot_reaction_curve ──────────────────────────────────────────────────


class TestCournotReactionCurve:
    """Meilleure reponse en concurrence de Cournot : (a - c - q_rival) / 2."""

    def test_monopoly_output_when_rival_zero(self):
        # Rival = 0 -> meilleure reponse = sortie de monopole (a-c)/2 = 45.
        assert cournot_reaction_curve(0, 100, 10) == 45.0

    def test_cournot_fixed_point(self):
        # La meilleure reponse a la quantite de Cournot (30) est Cournot (30).
        assert cournot_reaction_curve(30, 100, 10) == 30.0

    def test_reaction_decreases_with_rival_quantity(self):
        # Courbe de reaction decroissante (substitutes strategiques).
        qs = [cournot_reaction_curve(q, 100, 10) for q in (0, 20, 40, 60)]
        assert qs == sorted(qs, reverse=True)

    def test_clamp_at_zero_boundary(self):
        # rival_q = a - c (90) -> (90-90)/2 = 0 exactement a la frontiere.
        assert cournot_reaction_curve(90, 100, 10) == 0.0

    def test_clamp_at_zero_beyond_boundary(self):
        # rival_q > a - c -> reponse negative tronquee a 0.
        assert cournot_reaction_curve(100, 100, 10) == 0.0
        assert cournot_reaction_curve(150, 100, 10) == 0.0

    def test_custom_params(self):
        # a=120, c=20, rival=10 -> (120-20-10)/2 = 45.
        assert cournot_reaction_curve(10, 120, 20) == 45.0

    def test_returns_float(self):
        assert isinstance(cournot_reaction_curve(0, 100, 10), float)


# ── cournot_equilibrium ─────────────────────────────────────────────────────


class TestCournotEquilibrium:
    """Equilibre de Cournot-Nash symetrique : q* = (a - c) / 3."""

    def test_default_values(self):
        assert cournot_equilibrium(100, 10) == (30.0, 30.0)

    def test_symmetric(self):
        q1, q2 = cournot_equilibrium(100, 10)
        assert q1 == q2

    def test_custom_params(self):
        # a=120, c=0 -> q* = 40 chacun.
        assert cournot_equilibrium(120, 0) == (40.0, 40.0)

    def test_is_mutual_best_response(self):
        # Cournot est un Nash : chaque firme best-repond a l'autre.
        a, c = 100, 10
        q1, q2 = cournot_equilibrium(a, c)
        assert cournot_reaction_curve(q2, a, c) == pytest.approx(q1)
        assert cournot_reaction_curve(q1, a, c) == pytest.approx(q2)

    def test_higher_demand_higher_quantity(self):
        # Intercept de demande plus eleve -> quantites d'equilibre plus hautes.
        assert cournot_equilibrium(150, 10)[0] > cournot_equilibrium(100, 10)[0]

    def test_higher_cost_lower_quantity(self):
        # Cout marginal plus eleve -> quantites plus basses.
        assert cournot_equilibrium(100, 30)[0] < cournot_equilibrium(100, 10)[0]


# ── stackelberg_equilibrium ─────────────────────────────────────────────────


class TestStackelbergEquilibrium:
    """Equilibre de Stackelberg : leader anticipe la reaction du suiveur."""

    def test_symmetric_costs(self):
        assert stackelberg_equilibrium(100, 10, 10) == (45.0, 22.5)

    def test_leader_produces_more_than_follower(self):
        # Avantage de quantite du premier mover (couts egaux).
        q_L, q_F = stackelberg_equilibrium(100, 10, 10)
        assert q_L > q_F

    def test_leader_lower_cost_produces_more(self):
        # Leader avec cout inferieur -> q_L plus haute qu'en symetrique (45).
        q_L, _ = stackelberg_equilibrium(100, 5, 15)
        assert q_L == 52.5
        assert q_L > 45.0

    def test_follower_higher_cost_produces_less(self):
        # Suiveur avec cout superieur -> q_F plus basse qu'en symetrique (22.5).
        # Invariant de direction : la forme close follower est correcte post-#7385
        # (voir test_asymmetric_follower_equals_reaction_curve pour l'invariant
        # exact, et tests/test_stackelberg_asymmetric.py pour la couverture
        # parametree sur 5 paires asymetriques).
        _, q_F = stackelberg_equilibrium(100, 5, 15)
        assert q_F < 22.5

    def test_asymmetric_follower_equals_reaction_curve(self):
        """Le suiveur doit best-responder a la quantite du leader.

        Par definition de Stackelberg, q_F = (a - c_F - q_L) / 2 (courbe de
        reaction de Cournot evaluee au q_L d'equilibre). Le module courant
        utilise (a + c_L - 2 c_F) / 4, egale a la courbe de reaction seulement
        quand c_L == c_F ; corrige dans #7385. Avec (100, 5, 15) : q_L = 52.5
        (leader, deja correct), q_F vraie = 16.25, q_F buggy = 18.75.
        """
        a, c_L, c_F = 100, 5, 15
        q_L, q_F = stackelberg_equilibrium(a, c_L, c_F)
        assert q_L == 52.5  # leader unaffected by the follower-formula bug
        assert q_F == (a - c_F - q_L) / 2  # = 16.25, the reaction curve

    def test_leader_clamp_to_zero(self):
        # c_L si eleve que la forme close sort negative -> clamp a 0.
        # a=100, c_L=200, c_F=10 -> (100-400+10)/2 = -145 -> 0.
        q_L, _ = stackelberg_equilibrium(100, 200, 10)
        assert q_L == 0.0

    def test_returns_tuple_of_floats(self):
        q_L, q_F = stackelberg_equilibrium(100, 10, 10)
        assert isinstance(q_L, float) and isinstance(q_F, float)


# ── calculate_profits ───────────────────────────────────────────────────────


class TestCalculateProfits:
    """Profit de chaque firme : pi_i = (P - c_i) * q_i avec P = a - q1 - q2."""

    def test_cournot_profits(self):
        # price = 100-60 = 40, profit = (40-10)*30 = 900 chacun.
        assert calculate_profits(30, 30, 100, 10, 10) == (900.0, 900.0)

    def test_stackelberg_profits(self):
        # price = 100-67.5 = 32.5, profit_L = 22.5*45 = 1012.5,
        # profit_F = 22.5*22.5 = 506.25.
        assert calculate_profits(45, 22.5, 100, 10, 10) == (1012.5, 506.25)

    def test_negative_profit_below_cost(self):
        # Quantites si hautes que price = 0 < c -> pertes.
        # price = 100-100 = 0, profit = (0-10)*50 = -500.
        assert calculate_profits(50, 50, 100, 10, 10) == (-500.0, -500.0)

    def test_asymmetric_costs(self):
        # Firmes aux couts differents -> profits differents a quantites egales.
        p1, p2 = calculate_profits(30, 30, 100, 10, 20)
        assert p1 > p2  # cout plus bas -> profit plus haut

    def test_monopoly_profit(self):
        # Une seule firme produit -> profit de monopole.
        # price = 100-45 = 55, profit = (55-10)*45 = 2025.
        p1, p2 = calculate_profits(45, 0, 100, 10, 10)
        assert p1 == 2025.0
        assert p2 == 0.0


# ── Invariants economiques (integration Cournot vs Stackelberg) ──────────────


class TestEconomicInvariants:
    """Proprietes economiques comparant Cournot et Stackelberg."""

    def test_first_mover_advantage_profit(self):
        # Le leader Stackelberg gagne plus qu'en Cournot.
        a, c = 100, 10
        _, pi_cournot = calculate_profits(*cournot_equilibrium(a, c), a, c, c)
        q_L, q_F = stackelberg_equilibrium(a, c, c)
        pi_leader, _ = calculate_profits(q_L, q_F, a, c, c)
        assert pi_leader > pi_cournot  # 1012.5 > 900

    def test_follower_disadvantage_profit(self):
        # Le suiveur Stackelberg gagne moins qu'en Cournot.
        a, c = 100, 10
        _, pi_cournot = calculate_profits(*cournot_equilibrium(a, c), a, c, c)
        q_L, q_F = stackelberg_equilibrium(a, c, c)
        _, pi_follower = calculate_profits(q_L, q_F, a, c, c)
        assert pi_follower < pi_cournot  # 506.25 < 900

    def test_stackelberg_more_total_output(self):
        # Stackelberg > Cournot en quantite totale -> meilleurs pour les consommateurs.
        a, c = 100, 10
        q_c = sum(cournot_equilibrium(a, c))
        q_s = sum(stackelberg_equilibrium(a, c, c))
        assert q_s > q_c  # 67.5 > 60

    def test_stackelberg_lower_price(self):
        # Output total plus haut -> prix plus bas (demande decroissante).
        a, c = 100, 10
        Q_c = sum(cournot_equilibrium(a, c))
        Q_s = sum(stackelberg_equilibrium(a, c, c))
        assert (a - Q_s) < (a - Q_c)  # prix Stackelberg < prix Cournot

    def test_monopoly_output_on_reaction_curve(self):
        # Rival = 0 -> meilleure reponse = sortie de monopole (a-c)/2.
        # Et le monopole produit bien (a-c)/2 (max de (a-q-c)q -> q=(a-c)/2).
        a, c = 100, 10
        assert cournot_reaction_curve(0, a, c) == (a - c) / 2

    def test_cournot_between_monopoly_and_stackelberg(self):
        # Output total : monopole (45) < Cournot (60) < Stackelberg (67.5).
        a, c = 100, 10
        q_mono = cournot_reaction_curve(0, a, c)  # monopole unilateral
        q_cournot = sum(cournot_equilibrium(a, c))
        q_stackelberg = sum(stackelberg_equilibrium(a, c, c))
        assert q_mono < q_cournot < q_stackelberg


# ── Smoke : compare_equilibria + plot_equilibria ────────────────────────────


class TestSmokeCompareAndPlot:
    """compare_equilibria (stdout) et plot_equilibria (PNG) ne crashent pas."""

    def test_compare_equilibria_prints(self, capsys):
        compare_equilibria()
        out = capsys.readouterr().out
        assert "Cournot" in out
        assert "Stackelberg" in out
        assert "Leader advantage" in out

    def test_plot_equilibria_creates_png(self, tmp_path, monkeypatch):
        # plot_equilibria ecrit 'stackelberg_equilibrium.png' dans le cwd.
        monkeypatch.chdir(tmp_path)
        plot_equilibria()
        assert (tmp_path / "stackelberg_equilibrium.png").is_file()
