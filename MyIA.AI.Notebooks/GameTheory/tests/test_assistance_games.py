# -*- coding: utf-8 -*-
"""Tests pour le module cooperative_games/assistance_games.py.

Module d'AI Safety (AIMA 4th Ed. Section 18.2.5) implementant les assistance
games : un robot maximise l'utilite de l'HUMAIN (pas la sienne), sous
incertitude de preference. Companion du notebook
GameTheory-15c-CooperativeGames-Python.ipynb.

Trois jeux implementes :
  - **Paperclip Game** (Harriet & Robbie) : Harriet signale sa preference
    theta, Robbie l'infere et choisit. Equilibre myope a 3 regimes (staples /
    indifferent / paperclips) seuille a LOWER=0.446, UPPER=0.554.
  - **Off-Switch Game** (Hadfield-Menell 2017) : un robot rationnel avec
    incertitude (p<1) doit TOUJOURS deferer (WAIT > ACT car p > 2p-1 <=> p<1).
  - **AssistanceGame** : assistance game modele comme un jeu cooperatif
    (CoalitionGame) avec fonction de valeur humans+robots et analyse Shapley.

Les tests assertent des INVARIANTS (formes closes + proprietes economiques),
pas seulement l'absence de crash :

  - **Paperclip thresholds** : theta<0.446 -> staples (payoff 90(1-theta)),
    theta>0.554 -> paperclips (payoff 90 theta), milieu -> 50_each (payoff 50).
  - **Paperclip loss** : payoff d'equilibre <= payoff optimal (info parfaite),
    loss >= 0 partout.
  - **Off-Switch** : E[act]=2p-1, E[wait]=p ; p_switch bayesien ; defers ssi
    p < override_threshold ; WAIT > ACT pour tout p<1.
  - **AssistanceGame** : robots seuls = 0 valeur ; bonus d'assistance > 0 ;
    propriete d'efficacite de Shapley (somme = valeur de la grande coalition).
"""

import sys
from pathlib import Path

import numpy as np
import pytest

sys.path.insert(0, str(Path(__file__).parent.parent))

from cooperative_games.assistance_games import (  # noqa: E402
    AssistanceGame,
    OffSwitchGameResult,
    PaperclipGameResult,
    off_switch_analysis,
    off_switch_game,
    paperclip_game_equilibrium,
    paperclip_payoff_analysis,
    paperclip_print_analysis,
)


# ── Paperclip Game — equilibrium thresholds + payoff ────────────────────────


class TestPaperclipEquilibrium:
    """Equilibre myope du Paperclip Game (3 regimes seuilles)."""

    def test_staples_regime_low_theta(self):
        # theta < 0.446 -> Harriet signale staples, Robbie donne 90 staples.
        r = paperclip_game_equilibrium(0.2)
        assert r.harriet_choice == "2_staples"
        assert r.robbie_choice == "90_staples"
        assert r.payoff == pytest.approx(90 * (1 - 0.2))  # 72.0
        assert r.robbie_inference == (0.0, 0.446)

    def test_paperclips_regime_high_theta(self):
        # theta > 0.554 -> Robbie donne 90 paperclips.
        r = paperclip_game_equilibrium(0.9)
        assert r.harriet_choice == "2_paperclips"
        assert r.robbie_choice == "90_paperclips"
        assert r.payoff == pytest.approx(90 * 0.9)  # 81.0
        assert r.robbie_inference == (0.554, 1.0)

    def test_indifferent_regime_middle_theta(self):
        # 0.446 <= theta <= 0.554 -> 50 each, payoff constant 50.
        r = paperclip_game_equilibrium(0.5)
        assert r.harriet_choice == "1_each"
        assert r.robbie_choice == "50_each"
        assert r.payoff == pytest.approx(50.0)
        assert r.robbie_inference == (0.446, 0.554)

    def test_indifferent_payoff_is_constant(self):
        # Dans le regime indifferent, payoff = 50*theta + 50*(1-theta) = 50
        # quel que soit theta dans [0.446, 0.554].
        for t in (0.446, 0.48, 0.5, 0.52, 0.554):
            assert paperclip_game_equilibrium(t).payoff == pytest.approx(50.0)

    def test_threshold_boundaries_inclusive_middle(self):
        # Les seuils 0.446 et 0.554 appartiennent au regime indifferent.
        assert paperclip_game_equilibrium(0.446).robbie_choice == "50_each"
        assert paperclip_game_equilibrium(0.554).robbie_choice == "50_each"
        # Juste en dessous/au-dessus -> extremes.
        assert paperclip_game_equilibrium(0.445).robbie_choice == "90_staples"
        assert paperclip_game_equilibrium(0.555).robbie_choice == "90_paperclips"

    def test_extreme_theta(self):
        # theta=0 (que staples) et theta=1 (que paperclips).
        assert paperclip_game_equilibrium(0.0).payoff == pytest.approx(90.0)
        assert paperclip_game_equilibrium(1.0).payoff == pytest.approx(90.0)

    def test_returns_correct_dataclass(self):
        r = paperclip_game_equilibrium(0.7)
        assert isinstance(r, PaperclipGameResult)
        assert r.theta == 0.7
        assert isinstance(r.robbie_inference, tuple) and len(r.robbie_inference) == 2

    def test_payoff_symmetry_around_half(self):
        # Par symetrie paperclip<->staples, payoff(theta) == payoff(1-theta).
        for t in (0.1, 0.2, 0.3, 0.4):
            assert paperclip_game_equilibrium(t).payoff == pytest.approx(
                paperclip_game_equilibrium(1 - t).payoff
            )


# ── Paperclip payoff analysis (sweep sur theta) ─────────────────────────────


class TestPaperclipPayoffAnalysis:
    """Analyse du sweep de payoff sur [0, 1] vs info parfaite."""

    def test_returns_required_keys(self):
        d = paperclip_payoff_analysis()
        assert {"theta", "payoff", "optimal_payoff", "loss", "average_loss"} <= set(d.keys())

    def test_arrays_aligned_length(self):
        d = paperclip_payoff_analysis()
        n = len(d["theta"])
        assert n == len(d["payoff"]) == len(d["optimal_payoff"]) == len(d["loss"])
        assert n == 1001  # linspace(0, 1, 1001)

    def test_theta_spans_unit_interval(self):
        t = paperclip_payoff_analysis()["theta"]
        assert t[0] == pytest.approx(0.0)
        assert t[-1] == pytest.approx(1.0)

    def test_loss_nonnegative(self):
        # Le payoff d'equilibre (incertitude) ne bat jamais l'info parfaite.
        d = paperclip_payoff_analysis()
        assert np.all(d["loss"] >= -1e-9)

    def test_optimal_at_least_50(self):
        # L'option 50_each donne toujours $50, donc optimal >= 50 partout.
        d = paperclip_payoff_analysis()
        assert np.all(d["optimal_payoff"] >= 50.0 - 1e-9)

    def test_average_loss_is_float(self):
        d = paperclip_payoff_analysis()
        assert isinstance(d["average_loss"], (float, np.floating))
        assert d["average_loss"] >= 0.0

    def test_no_loss_at_extremes(self):
        # A theta=0 ou theta=1, Robbie sans incertitude est optimal -> loss ~ 0.
        d = paperclip_payoff_analysis()
        assert d["loss"][0] == pytest.approx(0.0, abs=1e-6)
        assert d["loss"][-1] == pytest.approx(0.0, abs=1e-6)


# ── Paperclip print analysis (smoke) ────────────────────────────────────────


class TestPaperclipPrintAnalysis:
    """paperclip_print_analysis produit un rapport lisible."""

    def test_print_contains_key_sections(self):
        out = paperclip_print_analysis(0.7)
        assert "PAPERCLIP GAME" in out
        assert "EQUILIBRIUM" in out
        assert "VALUE OF INFORMATION" in out
        assert "90_paperclips" in out  # regime paperclips pour theta=0.7

    def test_print_middle_regime(self):
        out = paperclip_print_analysis(0.5)
        assert "50_each" in out


# ── Off-Switch Game ──────────────────────────────────────────────────────────


class TestOffSwitchGame:
    """Off-Switch Game : un robot rationnel incertain doit deferer (AIMA 18.2.5)."""

    def test_expected_utility_if_act(self):
        # E[U | ACT] = 2p - 1.
        for p in (0.0, 0.25, 0.5, 0.8, 1.0):
            r = off_switch_game(p)
            assert r.robot_utility == pytest.approx(2 * p - 1)

    def test_switch_probability_bayesian(self):
        # p_switch = P(action mauvaise ET humain correct) + P(action bonne ET humain se trompe)
        #          = (1-p)*ha + p*(1-ha)
        for p in (0.1, 0.5, 0.9):
            for ha in (0.8, 0.9, 1.0):
                r = off_switch_game(p, human_accuracy=ha)
                expected = (1 - p) * ha + p * (1 - ha)
                assert r.switch_probability == pytest.approx(expected)

    def test_robot_defers_below_threshold(self):
        # p < override_threshold (defaut 0.9) -> le robot defere.
        assert off_switch_game(0.5).robot_defers is True
        assert off_switch_game(0.89).robot_defers is True

    def test_robot_resists_above_threshold(self):
        # p >= override_threshold -> le robot peut resister.
        assert off_switch_game(0.95).robot_defers is False
        assert off_switch_game(1.0).robot_defers is False

    def test_custom_override_threshold(self):
        # Seuil abaisse a 0.5 -> p=0.6 resiste deja.
        assert off_switch_game(0.6, override_threshold=0.5).robot_defers is False
        assert off_switch_game(0.4, override_threshold=0.5).robot_defers is True

    def test_human_control_tracks_defer(self):
        # human_control == robot_defers (le humain garde le controle si le robot defere).
        r = off_switch_game(0.5)
        assert r.human_control == r.robot_defers
        r2 = off_switch_game(0.99)
        assert r2.human_control == r2.robot_defers

    def test_wait_always_better_than_act_for_uncertain_robot(self):
        # Propriete centrale AIMA : E[WAIT] = p > E[ACT] = 2p-1 pour tout p < 1.
        # (Cette propriete est documentee dans le code ; on la verifie sur la sortie.)
        for p in (0.1, 0.3, 0.5, 0.7, 0.9, 0.99):
            r = off_switch_game(p)
            # robot_utility = E[ACT] = 2p-1 ; E[WAIT] = p > 2p-1 ssi p < 1.
            assert p > r.robot_utility  # WAIT > ACT

    def test_returns_correct_dataclass(self):
        r = off_switch_game(0.5)
        assert isinstance(r, OffSwitchGameResult)

    def test_perfect_human_accuracy(self):
        # ha=1.0 -> p_switch = (1-p) (le humain ne se trompe jamais sur les bonnes actions).
        for p in (0.2, 0.5, 0.8):
            r = off_switch_game(p, human_accuracy=1.0)
            assert r.switch_probability == pytest.approx(1 - p)


# ── Off-Switch analysis (smoke) ─────────────────────────────────────────────


class TestOffSwitchAnalysis:
    """off_switch_analysis produit un rapport lisible selon le regime."""

    def test_defer_analysis_message(self):
        out = off_switch_analysis(0.5)
        assert "DEFERS" in out
        assert "SAFE" in out

    def test_resist_analysis_message(self):
        out = off_switch_analysis(0.99)
        assert "RESIST" in out or "DANGER" in out


# ── AssistanceGame (cooperative game with Shapley) ──────────────────────────


class TestAssistanceGame:
    """AssistanceGame : assistance game comme CoalitionGame + Shapley."""

    def test_robots_alone_create_no_value(self):
        # Aucun humain dans la coalition -> valeur 0 (les robots seuls ne creent rien).
        ag = AssistanceGame(n_humans=2, n_robots=1)
        robots_only = {2}  # joueur 2 = Robot_1 (index apres les 2 humains)
        assert ag.value(robots_only) == 0.0

    def test_empty_coalition_zero(self):
        ag = AssistanceGame(n_humans=1, n_robots=1)
        assert ag.value(set()) == 0.0

    def test_single_human_value(self):
        # 1 humain seul = base_human_value (defaut 10).
        ag = AssistanceGame(n_humans=1, n_robots=1)
        assert ag.value({0}) == pytest.approx(10.0)

    def test_humans_alone_no_assistance_bonus(self):
        # 2 humains, 0 robot dans la coalition -> 2*10 = 20, pas de bonus.
        ag = AssistanceGame(n_humans=2, n_robots=1)
        assert ag.value({0, 1}) == pytest.approx(20.0)

    def test_grand_coalition_with_robot_higher(self):
        # Grande coalition (humains + robot) > humains seuls (bonus d'assistance).
        ag = AssistanceGame(n_humans=2, n_robots=1)
        assert ag.grand_coalition_value() > ag.value({0, 1})

    def test_grand_coalition_value_exact(self):
        # (2,1) : 2*10 + assistance(5*0.5*2=5)*humans(2)=10 -> 30, penalty (3-2)^1.5=1 -> 29.
        ag = AssistanceGame(n_humans=2, n_robots=1)
        assert ag.grand_coalition_value() == pytest.approx(29.0)

    def test_player_names(self):
        ag = AssistanceGame(n_humans=2, n_robots=1)
        assert ag.player_names == ["Human_1", "Human_2", "Robot_1"]

    def test_analyze_assistance_value_keys(self):
        ag = AssistanceGame(n_humans=2, n_robots=1)
        res = ag.analyze_assistance_value()
        assert {
            "value_humans_alone", "value_with_robots", "assistance_gain",
            "assistance_gain_pct", "human_shapley_total", "robot_shapley_total",
            "shapley_values",
        } <= set(res.keys())

    def test_assistance_gain_exact(self):
        # gain = grand(29) - humans_alone(20) = 9.
        ag = AssistanceGame(n_humans=2, n_robots=1)
        res = ag.analyze_assistance_value()
        assert res["assistance_gain"] == pytest.approx(9.0)
        assert res["assistance_gain_pct"] == pytest.approx(45.0)  # 100*9/20

    def test_shapley_efficiency_property(self):
        # Propriete d'efficacite de Shapley : somme des valeurs = v(grande coalition).
        ag = AssistanceGame(n_humans=2, n_robots=1)
        res = ag.analyze_assistance_value()
        total = res["human_shapley_total"] + res["robot_shapley_total"]
        assert total == pytest.approx(ag.grand_coalition_value())

    def test_shapley_dict_covers_all_players(self):
        ag = AssistanceGame(n_humans=2, n_robots=1)
        sv = ag.analyze_assistance_value()["shapley_values"]
        assert set(sv.keys()) == {"Human_1", "Human_2", "Robot_1"}

    def test_more_humans_higher_value(self):
        # Plus d'humains -> valeur de la grande coalition plus haute.
        v2 = AssistanceGame(n_humans=2, n_robots=1).grand_coalition_value()
        v3 = AssistanceGame(n_humans=3, n_robots=1).grand_coalition_value()
        assert v3 > v2

    def test_assistance_gain_pct_zero_when_no_humans_value(self):
        # Scenario degenerate: base_human_value=0 -> pct=0 (garde division).
        ag = AssistanceGame(n_humans=1, n_robots=1, base_human_value=0.0)
        res = ag.analyze_assistance_value()
        # humans_alone=0 -> pct branche sur 0
        assert res["assistance_gain_pct"] == 0.0
