# -*- coding: utf-8 -*-
"""Tests for examples/centipede_game.py.

The module had zero dedicated tests. Its deterministic functions
(centipede_payoffs, backward_induction) are pinned here against the
mathematical invariants of the centipede game, and the stochastic
simulate_experimental_play is pinned at its deterministic endpoints.

Per the pin-the-invariant-not-the-value lesson (fleet-wide after the
Stackelberg merge-hazard): assertions follow the payoff FORMULAS and the
textbook SPE structure, not literal arrays that could pin a latent bug.

Run with: pytest tests/test_centipede_game.py -v
"""

import sys
from pathlib import Path

import numpy as np
import pytest

sys.path.insert(0, str(Path(__file__).parent.parent))

from examples.centipede_game import (  # noqa: E402
    centipede_payoffs,
    backward_induction,
    simulate_experimental_play,
    print_game_tree,
)


# ----------------------------------------------------------------------------
# centipede_payoffs -- deterministic, follows the growth/bonus formulas.
# ----------------------------------------------------------------------------

class TestCentipedePayoffs:
    """centipede_payoffs follows pot*bonus (taker), pot/2 (other), pot *= growth."""

    def test_node_count(self):
        """n_rounds rounds -> 2*n_rounds Take-nodes + 1 final-cooperation node."""
        for n in (1, 2, 3, 5):
            p = centipede_payoffs(n)
            assert len(p) == 2 * n + 1

    def test_take_node_formulas(self):
        """At each Take-node i: taker = pot_i * bonus, other = pot_i / 2,
        with pot_i = growth^(2*i) (pot starts at 1, doubles per node *inside the loop*).

        The loop runs `round_num in range(n_rounds*2)` and grows pot AFTER each
        append, so node i's pot = growth**i.
        """
        growth, bonus = 2.0, 1.5
        p = centipede_payoffs(3, growth_rate=growth, defection_bonus=bonus)
        for i in range(6):  # 2*3 Take-nodes
            pot_i = growth ** i
            assert p[i] == pytest.approx((pot_i * bonus, pot_i / 2)), f"node {i}"

    def test_final_cooperation_is_equal_split(self):
        """The terminal (cooperation) node gives both players pot/2, equally."""
        growth = 2.0
        p = centipede_payoffs(3, growth_rate=growth)
        final = p[-1]
        assert final[0] == pytest.approx(final[1])
        # Final pot = growth^(2*n_rounds) (one more growth after the last loop iter).
        expected_pot = growth ** 6
        assert final[0] == pytest.approx(expected_pot / 2)

    def test_taker_always_beats_other_at_take_nodes(self):
        """Defection is individually lucrative: taker > other at every Take-node."""
        p = centipede_payoffs(4)
        for taker, other in p[:-1]:
            assert taker > other

    def test_pot_grows_monotonically(self):
        """The pot (hence taker payoff) grows strictly across Take-nodes."""
        p = centipede_payoffs(5)
        takers = [t for t, _ in p[:-1]]
        assert all(b > a for a, b in zip(takers, takers[1:]))

    def test_custom_parameters_propagate(self):
        """growth_rate and defection_bonus change the payoffs as documented."""
        p_default = centipede_payoffs(2)
        p_fast = centipede_payoffs(2, growth_rate=3.0)
        # Faster growth -> larger second-node taker payoff.
        assert p_fast[1][0] > p_default[1][0]
        p_bigbonus = centipede_payoffs(2, defection_bonus=2.0)
        # Bigger bonus -> larger first-node taker payoff (pot_0 = 1).
        assert p_bigbonus[0][0] == pytest.approx(2.0)

    def test_known_values_rounds_3(self):
        """Spot-check the canonical n_rounds=3 game (growth=2, bonus=1.5)."""
        p = centipede_payoffs(3)
        assert p[0] == pytest.approx((1.5, 0.5))
        assert p[1] == pytest.approx((3.0, 1.0))
        assert p[5] == pytest.approx((48.0, 16.0))
        assert p[-1] == pytest.approx((32.0, 32.0))


# ----------------------------------------------------------------------------
# backward_induction -- the centipede paradox: SPE is Take at node 0.
# ----------------------------------------------------------------------------

class TestBackwardInduction:
    """backward_induction yields the textbook centipede SPE: Take at every node."""

    def test_spe_is_take_at_node_0(self):
        """For the canonical centipede, backward induction predicts immediate
        defection: all 'Take', first Take at node 0. This is the paradox."""
        p = centipede_payoffs(3)
        actions = backward_induction(p)
        assert actions == ['Take'] * 6
        first_take = next((i for i, a in enumerate(actions) if a == 'Take'), len(actions))
        assert first_take == 0

    def test_action_count_matches_decision_nodes(self):
        """One action per decision node (= len(payoffs) - 1)."""
        p = centipede_payoffs(4)
        actions = backward_induction(p)
        assert len(actions) == len(p) - 1

    def test_spe_holds_for_varying_depths(self):
        """The all-Take SPE is robust to game depth (1 to 6 rounds)."""
        for n in (1, 2, 3, 4, 5, 6):
            p = centipede_payoffs(n)
            actions = backward_induction(p)
            assert all(a == 'Take' for a in actions), f"n_rounds={n}"

    def test_bi_outcome_is_pareto_inferior_to_cooperation(self):
        """The paradox: the BI outcome (Take at node 0) is worse for BOTH players
        than reaching the cooperation terminal."""
        p = centipede_payoffs(3)
        actions = backward_induction(p)
        first_take = next((i for i, a in enumerate(actions) if a == 'Take'), len(actions))
        bi_p1, bi_p2 = p[first_take]
        coop = p[-1]
        # At node 0 the taker gets 1.5 and other gets 0.5; cooperation gives 32 each.
        assert coop[0] > bi_p1 and coop[1] > bi_p2

    def test_actions_are_well_formed(self):
        """Every action is exactly 'Take' or 'Pass'."""
        p = centipede_payoffs(3)
        actions = backward_induction(p)
        assert all(a in ('Take', 'Pass') for a in actions)


# ----------------------------------------------------------------------------
# simulate_experimental_play -- stochastic; pinned at deterministic endpoints.
# ----------------------------------------------------------------------------

class TestSimulateExperimentalPlay:
    """simulate_experimental_play pinned at take_probability 0.0 and 1.0."""

    def test_always_take_reaches_node_0(self):
        """take_probability=1.0 -> always Take at node 0 (P1 defects immediately)."""
        np.random.seed(0)
        for _ in range(20):
            node, p1, p2 = simulate_experimental_play(3, take_probability=1.0)
            assert node == 0
            # P1 (player 0) is the taker: gets the 'take' payoff.
            payoffs = centipede_payoffs(3)
            assert p1 == pytest.approx(payoffs[0][0])
            assert p2 == pytest.approx(payoffs[0][1])

    def test_never_take_reaches_end(self):
        """take_probability=0.0 -> never Take, reach cooperation terminal."""
        np.random.seed(0)
        for _ in range(20):
            node, p1, p2 = simulate_experimental_play(3, take_probability=0.0)
            payoffs = centipede_payoffs(3)
            assert node == len(payoffs) - 1
            assert p1 == pytest.approx(payoffs[-1][0])
            assert p2 == pytest.approx(payoffs[-1][1])

    def test_ending_node_within_bounds(self):
        """Over many stochastic plays the ending node is a valid decision node
        or the cooperation terminal."""
        np.random.seed(42)
        payoffs = centipede_payoffs(3)
        for _ in range(50):
            node, _, _ = simulate_experimental_play(3, take_probability=0.3)
            assert 0 <= node <= len(payoffs) - 1

    def test_payoffs_match_node_where_take_occurs(self):
        """When the game ends by Take, the active player gets the taker payoff."""
        np.random.seed(7)
        payoffs = centipede_payoffs(3)
        for _ in range(50):
            node, p1, p2 = simulate_experimental_play(3, take_probability=0.5)
            if node < len(payoffs) - 1:  # ended by a Take
                taker, other = payoffs[node]
                player = node % 2
                if player == 0:
                    assert p1 == pytest.approx(taker) and p2 == pytest.approx(other)
                else:
                    assert p2 == pytest.approx(taker) and p1 == pytest.approx(other)


# ----------------------------------------------------------------------------
# print_game_tree -- display helper; just assert it runs and mentions nodes.
# ----------------------------------------------------------------------------

class TestPrintGameTree:
    """print_game_tree emits a readable tree without raising."""

    def test_runs_and_mentions_nodes(self, capsys):
        p = centipede_payoffs(2)
        actions = backward_induction(p)
        print_game_tree(p, actions)
        out = capsys.readouterr().out
        assert "Node" in out
        assert "END" in out


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
