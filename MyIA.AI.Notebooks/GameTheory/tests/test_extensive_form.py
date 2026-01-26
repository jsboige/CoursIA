"""
Tests for extensive form games and backward induction.

Run with: pytest tests/test_extensive_form.py
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from game_theory_utils import (
    GameNode, ExtensiveFormGame,
    backward_induction, create_entry_game, create_centipede_game
)


class TestGameNode:
    """Tests for GameNode class."""

    def test_terminal_node(self):
        """Terminal nodes have player -1."""
        node = GameNode("term", player=-1, payoffs=(1, 2))
        assert node.is_terminal()
        assert not node.is_chance()

    def test_chance_node(self):
        """Chance nodes have player 0."""
        node = GameNode("chance", player=0, actions=["A", "B"],
                       chance_probs={"A": 0.5, "B": 0.5})
        assert node.is_chance()
        assert not node.is_terminal()

    def test_decision_node(self):
        """Decision nodes have player >= 1."""
        node = GameNode("decision", player=1, actions=["X", "Y"], infoset="I1")
        assert not node.is_terminal()
        assert not node.is_chance()
        assert node.player == 1


class TestExtensiveFormGame:
    """Tests for ExtensiveFormGame class."""

    def test_entry_game_structure(self):
        """Entry game has correct structure."""
        game = create_entry_game()

        assert game.name == "Entry Game"
        assert game.num_players == 2
        assert game.root is not None
        assert len(game.get_terminal_nodes()) == 3

    def test_entry_game_perfect_info(self):
        """Entry game has perfect information."""
        game = create_entry_game()
        assert game.has_perfect_information()

    def test_centipede_game_structure(self):
        """Centipede game has correct structure."""
        n_rounds = 6
        game = create_centipede_game(n_rounds)

        assert game.name == "Centipede"
        assert game.num_players == 2
        # n_rounds Take terminals + 1 final Pass terminal
        assert len(game.get_terminal_nodes()) == n_rounds + 1

    def test_centipede_game_infosets(self):
        """Centipede game infosets are singletons (perfect info)."""
        game = create_centipede_game(6)
        assert game.has_perfect_information()


class TestBackwardInduction:
    """Tests for backward induction algorithm."""

    def test_entry_game_equilibrium(self):
        """Entry game equilibrium: (Enter, Accommodate)."""
        game = create_entry_game()
        solution, eq_payoffs = backward_induction(game)

        # Equilibrium payoffs
        assert eq_payoffs == (1, 1)

        # Entrant enters
        assert solution["root"][0] == "Enter"

        # Incumbent accommodates
        assert solution["incumbent"][0] == "Accommodate"

    def test_centipede_game_immediate_take(self):
        """Centipede game: Player 1 takes immediately at equilibrium."""
        game = create_centipede_game(6)
        solution, eq_payoffs = backward_induction(game)

        # First player takes immediately
        first_node = "node_0"
        assert solution[first_node][0] == "Take"

        # Payoffs at round 0: (1, 0) for player 1 taking
        # pot = 2^1 = 2, taker gets ceil(2/2) = 1, other gets 0
        assert eq_payoffs == (1, 0)

    def test_centipede_all_take(self):
        """At every decision node, the player prefers Take."""
        game = create_centipede_game(6)
        solution, _ = backward_induction(game)

        for node_id, (action, _) in solution.items():
            assert action == "Take", f"Node {node_id} should Take, got {action}"

    def test_simple_game_with_chance(self):
        """Test backward induction with chance node."""
        game = ExtensiveFormGame("Chance Game", num_players=2)

        # Terminal nodes
        win = GameNode("win", player=-1, payoffs=(10, 0))
        lose = GameNode("lose", player=-1, payoffs=(0, 10))

        # Chance node at root
        chance = GameNode("root", player=0, actions=["H", "T"],
                         chance_probs={"H": 0.5, "T": 0.5})
        chance.children = {"H": win, "T": lose}

        game.set_root(chance)
        game.add_node(win)
        game.add_node(lose)

        solution, eq_payoffs = backward_induction(game)

        # Expected payoffs: 0.5 * 10 + 0.5 * 0 = 5 for player 1
        np.testing.assert_almost_equal(eq_payoffs[0], 5.0)
        np.testing.assert_almost_equal(eq_payoffs[1], 5.0)


class TestCustomGames:
    """Tests for custom game constructions."""

    def test_ultimatum_simple(self):
        """Simple ultimatum: proposer offers 5, responder accepts."""
        game = ExtensiveFormGame("Ultimatum", num_players=2)

        # Terminal nodes
        accept = GameNode("accept", player=-1, payoffs=(5, 5))
        reject = GameNode("reject", player=-1, payoffs=(0, 0))

        # Responder
        responder = GameNode("responder", player=2,
                            actions=["Accept", "Reject"], infoset="I2")
        responder.children = {"Accept": accept, "Reject": reject}

        # Proposer (single offer for simplicity)
        proposer = GameNode("root", player=1,
                           actions=["Offer5"], infoset="I1")
        proposer.children = {"Offer5": responder}

        game.set_root(proposer)
        for node in [responder, accept, reject]:
            game.add_node(node)

        solution, eq_payoffs = backward_induction(game)

        # Responder accepts (5 > 0)
        assert solution["responder"][0] == "Accept"
        assert eq_payoffs == (5, 5)

    def test_three_player_game(self):
        """Test game with 3 players."""
        game = ExtensiveFormGame("Three Player", num_players=3)

        # Terminals
        t1 = GameNode("t1", player=-1, payoffs=(1, 2, 3))
        t2 = GameNode("t2", player=-1, payoffs=(2, 1, 1))

        # Player 3
        p3 = GameNode("p3", player=3, actions=["X", "Y"], infoset="I3")
        p3.children = {"X": t1, "Y": t2}

        # Player 2
        t3 = GameNode("t3", player=-1, payoffs=(3, 3, 0))
        p2 = GameNode("p2", player=2, actions=["A", "B"], infoset="I2")
        p2.children = {"A": p3, "B": t3}

        # Player 1
        p1 = GameNode("root", player=1, actions=["L", "R"], infoset="I1")
        t4 = GameNode("t4", player=-1, payoffs=(0, 0, 5))
        p1.children = {"L": p2, "R": t4}

        game.set_root(p1)
        for node in [p2, p3, t1, t2, t3, t4]:
            game.add_node(node)

        solution, eq_payoffs = backward_induction(game)

        # Player 3 at p3: X gives 3, Y gives 1 -> chooses X
        assert solution["p3"][0] == "X"

        # Player 2 at p2: A leads to (1,2,3), B gives (3,3,0) -> B (3 > 2)
        assert solution["p2"][0] == "B"

        # Player 1: L leads to (3,3,0), R gives (0,0,5) -> L (3 > 0)
        assert solution["root"][0] == "L"

        assert eq_payoffs == (3, 3, 0)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
