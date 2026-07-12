# -*- coding: utf-8 -*-
"""
Kuhn Poker - Counterfactual Regret Minimization
===============================================

Demonstrates CFR algorithm on Kuhn Poker.
Related to GameTheory-12-ImperfectInfo-CFR.ipynb

Kuhn Poker is a simplified poker game:
- 3 cards: Jack, Queen, King
- Each player antes 1 chip
- One card dealt to each player
- Player 1 acts first: Check or Bet
- Player 2 responds: Check/Call or Fold/Bet
"""

import numpy as np
from typing import Dict, List, Tuple
import random


# Game constants
JACK, QUEEN, KING = 0, 1, 2
CHECK, BET = 0, 1
FOLD, CALL = 0, 1

CARD_NAMES = {0: 'J', 1: 'Q', 2: 'K'}


class KuhnPoker:
    """Simple Kuhn Poker implementation for CFR."""

    def __init__(self):
        self.regret_sum: Dict[str, np.ndarray] = {}
        self.strategy_sum: Dict[str, np.ndarray] = {}

    def get_info_set(self, card: int, history: str) -> str:
        """Get information set string."""
        return f"{CARD_NAMES[card]}{history}"

    def get_strategy(self, info_set: str, n_actions: int = 2) -> np.ndarray:
        """Get current strategy through regret matching."""
        if info_set not in self.regret_sum:
            self.regret_sum[info_set] = np.zeros(n_actions)
            self.strategy_sum[info_set] = np.zeros(n_actions)

        regrets = self.regret_sum[info_set]
        positive_regrets = np.maximum(regrets, 0)
        total = positive_regrets.sum()

        if total > 0:
            return positive_regrets / total
        else:
            return np.ones(n_actions) / n_actions

    def cfr(self, cards: List[int], history: str,
            p0: float, p1: float) -> float:
        """
        Counterfactual Regret Minimization.

        Args:
            cards: [player0_card, player1_card]
            history: Action history string
            p0, p1: Reach probabilities for each player

        Returns:
            Expected utility for player 0
        """
        # Determine current player and check for terminal states
        player = len(history) % 2
        opponent = 1 - player

        # Terminal state checks
        if len(history) >= 2:
            # Check-Check: showdown
            if history == "cc":
                return 1 if cards[0] > cards[1] else -1

            # Check-Bet-Fold
            if history == "cbf":
                return 1  # Player 0 wins pot

            # Check-Bet-Call: showdown for pot of 4
            if history == "cbc":
                return 2 if cards[0] > cards[1] else -2

            # Bet-Fold
            if history == "bf":
                return 1  # Player 0 wins

            # Bet-Call: showdown
            if history == "bc":
                return 2 if cards[0] > cards[1] else -2

        # Get information set and strategy
        info_set = self.get_info_set(cards[player], history)
        strategy = self.get_strategy(info_set)

        # Get available actions based on history
        if history == "" or history == "c":
            actions = ['c', 'b']  # Check or Bet
        elif history == "b" or history == "cb":
            actions = ['f', 'c']  # Fold or Call
        else:
            return 0  # Shouldn't reach here

        n_actions = len(actions)
        action_utils = np.zeros(n_actions)

        # Calculate utilities for each action
        for i, action in enumerate(actions):
            new_history = history + action
            if player == 0:
                action_utils[i] = -self.cfr(cards, new_history,
                                           p0 * strategy[i], p1)
            else:
                action_utils[i] = -self.cfr(cards, new_history,
                                           p0, p1 * strategy[i])

        # Expected utility
        util = (strategy * action_utils).sum()

        # Accumulate regrets and strategy
        if player == 0:
            for i in range(n_actions):
                regret = action_utils[i] - util
                self.regret_sum[info_set][i] += p1 * regret
            self.strategy_sum[info_set] += p0 * strategy
        else:
            for i in range(n_actions):
                regret = action_utils[i] - util
                self.regret_sum[info_set][i] += p0 * regret
            self.strategy_sum[info_set] += p1 * strategy

        return util

    def train(self, iterations: int = 10000) -> float:
        """Train the CFR algorithm."""
        util = 0
        cards_list = [(i, j) for i in range(3) for j in range(3) if i != j]

        for _ in range(iterations):
            # Sample random card deal
            cards = list(random.choice(cards_list))
            util += self.cfr(cards, "", 1, 1)

        return util / iterations

    def get_average_strategy(self) -> Dict[str, np.ndarray]:
        """Get the average strategy (converges to Nash)."""
        avg_strategy = {}
        for info_set, strat_sum in self.strategy_sum.items():
            total = strat_sum.sum()
            if total > 0:
                avg_strategy[info_set] = strat_sum / total
            else:
                avg_strategy[info_set] = np.ones(2) / 2
        return avg_strategy


def main():
    print("=" * 60)
    print("Kuhn Poker - CFR Training")
    print("=" * 60)

    print("\nGame Rules:")
    print("  - 3 cards: Jack < Queen < King")
    print("  - Each player antes 1 chip")
    print("  - P1 acts: Check (c) or Bet (b)")
    print("  - P2 responds: Fold (f), Call (c), or Bet (b)")

    kuhn = KuhnPoker()

    print("\n--- Training ---")
    for n_iter in [100, 1000, 10000]:
        kuhn = KuhnPoker()  # Reset
        avg_util = kuhn.train(n_iter)
        print(f"After {n_iter:5d} iterations: Expected utility = {avg_util:.4f}")

    # Final training
    kuhn = KuhnPoker()
    kuhn.train(50000)
    avg_strategy = kuhn.get_average_strategy()

    print("\n--- Approximate Nash Equilibrium Strategy ---")
    print("\nPlayer 1 (First to act):")
    for card_name in ['J', 'Q', 'K']:
        info_set = card_name
        if info_set in avg_strategy:
            s = avg_strategy[info_set]
            print(f"  {card_name}: Check {s[0]*100:.1f}%, Bet {s[1]*100:.1f}%")

    print("\nPlayer 2 (After P1 checks):")
    for card_name in ['J', 'Q', 'K']:
        info_set = card_name + 'c'
        if info_set in avg_strategy:
            s = avg_strategy[info_set]
            print(f"  {card_name}: Check {s[0]*100:.1f}%, Bet {s[1]*100:.1f}%")

    print("\nPlayer 2 (After P1 bets):")
    for card_name in ['J', 'Q', 'K']:
        info_set = card_name + 'b'
        if info_set in avg_strategy:
            s = avg_strategy[info_set]
            print(f"  {card_name}: Fold {s[0]*100:.1f}%, Call {s[1]*100:.1f}%")

    print("\n--- Theoretical Nash Strategy (for comparison) ---")
    print("Player 1 with Jack: Bet 1/3, Check 2/3")
    print("Player 1 with Queen: Check always")
    print("Player 1 with King: Bet 3x more often than Jack bluffs")


if __name__ == "__main__":
    main()
