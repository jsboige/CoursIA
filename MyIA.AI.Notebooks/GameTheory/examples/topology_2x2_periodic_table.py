# -*- coding: utf-8 -*-
"""
Topology of 2x2 Games - Periodic Table Classification
======================================================

Implements the Robinson-Goforth classification of 2x2 games.
Related to GameTheory-3-Topology2x2.ipynb

The "periodic table" classifies all strict ordinal 2x2 games
based on their strategic properties.

References:
- Robinson & Goforth (2005) "The Topology of the 2x2 Games"
- Rapoport & Guyer (1966) "A Taxonomy of 2x2 Games"
"""

import numpy as np
from itertools import permutations
from typing import Tuple, List, Dict

# Standard ordinal rankings (1=worst, 4=best)
ORDINAL_VALUES = [1, 2, 3, 4]


def create_ordinal_game(p1_ranks: Tuple[int, int, int, int],
                        p2_ranks: Tuple[int, int, int, int]):
    """
    Create a 2x2 game from ordinal rankings.

    Args:
        p1_ranks: Player 1's rankings for outcomes (CC, CD, DC, DD)
        p2_ranks: Player 2's rankings for outcomes (CC, CD, DC, DD)

    Returns:
        Tuple of (A, B) payoff matrices
    """
    A = np.array([
        [p1_ranks[0], p1_ranks[1]],  # Row player Cooperate
        [p1_ranks[2], p1_ranks[3]]   # Row player Defect
    ])
    B = np.array([
        [p2_ranks[0], p2_ranks[2]],  # Column player Cooperate
        [p2_ranks[1], p2_ranks[3]]   # Column player Defect
    ])
    return A, B


def find_pure_nash(A: np.ndarray, B: np.ndarray) -> List[Tuple[int, int]]:
    """Find all pure strategy Nash equilibria."""
    nash = []
    for i in range(2):
        for j in range(2):
            # Check if row i is best response to column j
            row_best = A[i, j] >= A[1-i, j]
            # Check if column j is best response to row i
            col_best = B[i, j] >= B[i, 1-j]
            if row_best and col_best:
                nash.append((i, j))
    return nash


def find_dominant_strategy(payoff: np.ndarray, is_row: bool = True) -> int:
    """
    Find strictly dominant strategy if one exists.

    Returns:
        0 or 1 if dominant strategy exists, -1 otherwise
    """
    if is_row:
        # Check if row 0 dominates row 1
        if payoff[0, 0] > payoff[1, 0] and payoff[0, 1] > payoff[1, 1]:
            return 0
        # Check if row 1 dominates row 0
        if payoff[1, 0] > payoff[0, 0] and payoff[1, 1] > payoff[0, 1]:
            return 1
    else:
        # Check if column 0 dominates column 1
        if payoff[0, 0] > payoff[0, 1] and payoff[1, 0] > payoff[1, 1]:
            return 0
        # Check if column 1 dominates column 0
        if payoff[0, 1] > payoff[0, 0] and payoff[1, 1] > payoff[1, 0]:
            return 1
    return -1


def classify_game(A: np.ndarray, B: np.ndarray) -> str:
    """
    Classify a 2x2 game into one of the canonical types.

    Returns one of:
    - "Prisoner's Dilemma"
    - "Stag Hunt"
    - "Chicken/Hawk-Dove"
    - "Battle of the Sexes"
    - "Matching Pennies"
    - "Coordination Game"
    - "Dominant Strategy"
    - "Other"
    """
    nash_eq = find_pure_nash(A, B)
    dom1 = find_dominant_strategy(A, is_row=True)
    dom2 = find_dominant_strategy(B, is_row=False)

    # Both have dominant strategies
    if dom1 != -1 and dom2 != -1:
        # Check if it's a Prisoner's Dilemma pattern
        # Nash is (D,D) but (C,C) is Pareto superior
        if len(nash_eq) == 1:
            i, j = nash_eq[0]
            other_i, other_j = 1 - i, 1 - j
            if A[other_i, other_j] > A[i, j] and B[other_i, other_j] > B[i, j]:
                return "Prisoner's Dilemma"
        return "Dominant Strategy"

    # Check for zero pure Nash (Matching Pennies type)
    if len(nash_eq) == 0:
        return "Matching Pennies"

    # Two pure Nash equilibria
    if len(nash_eq) == 2:
        (i1, j1), (i2, j2) = nash_eq

        # Both on diagonal: Coordination game
        if (i1 == j1) and (i2 == j2):
            # Check for Stag Hunt pattern: one Nash is Pareto dominant
            p1 = A[i1, j1] + B[i1, j1]
            p2 = A[i2, j2] + B[i2, j2]
            if p1 != p2:
                return "Stag Hunt"
            return "Coordination Game"

        # Anti-coordination: Chicken/Hawk-Dove
        if (i1 != j1) and (i2 != j2):
            return "Chicken/Hawk-Dove"

        return "Battle of the Sexes"

    # One pure Nash
    return "Other"


# Named game templates
NAMED_GAMES = {
    "Prisoner's Dilemma": {
        "p1": (3, 1, 4, 2),  # R, S, T, P
        "p2": (3, 4, 1, 2),
        "description": "Both defect despite mutual cooperation being better"
    },
    "Stag Hunt": {
        "p1": (4, 1, 3, 2),
        "p2": (4, 3, 1, 2),
        "description": "Two equilibria: risk-dominant (Hare) vs payoff-dominant (Stag)"
    },
    "Chicken": {
        "p1": (3, 2, 4, 1),
        "p2": (3, 4, 2, 1),
        "description": "Anti-coordination: two asymmetric equilibria"
    },
    "Battle of the Sexes": {
        "p1": (4, 1, 2, 3),
        "p2": (3, 2, 1, 4),
        "description": "Coordination with different preferences"
    },
    "Matching Pennies": {
        "p1": (4, 1, 2, 3),
        "p2": (1, 4, 3, 2),
        "description": "Zero-sum, no pure equilibrium"
    },
}


def print_game_analysis(name: str, A: np.ndarray, B: np.ndarray):
    """Print detailed analysis of a game."""
    print(f"\n{'='*50}")
    print(f"Game: {name}")
    print(f"{'='*50}")

    print("\nPayoff matrix (P1, P2):")
    print("              C           D")
    print(f"  C       ({A[0,0]},{B[0,0]})       ({A[0,1]},{B[0,1]})")
    print(f"  D       ({A[1,0]},{B[1,0]})       ({A[1,1]},{B[1,1]})")

    nash = find_pure_nash(A, B)
    print(f"\nPure Nash equilibria: {nash}")

    classification = classify_game(A, B)
    print(f"Classification: {classification}")


def main():
    print("=" * 60)
    print("Topology of 2x2 Games - Periodic Table")
    print("=" * 60)

    # Analyze named games
    for name, data in NAMED_GAMES.items():
        A, B = create_ordinal_game(data["p1"], data["p2"])
        print_game_analysis(name, A, B)
        print(f"Description: {data['description']}")

    # Count total number of strict ordinal 2x2 games
    print("\n" + "=" * 60)
    print("Statistics")
    print("=" * 60)

    # Each player has 4! = 24 ordinal preferences
    # Total: 24 * 24 = 576 games (before symmetry reduction)
    print(f"\nTotal strict ordinal 2x2 games: 24 x 24 = 576")
    print("After removing symmetric equivalents: 78 distinct games")
    print("Robinson-Goforth identifies 4 main 'layers' based on Nash structure")


if __name__ == "__main__":
    main()
