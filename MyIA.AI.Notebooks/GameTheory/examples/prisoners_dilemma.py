# -*- coding: utf-8 -*-
"""
Prisoner's Dilemma - Classic Example
====================================

Demonstrates the Prisoner's Dilemma using Nashpy.
Related to GameTheory-2-NormalForm.ipynb and GameTheory-4-NashEquilibrium.ipynb

Payoff matrix:
              Player 2
              C       D
Player 1  C  (3,3)   (0,5)
          D  (5,0)   (1,1)

Where:
- C = Cooperate
- D = Defect
- T=5 (Temptation), R=3 (Reward), P=1 (Punishment), S=0 (Sucker)
"""

import numpy as np

try:
    import nashpy as nash
    HAS_NASHPY = True
except ImportError:
    HAS_NASHPY = False
    print("Warning: nashpy not installed. Run: pip install nashpy")


def create_prisoners_dilemma():
    """Create the Prisoner's Dilemma game."""
    # Payoff matrices (row player, column player)
    A = np.array([
        [3, 0],  # Player 1: Cooperate
        [5, 1]   # Player 1: Defect
    ])
    B = np.array([
        [3, 5],  # Player 2: Cooperate
        [0, 1]   # Player 2: Defect
    ])
    return A, B


def find_nash_equilibria(A, B):
    """Find Nash equilibria using support enumeration."""
    if not HAS_NASHPY:
        return None

    game = nash.Game(A, B)
    equilibria = list(game.support_enumeration())
    return equilibria


def analyze_dominance(A, B):
    """Analyze dominant strategies."""
    results = []

    # Check if Defect dominates Cooperate for Player 1
    if A[1, 0] > A[0, 0] and A[1, 1] > A[0, 1]:
        results.append("Player 1: Defect strictly dominates Cooperate")

    # Check if Defect dominates Cooperate for Player 2
    if B[0, 1] > B[0, 0] and B[1, 1] > B[1, 0]:
        results.append("Player 2: Defect strictly dominates Cooperate")

    return results


def main():
    print("=" * 60)
    print("Prisoner's Dilemma Analysis")
    print("=" * 60)

    A, B = create_prisoners_dilemma()

    print("\nPayoff Matrix (Player 1, Player 2):")
    print("              Cooperate    Defect")
    print(f"  Cooperate   ({A[0,0]},{B[0,0]})        ({A[0,1]},{B[0,1]})")
    print(f"  Defect      ({A[1,0]},{B[1,0]})        ({A[1,1]},{B[1,1]})")

    # Dominance analysis
    print("\n--- Dominance Analysis ---")
    dominance = analyze_dominance(A, B)
    for d in dominance:
        print(f"  {d}")

    # Nash equilibria
    if HAS_NASHPY:
        print("\n--- Nash Equilibria ---")
        equilibria = find_nash_equilibria(A, B)
        for i, (s1, s2) in enumerate(equilibria, 1):
            print(f"  Equilibrium {i}:")
            print(f"    Player 1: [{s1[0]:.2f} C, {s1[1]:.2f} D]")
            print(f"    Player 2: [{s2[0]:.2f} C, {s2[1]:.2f} D]")

            # Calculate expected payoffs
            expected_1 = s1 @ A @ s2
            expected_2 = s1 @ B @ s2
            print(f"    Expected payoffs: ({expected_1:.2f}, {expected_2:.2f})")

    # Interpretation
    print("\n--- Interpretation ---")
    print("  The unique Nash equilibrium is (Defect, Defect)")
    print("  This is Pareto-inferior to (Cooperate, Cooperate)")
    print("  This illustrates the tension between individual and collective rationality")


if __name__ == "__main__":
    main()
