# -*- coding: utf-8 -*-
"""
Stag Hunt and Forward Induction
===============================

Demonstrates forward induction as an equilibrium refinement.
Related to GameTheory-9-ForwardInduction-SPE.ipynb

The Stag Hunt has two pure Nash equilibria:
- (Stag, Stag) - Pareto optimal
- (Hare, Hare) - Risk dominant

Forward induction can sometimes select between multiple equilibria
by reasoning about what deviations "signal" about a player's intentions.
"""

import numpy as np
from typing import Tuple, List, Optional

try:
    import nashpy as nash
    HAS_NASHPY = True
except ImportError:
    HAS_NASHPY = False


def create_stag_hunt(stag_reward: float = 4.0,
                     hare_reward: float = 2.0,
                     coordination_fail: float = 0.0) -> Tuple[np.ndarray, np.ndarray]:
    """
    Create a Stag Hunt game.

    Standard payoffs:
    - Both hunt stag: (stag_reward, stag_reward)
    - Both hunt hare: (hare_reward, hare_reward)
    - One hunts stag, other hunts hare: stag hunter gets fail, hare hunter gets hare_reward
    """
    A = np.array([
        [stag_reward, coordination_fail],  # Hunt Stag
        [hare_reward - 1, hare_reward]     # Hunt Hare (slightly less with mixed)
    ])
    B = np.array([
        [stag_reward, hare_reward - 1],
        [coordination_fail, hare_reward]
    ])
    return A, B


def find_equilibria(A: np.ndarray, B: np.ndarray) -> dict:
    """Find all Nash equilibria."""
    result = {
        'pure': [],
        'mixed': []
    }

    # Pure equilibria
    for i in range(2):
        for j in range(2):
            if A[i, j] >= A[1-i, j] and B[i, j] >= B[i, 1-j]:
                result['pure'].append((i, j))

    # Mixed equilibria using nashpy
    if HAS_NASHPY:
        game = nash.Game(A, B)
        for eq in game.support_enumeration():
            s1, s2 = eq
            if not (np.allclose(s1, [1, 0]) or np.allclose(s1, [0, 1])):
                result['mixed'].append((s1, s2))

    return result


def risk_dominance_analysis(A: np.ndarray, B: np.ndarray,
                            eq1: Tuple[int, int], eq2: Tuple[int, int]) -> str:
    """
    Determine which equilibrium is risk-dominant using Harsanyi-Selten criterion.

    An equilibrium (a*, b*) risk-dominates (a', b') if:
    [u1(a*, b*) - u1(a', b*)] * [u2(a*, b*) - u2(a*, b')] >
    [u1(a', b') - u1(a*, b')] * [u2(a', b') - u2(a', b*)]
    """
    i1, j1 = eq1
    i2, j2 = eq2

    # Deviation losses for equilibrium 1
    loss1_player1 = A[i1, j1] - A[i2, j1]  # P1 deviates from eq1
    loss1_player2 = B[i1, j1] - B[i1, j2]  # P2 deviates from eq1
    product1 = loss1_player1 * loss1_player2

    # Deviation losses for equilibrium 2
    loss2_player1 = A[i2, j2] - A[i1, j2]  # P1 deviates from eq2
    loss2_player2 = B[i2, j2] - B[i2, j1]  # P2 deviates from eq2
    product2 = loss2_player1 * loss2_player2

    if product1 > product2:
        return f"Equilibrium 1 {eq1} is risk-dominant"
    elif product2 > product1:
        return f"Equilibrium 2 {eq2} is risk-dominant"
    else:
        return "Neither equilibrium is strictly risk-dominant"


def forward_induction_analysis():
    """
    Explain forward induction reasoning in an extended Stag Hunt.

    Consider: Player 1 can "burn money" (destroy some payoff) before playing.
    If P1 burns money AND still plays Stag, this signals commitment.
    """
    print("\n--- Forward Induction Analysis ---")
    print("\nScenario: Extended Stag Hunt with 'money burning'")
    print("\nPlayer 1 can choose to:")
    print("  (a) Play standard game")
    print("  (b) Burn 1 unit of payoff, then play")
    print("\nForward Induction Reasoning:")
    print("  1. If P1 burns money but then plays Hare, they get less than not burning")
    print("  2. So burning money is only rational if P1 intends to play Stag")
    print("  3. P2, seeing burned money, should infer P1 will play Stag")
    print("  4. P2's best response to Stag is Stag")
    print("  5. Thus, burning money can coordinate on (Stag, Stag)")
    print("\nThis shows how forward induction selects the payoff-dominant equilibrium")


def main():
    print("=" * 60)
    print("Stag Hunt - Forward Induction Analysis")
    print("=" * 60)

    A, B = create_stag_hunt()

    print("\nPayoff Matrix:")
    print("              Stag        Hare")
    print(f"  Stag       ({A[0,0]:.0f},{B[0,0]:.0f})       ({A[0,1]:.0f},{B[0,1]:.0f})")
    print(f"  Hare       ({A[1,0]:.0f},{B[1,0]:.0f})       ({A[1,1]:.0f},{B[1,1]:.0f})")

    # Find equilibria
    eq = find_equilibria(A, B)

    print("\n--- Nash Equilibria ---")
    print(f"Pure equilibria: {eq['pure']}")
    for i, (row, col) in enumerate(eq['pure']):
        action1 = "Stag" if row == 0 else "Hare"
        action2 = "Stag" if col == 0 else "Hare"
        print(f"  ({action1}, {action2}): Payoffs = ({A[row,col]:.0f}, {B[row,col]:.0f})")

    if eq['mixed']:
        print(f"\nMixed equilibria:")
        for s1, s2 in eq['mixed']:
            print(f"  P1: {s1[0]:.2f} Stag, {s1[1]:.2f} Hare")
            print(f"  P2: {s2[0]:.2f} Stag, {s2[1]:.2f} Hare")

    # Risk dominance
    if len(eq['pure']) >= 2:
        print("\n--- Risk Dominance ---")
        print(risk_dominance_analysis(A, B, eq['pure'][0], eq['pure'][1]))
        print("\n(Hare, Hare) is risk-dominant despite lower payoffs")
        print("because deviating from it is less risky")

    # Forward induction
    forward_induction_analysis()


if __name__ == "__main__":
    main()
