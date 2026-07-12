# -*- coding: utf-8 -*-
"""
Stackelberg Leader-Follower Game
================================

Demonstrates Stackelberg equilibrium in a duopoly setting.
Related to GameTheory-13-DifferentialGames.ipynb

In a Stackelberg game:
- The leader moves first and commits to a quantity
- The follower observes the leader's choice and responds optimally
- The leader anticipates the follower's response
"""

import numpy as np
from typing import Tuple, Callable
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt


def cournot_reaction_curve(rival_quantity: float,
                           demand_intercept: float = 100,
                           marginal_cost: float = 10) -> float:
    """
    Calculate best response in Cournot competition.

    Linear demand: P = a - Q where Q = q1 + q2
    Profit: pi_i = (P - c) * q_i = (a - q1 - q2 - c) * q_i

    Best response: q_i = (a - c - q_j) / 2
    """
    a, c = demand_intercept, marginal_cost
    return max(0, (a - c - rival_quantity) / 2)


def cournot_equilibrium(demand_intercept: float = 100,
                        marginal_cost: float = 10) -> Tuple[float, float]:
    """
    Calculate Cournot-Nash equilibrium quantities.

    Symmetric equilibrium: q* = (a - c) / 3
    """
    a, c = demand_intercept, marginal_cost
    q_star = (a - c) / 3
    return q_star, q_star


def stackelberg_equilibrium(demand_intercept: float = 100,
                            cost_leader: float = 10,
                            cost_follower: float = 10) -> Tuple[float, float]:
    """
    Calculate Stackelberg equilibrium.

    Leader maximizes profit anticipating follower's best response.
    Follower's reaction: q_F = (a - c_F - q_L) / 2

    Leader solves: max (a - q_L - q_F - c_L) * q_L
                   s.t. q_F = (a - c_F - q_L) / 2

    Solution:
    q_L = (a - 2*c_L + c_F) / 2
    q_F = (a - 2*c_F + c_L) / 4
    """
    a = demand_intercept
    c_L, c_F = cost_leader, cost_follower

    q_leader = (a - 2 * c_L + c_F) / 2
    q_follower = (a + c_L - 2 * c_F) / 4

    return max(0, q_leader), max(0, q_follower)


def calculate_profits(q1: float, q2: float,
                      demand_intercept: float = 100,
                      cost1: float = 10, cost2: float = 10) -> Tuple[float, float]:
    """Calculate profits for both firms."""
    a = demand_intercept
    price = a - q1 - q2
    profit1 = (price - cost1) * q1
    profit2 = (price - cost2) * q2
    return profit1, profit2


def compare_equilibria():
    """Compare Cournot and Stackelberg equilibria."""
    a, c = 100, 10

    # Cournot
    q_c1, q_c2 = cournot_equilibrium(a, c)
    pi_c1, pi_c2 = calculate_profits(q_c1, q_c2, a, c, c)

    # Stackelberg (Firm 1 leads)
    q_s1, q_s2 = stackelberg_equilibrium(a, c, c)
    pi_s1, pi_s2 = calculate_profits(q_s1, q_s2, a, c, c)

    print("\n--- Equilibrium Comparison ---")
    print(f"\nParameters: Demand intercept = {a}, Marginal cost = {c}")

    print("\nCournot-Nash Equilibrium:")
    print(f"  Quantities: q1 = {q_c1:.2f}, q2 = {q_c2:.2f}")
    print(f"  Total output: Q = {q_c1 + q_c2:.2f}")
    print(f"  Price: P = {a - q_c1 - q_c2:.2f}")
    print(f"  Profits: pi1 = {pi_c1:.2f}, pi2 = {pi_c2:.2f}")

    print("\nStackelberg Equilibrium (Firm 1 leads):")
    print(f"  Quantities: q_L = {q_s1:.2f}, q_F = {q_s2:.2f}")
    print(f"  Total output: Q = {q_s1 + q_s2:.2f}")
    print(f"  Price: P = {a - q_s1 - q_s2:.2f}")
    print(f"  Profits: pi_L = {pi_s1:.2f}, pi_F = {pi_s2:.2f}")

    print("\n--- Key Insights ---")
    print(f"  Leader advantage: {pi_s1 - pi_c1:.2f} extra profit")
    print(f"  Follower disadvantage: {pi_c2 - pi_s2:.2f} lost profit")
    print(f"  Total output higher in Stackelberg: {q_s1 + q_s2 - q_c1 - q_c2:.2f}")
    print(f"  Consumer surplus higher in Stackelberg (lower price)")


def plot_equilibria():
    """Visualize reaction curves and equilibria."""
    a, c = 100, 10

    # Cournot equilibrium
    q_c1, q_c2 = cournot_equilibrium(a, c)

    # Stackelberg equilibrium
    q_s1, q_s2 = stackelberg_equilibrium(a, c, c)

    # Reaction curves
    q_range = np.linspace(0, 50, 100)
    r1 = [cournot_reaction_curve(q, a, c) for q in q_range]  # Firm 1's reaction
    r2 = [cournot_reaction_curve(q, a, c) for q in q_range]  # Firm 2's reaction

    fig, ax = plt.subplots(figsize=(10, 8))

    # Plot reaction curves
    ax.plot(q_range, r1, 'b-', label='Firm 1 reaction', linewidth=2)
    ax.plot(r2, q_range, 'r-', label='Firm 2 reaction', linewidth=2)

    # Plot equilibria
    ax.plot(q_c1, q_c2, 'go', markersize=12, label='Cournot equilibrium')
    ax.plot(q_s1, q_s2, 'rs', markersize=12, label='Stackelberg (1 leads)')

    # Leader's iso-profit curve through Stackelberg equilibrium
    # pi_L = (a - q1 - q2 - c) * q1 = constant
    q1_vals = np.linspace(1, 50, 100)
    profit_L = calculate_profits(q_s1, q_s2, a, c, c)[0]
    q2_iso = a - c - q1_vals - profit_L / q1_vals
    q2_iso = np.where(q2_iso > 0, q2_iso, np.nan)
    ax.plot(q1_vals, q2_iso, 'g--', alpha=0.5, label='Leader iso-profit')

    ax.set_xlabel('Firm 1 Quantity (q1)')
    ax.set_ylabel('Firm 2 Quantity (q2)')
    ax.set_title('Cournot vs Stackelberg Equilibrium')
    ax.legend()
    ax.set_xlim(0, 50)
    ax.set_ylim(0, 50)
    ax.grid(True, alpha=0.3)

    plt.tight_layout()
    plt.savefig('stackelberg_equilibrium.png', dpi=150)
    print("\nPlot saved to stackelberg_equilibrium.png")
    plt.close()


def main():
    print("=" * 60)
    print("Stackelberg Leader-Follower Model")
    print("=" * 60)

    print("\nModel Setup:")
    print("  - Two firms compete in quantities (Cournot competition)")
    print("  - Linear demand: P = a - Q")
    print("  - Constant marginal cost: c")
    print("\nStackelberg adds commitment:")
    print("  - Leader commits to quantity first")
    print("  - Follower observes and responds optimally")
    print("  - Leader anticipates follower's reaction")

    compare_equilibria()
    plot_equilibria()


if __name__ == "__main__":
    main()
