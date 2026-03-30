# -*- coding: utf-8 -*-
"""
Centipede Game - Backward Induction Paradox
===========================================

Demonstrates the centipede game and backward induction.
Related to GameTheory-8-BackwardInduction.ipynb

The centipede game shows a tension between backward induction
(which predicts immediate defection) and empirical behavior
(where players often continue longer).
"""

import numpy as np
from typing import List, Tuple


def centipede_payoffs(n_rounds: int,
                      growth_rate: float = 2.0,
                      defection_bonus: float = 1.5) -> List[Tuple[float, float]]:
    """
    Calculate payoffs at each decision node of a centipede game.

    Args:
        n_rounds: Number of rounds (each round has 2 decisions)
        growth_rate: How much the pot grows each round
        defection_bonus: Bonus for the player who defects

    Returns:
        List of (defector_payoff, other_payoff) at each node
    """
    payoffs = []
    pot = 1.0

    for round_num in range(n_rounds * 2):
        # If player defects now
        defector_gets = pot * defection_bonus
        other_gets = pot / 2
        payoffs.append((defector_gets, other_gets))

        # Pot grows for next round
        pot *= growth_rate

    # Final cooperation payoff (if no one defects)
    final_payoff = pot / 2
    payoffs.append((final_payoff, final_payoff))

    return payoffs


def backward_induction(payoffs: List[Tuple[float, float]]) -> List[str]:
    """
    Solve the centipede game by backward induction.

    Returns:
        List of optimal actions ('Take' or 'Pass') at each node
    """
    n_nodes = len(payoffs) - 1  # Last entry is mutual cooperation
    actions = ['Pass'] * n_nodes

    # Start from the last decision node
    current_player_value = [None, None]  # [Player 1 value, Player 2 value]

    # Final node: both get equal share if reaching the end
    final_value = payoffs[-1][0]  # Same for both
    current_player_value[0] = final_value
    current_player_value[1] = final_value

    # Work backwards
    for node in range(n_nodes - 1, -1, -1):
        player = node % 2  # 0 = Player 1, 1 = Player 2

        take_payoff = payoffs[node][0]  # What this player gets if they take
        pass_value = current_player_value[player]  # Value of passing

        if take_payoff >= pass_value:
            actions[node] = 'Take'
            # If taking, update values for previous nodes
            current_player_value[player] = take_payoff
            current_player_value[1 - player] = payoffs[node][1]
        else:
            actions[node] = 'Pass'

    return actions


def simulate_experimental_play(n_rounds: int,
                                take_probability: float = 0.1) -> Tuple[int, float, float]:
    """
    Simulate experimental behavior (players don't always take immediately).

    Args:
        n_rounds: Number of rounds
        take_probability: Probability of taking at each node

    Returns:
        (ending_node, player1_payoff, player2_payoff)
    """
    payoffs = centipede_payoffs(n_rounds)

    for node in range(len(payoffs) - 1):
        if np.random.random() < take_probability:
            player = node % 2
            if player == 0:
                return node, payoffs[node][0], payoffs[node][1]
            else:
                return node, payoffs[node][1], payoffs[node][0]

    # Reached the end
    return len(payoffs) - 1, payoffs[-1][0], payoffs[-1][1]


def print_game_tree(payoffs: List[Tuple[float, float]], actions: List[str]):
    """Print a visual representation of the game."""
    print("\nCentipede Game Tree:")
    print("-" * 60)

    for node in range(len(payoffs) - 1):
        player = "P1" if node % 2 == 0 else "P2"
        take_p1, take_p2 = payoffs[node]
        action = actions[node]

        marker = "**" if action == "Take" else "  "
        print(f"  Node {node} ({player}): Take=({take_p1:.1f}, {take_p2:.1f}) {marker}")
        print(f"  {' ' * 12} |")
        print(f"  {' ' * 12} v Pass")

    final = payoffs[-1][0]
    print(f"  END: ({final:.1f}, {final:.1f})")


def main():
    print("=" * 60)
    print("Centipede Game - Backward Induction Analysis")
    print("=" * 60)

    n_rounds = 3
    payoffs = centipede_payoffs(n_rounds)

    print(f"\nGame with {n_rounds} rounds ({n_rounds * 2} decision nodes)")
    print(f"Payoffs at each node (if player 'Takes'):")
    for i, (take, other) in enumerate(payoffs[:-1]):
        player = "P1" if i % 2 == 0 else "P2"
        print(f"  Node {i} ({player}): Taker gets {take:.1f}, Other gets {other:.1f}")
    print(f"  Final cooperation: Both get {payoffs[-1][0]:.1f}")

    # Backward induction
    print("\n--- Backward Induction ---")
    actions = backward_induction(payoffs)
    print_game_tree(payoffs, actions)

    # Find where the game ends according to BI
    first_take = next((i for i, a in enumerate(actions) if a == 'Take'), len(actions))
    print(f"\nBackward induction predicts: Take at node {first_take}")

    # Paradox explanation
    print("\n--- The Paradox ---")
    print("Backward induction says Player 1 should Take at node 0.")
    print("But if both reach the end, they both get much more!")
    print(f"  BI outcome: ({payoffs[first_take][0]:.1f}, {payoffs[first_take][1]:.1f})")
    print(f"  Cooperation: ({payoffs[-1][0]:.1f}, {payoffs[-1][1]:.1f})")

    # Experimental simulation
    print("\n--- Simulated Experimental Play ---")
    n_simulations = 1000
    results = [simulate_experimental_play(n_rounds, take_probability=0.15)
               for _ in range(n_simulations)]

    avg_ending = np.mean([r[0] for r in results])
    avg_p1 = np.mean([r[1] for r in results])
    avg_p2 = np.mean([r[2] for r in results])

    print(f"Over {n_simulations} simulations (take_prob=0.15):")
    print(f"  Average ending node: {avg_ending:.2f}")
    print(f"  Average P1 payoff: {avg_p1:.2f}")
    print(f"  Average P2 payoff: {avg_p2:.2f}")


if __name__ == "__main__":
    main()
