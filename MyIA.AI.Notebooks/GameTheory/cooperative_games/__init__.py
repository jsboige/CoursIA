"""
Cooperative Game Theory Module
==============================

This module provides tools for analyzing cooperative games:
- Shapley value computation (exact and Monte Carlo)
- Core computation via Linear Programming
- Coalition game structures
- French political coalition example (2024 data)

Main classes:
- CoalitionGame: Base class for cooperative games
- VotingGame: Weighted voting games
- ShapleyCalculator: Exact and approximate Shapley values

Example usage:
    from cooperative_games import CoalitionGame, shapley_value_exact

    # Define a simple 3-player majority game
    def v(coalition):
        return 1.0 if len(coalition) >= 2 else 0.0

    game = CoalitionGame(n_players=3, characteristic_function=v)
    shapley = shapley_value_exact(game)
    print(f"Shapley values: {shapley}")
"""

from .coalition_games import CoalitionGame, VotingGame, WeightedVotingGame
from .shapley import (
    shapley_value_exact,
    shapley_value_monte_carlo,
    marginal_contribution,
    ShapleyCalculator
)
from .core import compute_core, is_in_core, core_constraints
from .french_politics import (
    FrenchLeftCoalition2024,
    get_2024_legislative_data,
    analyze_coalition_dynamics
)

__version__ = "1.0.0"
__all__ = [
    # Coalition games
    "CoalitionGame",
    "VotingGame",
    "WeightedVotingGame",
    # Shapley
    "shapley_value_exact",
    "shapley_value_monte_carlo",
    "marginal_contribution",
    "ShapleyCalculator",
    # Core
    "compute_core",
    "is_in_core",
    "core_constraints",
    # French politics
    "FrenchLeftCoalition2024",
    "get_2024_legislative_data",
    "analyze_coalition_dynamics",
]
