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
    shapley_value_formula,
    shapley_value_with_variance,
    marginal_contribution,
    shapley_decomposition,
    ShapleyCalculator
)
from .core import (
    compute_core,
    is_in_core,
    core_constraints,
    core_vertices_2d,
    core_vertices_3d,
    bondareva_shapley_condition
)
from .french_politics import (
    FrenchLeftCoalition2024,
    get_2024_legislative_data,
    analyze_coalition_dynamics,
    PARTIES_2024,
    scenario_analysis,
    compare_value_functions,
    analyze_barrage_effect,
    analyze_center_transfers,
    compare_model_vs_reality,
    SECOND_ROUND_RESULTS,
    TRANSFERS_TO_NFP,
    TRANSFERS_TO_ENSEMBLE,
    TRANSFERS_TO_RN
)
from .assistance_games import (
    paperclip_game_equilibrium,
    paperclip_payoff_analysis,
    paperclip_print_analysis,
    off_switch_game,
    off_switch_analysis,
    AssistanceGame,
    paperclip_vs_coordination_comparison,
    PaperclipGameResult,
    OffSwitchGameResult
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
    "shapley_value_formula",
    "shapley_value_with_variance",
    "marginal_contribution",
    "shapley_decomposition",
    "ShapleyCalculator",
    # Core
    "compute_core",
    "is_in_core",
    "core_constraints",
    "core_vertices_2d",
    "core_vertices_3d",
    "bondareva_shapley_condition",
    # French politics
    "FrenchLeftCoalition2024",
    "get_2024_legislative_data",
    "analyze_coalition_dynamics",
    "PARTIES_2024",
    "scenario_analysis",
    "compare_value_functions",
    "analyze_barrage_effect",
    "analyze_center_transfers",
    "compare_model_vs_reality",
    "SECOND_ROUND_RESULTS",
    "TRANSFERS_TO_NFP",
    "TRANSFERS_TO_ENSEMBLE",
    "TRANSFERS_TO_RN",
    # Assistance games (AI Safety)
    "paperclip_game_equilibrium",
    "paperclip_payoff_analysis",
    "paperclip_print_analysis",
    "off_switch_game",
    "off_switch_analysis",
    "AssistanceGame",
    "paperclip_vs_coordination_comparison",
    "PaperclipGameResult",
    "OffSwitchGameResult",
]
