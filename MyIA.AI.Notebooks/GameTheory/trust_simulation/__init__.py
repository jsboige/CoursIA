# Trust Simulation Module
# Implementation of Axelrod's tournament and iterated prisoner's dilemma strategies
# Inspired by Nicky Case's "Evolution of Trust" (https://ncase.me/trust/)

from .strategies import (
    Strategy,
    AlwaysCooperate,
    AlwaysDefect,
    TitForTat,
    Copykitten,
    Grudger,
    Random,
    Pavlov,
    TitForTwoTats,
)
from .tournament import Tournament, run_axelrod_tournament
from .visualization import (
    plot_tournament_results,
    plot_population_dynamics,
    animate_replicator_dynamics,
)

__all__ = [
    # Strategies
    "Strategy",
    "AlwaysCooperate",
    "AlwaysDefect",
    "TitForTat",
    "Copykitten",
    "Grudger",
    "Random",
    "Pavlov",
    "TitForTwoTats",
    # Tournament
    "Tournament",
    "run_axelrod_tournament",
    # Visualization
    "plot_tournament_results",
    "plot_population_dynamics",
    "animate_replicator_dynamics",
]
