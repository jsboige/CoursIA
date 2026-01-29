# -*- coding: utf-8 -*-
"""
Tournament System for Iterated Prisoner's Dilemma
=================================================

Implementation of Axelrod-style tournaments where strategies compete
in round-robin matches.

Features:
- Round-robin tournament execution
- Score tracking and ranking
- Support for custom payoff matrices
- Noise/error simulation
"""

from typing import List, Type, Dict, Optional
import numpy as np
from dataclasses import dataclass
from .strategies import Strategy, play_match, ALL_STRATEGIES


@dataclass
class MatchResult:
    """Result of a single match between two strategies."""
    player1: str
    player2: str
    score1: float
    score2: float
    rounds: int


@dataclass
class TournamentResults:
    """Complete results of a tournament."""
    strategies: List[str]
    scores: Dict[str, float]
    match_results: List[MatchResult]
    rankings: List[tuple]  # List of (strategy_name, total_score)

    def __repr__(self):
        lines = ["Tournament Results:", "=" * 40]
        for i, (name, score) in enumerate(self.rankings, 1):
            lines.append(f"{i}. {name}: {score:.1f}")
        return "\n".join(lines)


class Tournament:
    """
    Axelrod-style tournament for IPD strategies.

    Each strategy plays against every other strategy (including itself)
    in a round-robin format. The strategy with the highest total score wins.
    """

    def __init__(
        self,
        strategies: List[Type[Strategy]] = None,
        rounds_per_match: int = 200,
        repetitions: int = 1,
        noise: float = 0.0,
    ):
        """
        Initialize tournament.

        Args:
            strategies: List of Strategy classes to compete
            rounds_per_match: Number of rounds per match
            repetitions: Number of times to repeat each match (for averaging)
            noise: Probability of action being flipped (for noisy environments)
        """
        self.strategy_classes = strategies or ALL_STRATEGIES
        self.rounds_per_match = rounds_per_match
        self.repetitions = repetitions
        self.noise = noise
        self.results: Optional[TournamentResults] = None

    def run(self) -> TournamentResults:
        """
        Run the tournament.

        Returns:
            TournamentResults with scores and rankings
        """
        # Initialize strategies
        strategies = [cls() for cls in self.strategy_classes]
        n = len(strategies)

        # Track scores
        scores = {s.name: 0.0 for s in strategies}
        match_results = []

        # Round-robin: each pair plays
        for i in range(n):
            for j in range(n):  # Include self-play
                total1, total2 = 0.0, 0.0

                for _ in range(self.repetitions):
                    result = play_match(
                        strategies[i],
                        strategies[j],
                        rounds=self.rounds_per_match
                    )
                    total1 += result["score1"]
                    total2 += result["score2"]

                avg1 = total1 / self.repetitions
                avg2 = total2 / self.repetitions

                scores[strategies[i].name] += avg1

                if i != j:  # Don't double-count self-play
                    match_results.append(MatchResult(
                        player1=strategies[i].name,
                        player2=strategies[j].name,
                        score1=avg1,
                        score2=avg2,
                        rounds=self.rounds_per_match
                    ))

        # Create rankings
        rankings = sorted(scores.items(), key=lambda x: x[1], reverse=True)

        self.results = TournamentResults(
            strategies=[s.name for s in strategies],
            scores=scores,
            match_results=match_results,
            rankings=rankings
        )

        return self.results

    def get_payoff_matrix(self) -> np.ndarray:
        """
        Get the payoff matrix from tournament results.

        Returns:
            2D numpy array where entry [i,j] is strategy i's score vs strategy j
        """
        if self.results is None:
            raise ValueError("Run tournament first")

        n = len(self.results.strategies)
        matrix = np.zeros((n, n))

        name_to_idx = {name: i for i, name in enumerate(self.results.strategies)}

        for match in self.results.match_results:
            i = name_to_idx[match.player1]
            j = name_to_idx[match.player2]
            matrix[i, j] = match.score1

        return matrix


def run_axelrod_tournament(
    strategies: List[Type[Strategy]] = None,
    rounds: int = 200,
    show_results: bool = True
) -> TournamentResults:
    """
    Convenience function to run a standard Axelrod tournament.

    Args:
        strategies: Strategy classes to include (default: all)
        rounds: Rounds per match
        show_results: Whether to print results

    Returns:
        TournamentResults
    """
    tournament = Tournament(
        strategies=strategies,
        rounds_per_match=rounds
    )
    results = tournament.run()

    if show_results:
        print(results)

    return results


def ecological_simulation(
    strategies: List[Type[Strategy]] = None,
    initial_population: Dict[str, int] = None,
    generations: int = 100,
    rounds_per_match: int = 10,
) -> List[Dict[str, int]]:
    """
    Run an ecological simulation where populations evolve based on fitness.

    Each generation:
    1. Strategies play matches against each other
    2. Fitness = average score
    3. Population adjusts proportionally to fitness

    Args:
        strategies: Strategy classes
        initial_population: Starting population sizes
        generations: Number of generations
        rounds_per_match: Rounds per match

    Returns:
        History of population sizes per generation
    """
    if strategies is None:
        strategies = ALL_STRATEGIES

    # Initialize population
    if initial_population is None:
        initial_population = {cls().name: 100 for cls in strategies}

    population = initial_population.copy()
    history = [population.copy()]

    strategy_instances = {cls().name: cls for cls in strategies}

    for gen in range(generations):
        # Calculate fitness (average score weighted by opponent population)
        fitness = {name: 0.0 for name in population}
        total_pop = sum(population.values())

        if total_pop == 0:
            break

        for name1 in population:
            if population[name1] == 0:
                continue

            s1 = strategy_instances[name1]()

            for name2 in population:
                if population[name2] == 0:
                    continue

                s2 = strategy_instances[name2]()
                result = play_match(s1, s2, rounds=rounds_per_match)

                # Weight by opponent's population proportion
                weight = population[name2] / total_pop
                fitness[name1] += result["avg1"] * weight

        # Update population based on fitness
        total_fitness = sum(f * population[n] for n, f in fitness.items() if population[n] > 0)

        if total_fitness > 0:
            new_population = {}
            for name in population:
                if population[name] > 0 and fitness[name] > 0:
                    # Population grows proportionally to fitness
                    share = (fitness[name] * population[name]) / total_fitness
                    new_population[name] = max(0, int(total_pop * share))
                else:
                    new_population[name] = 0

            population = new_population

        history.append(population.copy())

    return history


def replicator_dynamics(
    payoff_matrix: np.ndarray,
    initial_proportions: np.ndarray,
    timesteps: int = 100,
    dt: float = 0.1,
) -> np.ndarray:
    """
    Simulate replicator dynamics for a given payoff matrix.

    The replicator equation: dx_i/dt = x_i * (f_i - avg_f)
    where f_i is fitness of strategy i and avg_f is average fitness.

    Args:
        payoff_matrix: n x n payoff matrix
        initial_proportions: Initial population proportions (sum to 1)
        timesteps: Number of simulation steps
        dt: Time step size

    Returns:
        Array of shape (timesteps, n) with population proportions over time
    """
    n = len(initial_proportions)
    x = initial_proportions.copy()
    history = [x.copy()]

    for _ in range(timesteps - 1):
        # Calculate fitness for each strategy
        fitness = payoff_matrix @ x

        # Average fitness
        avg_fitness = x @ fitness

        # Replicator dynamics update
        dx = x * (fitness - avg_fitness) * dt
        x = x + dx

        # Normalize to ensure proportions sum to 1
        x = np.maximum(x, 0)  # No negative populations
        x = x / x.sum()

        history.append(x.copy())

    return np.array(history)
