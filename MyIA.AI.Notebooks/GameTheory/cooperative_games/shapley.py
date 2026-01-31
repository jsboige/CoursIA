"""
Shapley Value Computation
=========================

The Shapley value is the unique solution concept satisfying:
1. Efficiency: Sum of Shapley values = v(N)
2. Symmetry: Symmetric players get equal values
3. Null player: Players with zero marginal contribution get zero
4. Additivity: phi(v + w) = phi(v) + phi(w)

Formula:
    phi_i(v) = Sum over S in N without i of [|S|!(n-|S|-1)!/n!] * [v(S + i) - v(S)]

This module provides:
- Exact computation (O(n! * 2^n) - only for small n)
- Monte Carlo approximation (O(samples * n))
- Marginal contribution analysis
"""

from typing import Set, List, Optional, Callable
from itertools import permutations, combinations
import math
import numpy as np
from .coalition_games import CoalitionGame


def marginal_contribution(
    game: CoalitionGame,
    player: int,
    coalition: Set[int]
) -> float:
    """
    Compute the marginal contribution of a player to a coalition.

    Args:
        game: The cooperative game
        player: Player index
        coalition: Coalition not containing the player

    Returns:
        v(S ∪ {i}) - v(S)
    """
    return game.marginal_contribution(player, coalition)


def shapley_value_exact(game: CoalitionGame) -> np.ndarray:
    """
    Compute exact Shapley values using the permutation formula.

    The Shapley value for player i is the average marginal contribution
    of i over all possible orderings of players.

    Complexity: O(n! · n) - only practical for n <= 10

    Args:
        game: The cooperative game

    Returns:
        Array of Shapley values for each player

    Example:
        >>> game = VotingGame(3, quota=2)  # Majority game
        >>> shapley = shapley_value_exact(game)
        >>> shapley  # All players equal: [1/3, 1/3, 1/3]
    """
    n = game.n_players
    shapley = np.zeros(n)
    num_perms = 0

    for perm in permutations(range(n)):
        coalition = set()
        for i in perm:
            mc = game.value(coalition | {i}) - game.value(coalition)
            shapley[i] += mc
            coalition.add(i)
        num_perms += 1

    return shapley / num_perms


def shapley_value_formula(game: CoalitionGame) -> np.ndarray:
    """
    Compute Shapley values using the coalition-based formula.

    phi_i = Sum over S in N without i of [|S|!(n-|S|-1)!/n!] * [v(S + i) - v(S)]

    Complexity: O(2^n * n) - faster than permutation for n > 6

    Args:
        game: The cooperative game

    Returns:
        Array of Shapley values
    """
    n = game.n_players
    shapley = np.zeros(n)
    factorial_n = math.factorial(n)

    for i in range(n):
        # Sum over all coalitions not containing i
        other_players = [j for j in range(n) if j != i]

        for s_size in range(n):
            weight = math.factorial(s_size) * math.factorial(n - s_size - 1) / factorial_n

            for s in combinations(other_players, s_size):
                s_set = set(s)
                mc = game.value(s_set | {i}) - game.value(s_set)
                shapley[i] += weight * mc

    return shapley


def shapley_value_monte_carlo(
    game: CoalitionGame,
    n_samples: int = 10000,
    seed: Optional[int] = None
) -> np.ndarray:
    """
    Approximate Shapley values using Monte Carlo sampling.

    Randomly samples permutations and averages marginal contributions.
    Provides unbiased estimates with variance decreasing as O(1/sqrt(samples)).

    Complexity: O(samples · n)

    Args:
        game: The cooperative game
        n_samples: Number of random permutations to sample
        seed: Random seed for reproducibility

    Returns:
        Array of approximate Shapley values

    Example:
        >>> game = WeightedVotingGame([10, 5, 3, 2], quota=11)
        >>> shapley = shapley_value_monte_carlo(game, n_samples=50000)
    """
    if seed is not None:
        np.random.seed(seed)

    n = game.n_players
    shapley = np.zeros(n)

    for _ in range(n_samples):
        perm = np.random.permutation(n)
        coalition = set()
        for i in perm:
            mc = game.value(coalition | {i}) - game.value(coalition)
            shapley[i] += mc
            coalition.add(i)

    return shapley / n_samples


def shapley_value_with_variance(
    game: CoalitionGame,
    n_samples: int = 10000,
    seed: Optional[int] = None
) -> tuple:
    """
    Compute Monte Carlo Shapley values with variance estimates.

    Args:
        game: The cooperative game
        n_samples: Number of samples
        seed: Random seed

    Returns:
        Tuple of (shapley_values, standard_errors)
    """
    if seed is not None:
        np.random.seed(seed)

    n = game.n_players
    contributions = np.zeros((n_samples, n))

    for sample_idx in range(n_samples):
        perm = np.random.permutation(n)
        coalition = set()
        for i in perm:
            mc = game.value(coalition | {i}) - game.value(coalition)
            contributions[sample_idx, i] = mc
            coalition.add(i)

    shapley = contributions.mean(axis=0)
    std_errors = contributions.std(axis=0) / np.sqrt(n_samples)

    return shapley, std_errors


class ShapleyCalculator:
    """
    Unified interface for Shapley value computation.

    Automatically chooses between exact and Monte Carlo methods
    based on problem size.

    Attributes:
        game: The cooperative game
        method: 'exact', 'formula', 'monte_carlo', or 'auto'
        n_samples: Number of samples for Monte Carlo

    Example:
        >>> calc = ShapleyCalculator(game, method='auto')
        >>> values = calc.compute()
        >>> print(calc.summary())
    """

    # Threshold for switching to Monte Carlo
    EXACT_THRESHOLD = 10

    def __init__(
        self,
        game: CoalitionGame,
        method: str = 'auto',
        n_samples: int = 10000,
        seed: Optional[int] = None
    ):
        """
        Initialize the Shapley calculator.

        Args:
            game: The cooperative game
            method: 'exact', 'formula', 'monte_carlo', or 'auto'
            n_samples: Samples for Monte Carlo
            seed: Random seed
        """
        self.game = game
        self.method = method
        self.n_samples = n_samples
        self.seed = seed
        self._values: Optional[np.ndarray] = None
        self._std_errors: Optional[np.ndarray] = None
        self._method_used: Optional[str] = None

    def compute(self) -> np.ndarray:
        """Compute Shapley values using the configured method."""
        method = self.method

        if method == 'auto':
            if self.game.n_players <= self.EXACT_THRESHOLD:
                method = 'formula'
            else:
                method = 'monte_carlo'

        self._method_used = method

        if method == 'exact':
            self._values = shapley_value_exact(self.game)
        elif method == 'formula':
            self._values = shapley_value_formula(self.game)
        elif method == 'monte_carlo':
            self._values, self._std_errors = shapley_value_with_variance(
                self.game, self.n_samples, self.seed
            )
        else:
            raise ValueError(f"Unknown method: {method}")

        return self._values

    @property
    def values(self) -> np.ndarray:
        """Get computed Shapley values (compute if needed)."""
        if self._values is None:
            self.compute()
        return self._values

    @property
    def standard_errors(self) -> Optional[np.ndarray]:
        """Get standard errors (only for Monte Carlo)."""
        return self._std_errors

    def summary(self) -> str:
        """Generate a summary of Shapley values."""
        if self._values is None:
            self.compute()

        lines = [
            f"Shapley Value Analysis",
            f"=" * 50,
            f"Game: {self.game}",
            f"Method: {self._method_used}",
            f"Grand coalition value: {self.game.grand_coalition_value():.4f}",
            f"",
            f"Player Shapley Values:",
        ]

        for i, name in enumerate(self.game.player_names):
            value = self._values[i]
            if self._std_errors is not None:
                lines.append(f"  {name}: {value:.4f} ± {self._std_errors[i]:.4f}")
            else:
                lines.append(f"  {name}: {value:.4f}")

        lines.append(f"")
        lines.append(f"Sum of Shapley values: {self._values.sum():.4f}")
        lines.append(f"Efficiency check: {np.isclose(self._values.sum(), self.game.grand_coalition_value())}")

        return "\n".join(lines)

    def to_dict(self) -> dict:
        """Export results as a dictionary."""
        if self._values is None:
            self.compute()

        result = {
            "player_names": self.game.player_names,
            "shapley_values": self._values.tolist(),
            "grand_coalition_value": self.game.grand_coalition_value(),
            "method": self._method_used,
        }

        if self._std_errors is not None:
            result["standard_errors"] = self._std_errors.tolist()

        return result


def shapley_decomposition(
    game: CoalitionGame,
    player: int
) -> dict:
    """
    Decompose a player's Shapley value by coalition size.

    Shows how much each coalition size contributes to the
    player's total Shapley value.

    Args:
        game: The cooperative game
        player: Player index

    Returns:
        Dictionary with 'by_size' (contributions by coalition size)
        and 'total' (final Shapley value)
    """
    n = game.n_players
    contributions_by_size = np.zeros(n)
    factorial_n = math.factorial(n)

    other_players = [j for j in range(n) if j != player]

    for s_size in range(n):
        weight = math.factorial(s_size) * math.factorial(n - s_size - 1) / factorial_n

        for s in combinations(other_players, s_size):
            s_set = set(s)
            mc = game.value(s_set | {player}) - game.value(s_set)
            contributions_by_size[s_size] += weight * mc

    return {
        "by_size": contributions_by_size,
        "total": contributions_by_size.sum(),
        "player": player,
        "player_name": game.player_names[player]
    }
