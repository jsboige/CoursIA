"""
Coalition Games - Base Classes
==============================

Provides fundamental structures for cooperative game theory:
- CoalitionGame: General cooperative game with characteristic function
- VotingGame: Simple voting games (quota-based)
- WeightedVotingGame: Weighted voting with player weights

A cooperative game is defined by:
- N: Set of players {1, 2, ..., n}
- v: Characteristic function v: 2^N -> R
  where v(S) represents the value coalition S can achieve

Key concepts:
- Grand coalition: N (all players)
- Empty coalition: {} with v({}) = 0
- Superadditivity: v(S ∪ T) >= v(S) + v(T) for disjoint S, T
- Convexity: v(S ∪ {i}) - v(S) <= v(T ∪ {i}) - v(T) for S ⊆ T
"""

from typing import Callable, Set, FrozenSet, List, Dict, Optional, Union
from itertools import combinations
import numpy as np


class CoalitionGame:
    """
    Base class for cooperative games with transferable utility (TU games).

    A TU game is defined by a set of players and a characteristic function
    that assigns a value to each coalition.

    Attributes:
        n_players: Number of players
        player_names: Optional names for players
        _v: Characteristic function (cached)

    Example:
        >>> def v(S): return len(S) ** 2  # Superadditive game
        >>> game = CoalitionGame(3, v)
        >>> game.value({0, 1})  # Value of coalition {0, 1}
        4
    """

    def __init__(
        self,
        n_players: int,
        characteristic_function: Callable[[Set[int]], float],
        player_names: Optional[List[str]] = None
    ):
        """
        Initialize a cooperative game.

        Args:
            n_players: Number of players (indexed 0 to n-1)
            characteristic_function: Function v(S) -> value for coalition S
            player_names: Optional list of player names
        """
        self.n_players = n_players
        self._characteristic_function = characteristic_function
        self.player_names = player_names or [f"Player_{i}" for i in range(n_players)]

        # Cache for computed values
        self._value_cache: Dict[FrozenSet[int], float] = {}

        # Ensure v(empty) = 0
        empty_value = self._characteristic_function(set())
        if empty_value != 0:
            raise ValueError(f"Characteristic function must satisfy v(∅) = 0, got {empty_value}")

    def value(self, coalition: Union[Set[int], FrozenSet[int], List[int]]) -> float:
        """
        Get the value of a coalition.

        Args:
            coalition: Set of player indices

        Returns:
            Value v(S) for the coalition
        """
        if isinstance(coalition, list):
            coalition = frozenset(coalition)
        elif isinstance(coalition, set):
            coalition = frozenset(coalition)

        if coalition not in self._value_cache:
            self._value_cache[coalition] = self._characteristic_function(set(coalition))

        return self._value_cache[coalition]

    def grand_coalition_value(self) -> float:
        """Value of the grand coalition (all players)."""
        return self.value(set(range(self.n_players)))

    def all_coalitions(self) -> List[FrozenSet[int]]:
        """Generate all possible coalitions (2^n subsets)."""
        coalitions = []
        for size in range(self.n_players + 1):
            for combo in combinations(range(self.n_players), size):
                coalitions.append(frozenset(combo))
        return coalitions

    def is_superadditive(self) -> bool:
        """
        Check if the game is superadditive.

        A game is superadditive if v(S ∪ T) >= v(S) + v(T)
        for all disjoint coalitions S and T.
        """
        players = set(range(self.n_players))
        for s_size in range(1, self.n_players):
            for s in combinations(range(self.n_players), s_size):
                s_set = set(s)
                remaining = players - s_set
                for t_size in range(1, len(remaining) + 1):
                    for t in combinations(remaining, t_size):
                        t_set = set(t)
                        if self.value(s_set | t_set) < self.value(s_set) + self.value(t_set) - 1e-10:
                            return False
        return True

    def is_convex(self) -> bool:
        """
        Check if the game is convex (supermodular).

        A game is convex if for all S ⊆ T and all i ∉ T:
        v(S ∪ {i}) - v(S) <= v(T ∪ {i}) - v(T)

        Convex games have nice properties: Shapley value is in the core.
        """
        for i in range(self.n_players):
            for t_size in range(1, self.n_players):
                for t in combinations([j for j in range(self.n_players) if j != i], t_size):
                    t_set = set(t)
                    for s_size in range(t_size):
                        for s in combinations(t, s_size):
                            s_set = set(s)
                            mc_s = self.value(s_set | {i}) - self.value(s_set)
                            mc_t = self.value(t_set | {i}) - self.value(t_set)
                            if mc_s > mc_t + 1e-10:
                                return False
        return True

    def marginal_contribution(self, player: int, coalition: Set[int]) -> float:
        """
        Compute the marginal contribution of a player to a coalition.

        Args:
            player: Player index
            coalition: Coalition (not containing player)

        Returns:
            v(S ∪ {i}) - v(S)
        """
        if player in coalition:
            raise ValueError(f"Player {player} already in coalition {coalition}")
        return self.value(coalition | {player}) - self.value(coalition)

    def __repr__(self) -> str:
        return f"CoalitionGame(n_players={self.n_players}, v(N)={self.grand_coalition_value():.2f})"


class VotingGame(CoalitionGame):
    """
    Simple voting game with a quota.

    A coalition wins (value 1) if it has at least 'quota' members,
    otherwise it loses (value 0).

    Example:
        >>> # Majority game with 3 players
        >>> game = VotingGame(n_players=3, quota=2)
        >>> game.value({0, 1})  # Coalition of 2 wins
        1.0
        >>> game.value({0})  # Single player loses
        0.0
    """

    def __init__(
        self,
        n_players: int,
        quota: int,
        player_names: Optional[List[str]] = None
    ):
        """
        Initialize a simple voting game.

        Args:
            n_players: Number of voters
            quota: Minimum coalition size to win
            player_names: Optional voter names
        """
        self.quota = quota

        def v(coalition: Set[int]) -> float:
            return 1.0 if len(coalition) >= quota else 0.0

        super().__init__(n_players, v, player_names)

    def __repr__(self) -> str:
        return f"VotingGame(n_players={self.n_players}, quota={self.quota})"


class WeightedVotingGame(CoalitionGame):
    """
    Weighted voting game [q; w1, w2, ..., wn].

    Each player i has a weight w_i. A coalition S wins if
    the sum of weights exceeds the quota q.

    Common examples:
    - UN Security Council: [39; 7,7,7,7,7, 1,1,1,1,1,1,1,1,1,1]
    - EU Council of Ministers: Various weighted voting schemes
    - Shareholder voting: Weights = number of shares

    Example:
        >>> # [3; 2, 1, 1] - Player 0 has veto power
        >>> game = WeightedVotingGame(weights=[2, 1, 1], quota=3)
        >>> game.value({0, 1})  # Weight 3 >= quota 3
        1.0
        >>> game.value({1, 2})  # Weight 2 < quota 3
        0.0
    """

    def __init__(
        self,
        weights: List[float],
        quota: float,
        player_names: Optional[List[str]] = None
    ):
        """
        Initialize a weighted voting game.

        Args:
            weights: List of player weights [w1, w2, ..., wn]
            quota: Minimum total weight to win
            player_names: Optional player names
        """
        self.weights = np.array(weights)
        self.quota = quota

        def v(coalition: Set[int]) -> float:
            if not coalition:
                return 0.0
            total_weight = sum(self.weights[i] for i in coalition)
            return 1.0 if total_weight >= quota else 0.0

        super().__init__(len(weights), v, player_names)

    def is_winning(self, coalition: Set[int]) -> bool:
        """Check if a coalition is winning."""
        return self.value(coalition) >= 1.0

    def is_minimal_winning(self, coalition: Set[int]) -> bool:
        """
        Check if a coalition is minimal winning.

        A coalition is minimal winning if it wins but removing
        any single member makes it losing.
        """
        if not self.is_winning(coalition):
            return False
        for player in coalition:
            if self.is_winning(coalition - {player}):
                return False
        return True

    def minimal_winning_coalitions(self) -> List[Set[int]]:
        """Find all minimal winning coalitions."""
        mwc = []
        for coalition in self.all_coalitions():
            if self.is_minimal_winning(set(coalition)):
                mwc.append(set(coalition))
        return mwc

    def is_veto_player(self, player: int) -> bool:
        """
        Check if a player has veto power.

        A player has veto power if they are in every winning coalition.
        """
        for coalition in self.all_coalitions():
            if player not in coalition and self.is_winning(set(coalition)):
                return False
        return True

    def is_dictator(self, player: int) -> bool:
        """
        Check if a player is a dictator.

        A player is a dictator if they can win alone and
        no other coalition without them can win.
        """
        # Can win alone
        if not self.is_winning({player}):
            return False
        # No other coalition without them can win
        for coalition in self.all_coalitions():
            if player not in coalition and self.is_winning(set(coalition)):
                return False
        return True

    def is_dummy(self, player: int) -> bool:
        """
        Check if a player is a dummy (null player).

        A player is a dummy if their marginal contribution is 0
        for all coalitions (they never make a difference).
        """
        for coalition in self.all_coalitions():
            if player not in coalition:
                mc = self.marginal_contribution(player, set(coalition))
                if mc > 1e-10:
                    return False
        return True

    def banzhaf_index(self) -> np.ndarray:
        """
        Compute the Banzhaf power index for all players.

        The Banzhaf index counts the number of times a player
        is critical (their removal changes a winning coalition to losing),
        normalized by total critical counts.

        Returns:
            Array of Banzhaf indices (sum = 1)
        """
        critical_counts = np.zeros(self.n_players)

        for coalition in self.all_coalitions():
            if self.is_winning(set(coalition)):
                for player in coalition:
                    # Check if player is critical
                    if not self.is_winning(set(coalition) - {player}):
                        critical_counts[player] += 1

        total = critical_counts.sum()
        if total == 0:
            return np.ones(self.n_players) / self.n_players
        return critical_counts / total

    def __repr__(self) -> str:
        weights_str = ", ".join(f"{w:.1f}" for w in self.weights)
        return f"WeightedVotingGame([{self.quota:.1f}; {weights_str}])"


# Convenience function for creating common games
def majority_game(n_players: int) -> VotingGame:
    """Create a simple majority voting game."""
    quota = (n_players // 2) + 1
    return VotingGame(n_players, quota)


def unanimity_game(n_players: int, required_players: Set[int]) -> CoalitionGame:
    """
    Create a unanimity game.

    A coalition wins if it contains all required players.

    Args:
        n_players: Total number of players
        required_players: Set of players that must all be present
    """
    def v(coalition: Set[int]) -> float:
        return 1.0 if required_players <= coalition else 0.0

    return CoalitionGame(n_players, v)
