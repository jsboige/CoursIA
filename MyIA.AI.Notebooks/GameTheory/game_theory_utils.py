"""
Game Theory Utilities Module

This module provides shared classes and functions for the Game Theory notebook series.

Classes:
    - NormalFormGame: Representation of a normal form game
    - ZeroSumGame: Zero-sum two-player game
    - Strategy: Base class for IPD strategies
    - Tournament: Axelrod-style tournament runner

Functions:
    - find_pure_nash: Find pure Nash equilibria
    - find_mixed_nash_2x2: Find mixed Nash equilibrium for 2x2 games
    - solve_minimax_lp: Solve zero-sum game via linear programming
    - play_match: Simulate IPD match between strategies
    - run_tournament: Run round-robin tournament
    - replicator_dynamics: Simulate population evolution

Author: CoursIA GameTheory Series
"""

import numpy as np
from scipy.optimize import linprog
from typing import List, Tuple, Dict, Optional, Callable
from dataclasses import dataclass
from abc import ABC, abstractmethod
from collections import defaultdict
import random


# =============================================================================
# CONSTANTS
# =============================================================================

# IPD Actions
COOPERATE = 'C'
DEFECT = 'D'

# IPD Payoff parameters (Axelrod convention)
T = 5  # Temptation
R = 3  # Reward
P = 1  # Punishment
S = 0  # Sucker


# =============================================================================
# NORMAL FORM GAMES
# =============================================================================

@dataclass
class NormalFormGame:
    """
    Representation of a two-player normal form game.

    Attributes:
        A: Payoff matrix for row player (m x n)
        B: Payoff matrix for column player (m x n)
        row_labels: Labels for row player's actions
        col_labels: Labels for column player's actions
        name: Name of the game
    """
    A: np.ndarray
    B: np.ndarray
    row_labels: List[str] = None
    col_labels: List[str] = None
    name: str = "Game"

    def __post_init__(self):
        self.A = np.array(self.A, dtype=float)
        self.B = np.array(self.B, dtype=float)
        self.m, self.n = self.A.shape

        if self.row_labels is None:
            self.row_labels = [f"R{i}" for i in range(self.m)]
        if self.col_labels is None:
            self.col_labels = [f"C{j}" for j in range(self.n)]

    def payoff(self, i: int, j: int) -> Tuple[float, float]:
        """Get payoffs for action profile (i, j)."""
        return self.A[i, j], self.B[i, j]

    def expected_payoff(self, sigma_row: np.ndarray, sigma_col: np.ndarray) -> Tuple[float, float]:
        """Get expected payoffs for mixed strategies."""
        u_row = sigma_row @ self.A @ sigma_col
        u_col = sigma_row @ self.B @ sigma_col
        return u_row, u_col

    def display(self):
        """Print the game in a readable format."""
        print(f"\n{self.name}")
        print("=" * 50)

        # Header
        header = "          " + "  ".join(f"{c:>12}" for c in self.col_labels)
        print(header)
        print("-" * len(header))

        # Rows
        for i, label in enumerate(self.row_labels):
            row_str = f"{label:>8}  "
            for j in range(self.n):
                row_str += f"({self.A[i,j]:>4.1f},{self.B[i,j]:>4.1f})  "
            print(row_str)


class ZeroSumGame:
    """
    Zero-sum two-player game where B = -A.

    Attributes:
        A: Payoff matrix for row player
        row_labels: Labels for row player's actions
        col_labels: Labels for column player's actions
        name: Name of the game
    """

    def __init__(self, A: np.ndarray,
                 row_labels: List[str] = None,
                 col_labels: List[str] = None,
                 name: str = "Zero-Sum Game"):
        self.A = np.array(A, dtype=float)
        self.m, self.n = self.A.shape
        self.name = name
        self.row_labels = row_labels or [f"R{i}" for i in range(self.m)]
        self.col_labels = col_labels or [f"C{j}" for j in range(self.n)]

    def payoff(self, sigma_row: np.ndarray, sigma_col: np.ndarray) -> float:
        """Get row player's payoff (= -col player's payoff)."""
        return sigma_row @ self.A @ sigma_col

    def display(self):
        """Print the game matrix."""
        print(f"\n{self.name} (Row player's payoffs)")
        print("=" * 50)

        header = "        " + "  ".join(f"{c:>8}" for c in self.col_labels)
        print(header)
        print("-" * len(header))

        for i, label in enumerate(self.row_labels):
            row_str = f"{label:>6}  "
            row_str += "  ".join(f"{self.A[i,j]:>8.2f}" for j in range(self.n))
            print(row_str)


# =============================================================================
# NASH EQUILIBRIUM FUNCTIONS
# =============================================================================

def find_pure_nash(game: NormalFormGame) -> List[Tuple[int, int]]:
    """
    Find all pure Nash equilibria by best response enumeration.

    Args:
        game: Normal form game

    Returns:
        List of (i, j) tuples representing pure Nash equilibria
    """
    equilibria = []

    for i in range(game.m):
        for j in range(game.n):
            # Is i a best response to j?
            row_br = all(game.A[i, j] >= game.A[k, j] for k in range(game.m))
            # Is j a best response to i?
            col_br = all(game.B[i, j] >= game.B[i, l] for l in range(game.n))

            if row_br and col_br:
                equilibria.append((i, j))

    return equilibria


def find_mixed_nash_2x2(game: NormalFormGame) -> Optional[Tuple[np.ndarray, np.ndarray]]:
    """
    Find the interior mixed Nash equilibrium of a 2x2 game.

    Uses the indifference condition: at equilibrium, each player is
    indifferent between their pure strategies.

    Args:
        game: 2x2 normal form game

    Returns:
        (sigma_row, sigma_col) or None if no interior equilibrium exists
    """
    if game.A.shape != (2, 2):
        raise ValueError("This function only works for 2x2 games")

    A, B = game.A, game.B

    # Indifference condition for Row:
    # A[0,0]*q + A[0,1]*(1-q) = A[1,0]*q + A[1,1]*(1-q)
    denom_q = A[0,0] - A[0,1] - A[1,0] + A[1,1]
    if abs(denom_q) < 1e-10:
        return None
    q = (A[1,1] - A[0,1]) / denom_q

    # Indifference condition for Col:
    # B[0,0]*p + B[1,0]*(1-p) = B[0,1]*p + B[1,1]*(1-p)
    denom_p = B[0,0] - B[1,0] - B[0,1] + B[1,1]
    if abs(denom_p) < 1e-10:
        return None
    p = (B[1,1] - B[1,0]) / denom_p

    # Check validity
    if 0 <= p <= 1 and 0 <= q <= 1:
        sigma_row = np.array([p, 1-p])
        sigma_col = np.array([q, 1-q])
        return sigma_row, sigma_col

    return None


# =============================================================================
# ZERO-SUM GAME SOLVERS
# =============================================================================

def solve_minimax_lp(game: ZeroSumGame) -> Tuple[np.ndarray, float]:
    """
    Solve a zero-sum game using linear programming.

    Finds the optimal mixed strategy for the row player and the game value.

    Args:
        game: Zero-sum game

    Returns:
        (optimal_strategy, game_value)
    """
    m, n = game.A.shape

    # Variables: [sigma_0, ..., sigma_{m-1}, v]
    # Objective: max v <=> min -v
    c = np.zeros(m + 1)
    c[-1] = -1

    # Constraints: A.T @ sigma >= v
    # Reformulated: -A.T @ sigma + v <= 0
    A_ub = np.zeros((n, m + 1))
    A_ub[:, :m] = -game.A.T
    A_ub[:, m] = 1
    b_ub = np.zeros(n)

    # Equality: sum(sigma) = 1
    A_eq = np.zeros((1, m + 1))
    A_eq[0, :m] = 1
    b_eq = np.array([1])

    # Bounds
    bounds = [(0, None) for _ in range(m)] + [(None, None)]

    result = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, bounds=bounds)

    if result.success:
        sigma = result.x[:m]
        v = result.x[m]
        return sigma, v
    else:
        raise ValueError(f"LP failed: {result.message}")


def maximin_pure(game: ZeroSumGame) -> Tuple[int, float]:
    """
    Find the pure maximin strategy for the row player.

    Returns:
        (action, maximin_value)
    """
    min_per_row = np.min(game.A, axis=1)
    best_row = np.argmax(min_per_row)
    return best_row, min_per_row[best_row]


def minimax_pure(game: ZeroSumGame) -> Tuple[int, float]:
    """
    Find the pure minimax strategy for the column player.

    Returns:
        (action, minimax_value)
    """
    max_per_col = np.max(game.A, axis=0)
    best_col = np.argmin(max_per_col)
    return best_col, max_per_col[best_col]


# =============================================================================
# IPD STRATEGIES
# =============================================================================

class Strategy(ABC):
    """
    Base class for Iterated Prisoner's Dilemma strategies.

    Subclasses must implement the choose() method.
    """

    def __init__(self, name: str = "Strategy"):
        self.name = name
        self.reset()

    def reset(self):
        """Reset internal state for a new match."""
        self.my_history: List[str] = []
        self.opponent_history: List[str] = []

    @abstractmethod
    def choose(self) -> str:
        """Choose an action based on history."""
        pass

    def update(self, my_action: str, opponent_action: str):
        """Update history after a round."""
        self.my_history.append(my_action)
        self.opponent_history.append(opponent_action)

    def __repr__(self):
        return self.name


class AlwaysCooperate(Strategy):
    """Always cooperate (Dove)."""
    def __init__(self):
        super().__init__("AlwaysCooperate")

    def choose(self) -> str:
        return COOPERATE


class AlwaysDefect(Strategy):
    """Always defect (Hawk)."""
    def __init__(self):
        super().__init__("AlwaysDefect")

    def choose(self) -> str:
        return DEFECT


class TitForTat(Strategy):
    """
    Tit-for-Tat: Cooperate first, then copy opponent's last move.
    Winner of Axelrod's tournament (1980).
    """
    def __init__(self):
        super().__init__("TitForTat")

    def choose(self) -> str:
        if not self.opponent_history:
            return COOPERATE
        return self.opponent_history[-1]


class TitForTwoTats(Strategy):
    """
    Tit-for-Two-Tats: Only defect after two consecutive defections.
    More forgiving than TFT.
    """
    def __init__(self):
        super().__init__("TitForTwoTats")

    def choose(self) -> str:
        if len(self.opponent_history) < 2:
            return COOPERATE
        if self.opponent_history[-1] == DEFECT and self.opponent_history[-2] == DEFECT:
            return DEFECT
        return COOPERATE


class Grudger(Strategy):
    """
    Grudger (Grim Trigger): Cooperate until first defection, then never forgive.
    """
    def __init__(self):
        super().__init__("Grudger")
        self.betrayed = False

    def reset(self):
        super().reset()
        self.betrayed = False

    def choose(self) -> str:
        return DEFECT if self.betrayed else COOPERATE

    def update(self, my_action: str, opponent_action: str):
        super().update(my_action, opponent_action)
        if opponent_action == DEFECT:
            self.betrayed = True


class RandomStrategy(Strategy):
    """Random strategy with probability p of cooperation."""
    def __init__(self, p: float = 0.5):
        super().__init__(f"Random(p={p})")
        self.p = p

    def choose(self) -> str:
        return COOPERATE if random.random() < self.p else DEFECT


# =============================================================================
# IPD TOURNAMENT
# =============================================================================

def ipd_payoff(action1: str, action2: str) -> Tuple[int, int]:
    """
    Get IPD payoffs for a pair of actions.

    Returns:
        (payoff_player1, payoff_player2)
    """
    if action1 == COOPERATE and action2 == COOPERATE:
        return (R, R)
    elif action1 == COOPERATE and action2 == DEFECT:
        return (S, T)
    elif action1 == DEFECT and action2 == COOPERATE:
        return (T, S)
    else:
        return (P, P)


def play_match(strategy1: Strategy, strategy2: Strategy,
               rounds: int = 200, noise: float = 0.0) -> Tuple[int, int]:
    """
    Simulate an IPD match between two strategies.

    Args:
        strategy1, strategy2: The two strategies
        rounds: Number of rounds
        noise: Probability of action being flipped (error)

    Returns:
        (score1, score2)
    """
    strategy1.reset()
    strategy2.reset()

    score1, score2 = 0, 0

    for _ in range(rounds):
        action1 = strategy1.choose()
        action2 = strategy2.choose()

        # Apply noise
        if noise > 0:
            if random.random() < noise:
                action1 = DEFECT if action1 == COOPERATE else COOPERATE
            if random.random() < noise:
                action2 = DEFECT if action2 == COOPERATE else COOPERATE

        p1, p2 = ipd_payoff(action1, action2)
        score1 += p1
        score2 += p2

        strategy1.update(action1, action2)
        strategy2.update(action2, action1)

    return score1, score2


def run_tournament(strategies: List[Strategy],
                   rounds: int = 200,
                   noise: float = 0.0,
                   repetitions: int = 1) -> Dict[str, float]:
    """
    Run a round-robin tournament.

    Args:
        strategies: List of strategies
        rounds: Rounds per match
        noise: Error probability
        repetitions: Number of repetitions (useful with noise)

    Returns:
        Dictionary {strategy_name: average_score_per_match}
    """
    n = len(strategies)
    scores = defaultdict(float)
    match_count = defaultdict(int)

    for _ in range(repetitions):
        for i in range(n):
            for j in range(n):
                s1 = type(strategies[i])()
                s2 = type(strategies[j])()

                score1, score2 = play_match(s1, s2, rounds, noise)

                scores[strategies[i].name] += score1
                scores[strategies[j].name] += score2
                match_count[strategies[i].name] += 1
                match_count[strategies[j].name] += 1

    return {name: scores[name] / match_count[name] for name in scores}


# =============================================================================
# REPLICATOR DYNAMICS
# =============================================================================

def compute_payoff_matrix(strategies: List[Strategy], rounds: int = 200) -> np.ndarray:
    """
    Compute the payoff matrix between strategies.

    M[i,j] = average payoff per round for strategy i against strategy j
    """
    n = len(strategies)
    M = np.zeros((n, n))

    for i in range(n):
        for j in range(n):
            s1 = type(strategies[i])()
            s2 = type(strategies[j])()
            score1, _ = play_match(s1, s2, rounds)
            M[i, j] = score1 / rounds

    return M


def replicator_dynamics(M: np.ndarray, x0: np.ndarray,
                        T: int = 100, dt: float = 0.1) -> np.ndarray:
    """
    Simulate replicator dynamics.

    dx_i/dt = x_i * (fitness_i - average_fitness)

    Args:
        M: Payoff matrix
        x0: Initial population distribution
        T: Number of iterations
        dt: Time step

    Returns:
        Trajectory array (T x n)
    """
    n = len(x0)
    trajectory = np.zeros((T, n))
    x = x0.copy()

    for t in range(T):
        trajectory[t] = x

        fitness = M @ x
        avg_fitness = x @ fitness

        dx = x * (fitness - avg_fitness) * dt
        x = x + dx

        x = np.maximum(x, 0)
        x = x / np.sum(x)

    return trajectory


# =============================================================================
# UTILITY FUNCTIONS
# =============================================================================

def create_classic_games() -> Dict[str, NormalFormGame]:
    """
    Create a collection of classic 2x2 games.

    Returns:
        Dictionary of game name to NormalFormGame
    """
    games = {
        "Prisoner's Dilemma": NormalFormGame(
            A=[[3, 0], [5, 1]],
            B=[[3, 5], [0, 1]],
            row_labels=['Cooperate', 'Defect'],
            col_labels=['Cooperate', 'Defect'],
            name="Prisoner's Dilemma"
        ),
        "Stag Hunt": NormalFormGame(
            A=[[4, 0], [3, 3]],
            B=[[4, 3], [0, 3]],
            row_labels=['Stag', 'Hare'],
            col_labels=['Stag', 'Hare'],
            name="Stag Hunt"
        ),
        "Battle of the Sexes": NormalFormGame(
            A=[[3, 0], [0, 2]],
            B=[[2, 0], [0, 3]],
            row_labels=['Opera', 'Football'],
            col_labels=['Opera', 'Football'],
            name="Battle of the Sexes"
        ),
        "Chicken": NormalFormGame(
            A=[[0, -1], [1, -10]],
            B=[[0, 1], [-1, -10]],
            row_labels=['Swerve', 'Straight'],
            col_labels=['Swerve', 'Straight'],
            name="Chicken"
        ),
        "Matching Pennies": NormalFormGame(
            A=[[1, -1], [-1, 1]],
            B=[[-1, 1], [1, -1]],
            row_labels=['Heads', 'Tails'],
            col_labels=['Heads', 'Tails'],
            name="Matching Pennies"
        ),
    }
    return games


# =============================================================================
# EXTENSIVE FORM GAMES (Phase 2)
# =============================================================================

@dataclass
class GameNode:
    """
    Node in an extensive form game tree.

    Attributes:
        node_id: Unique identifier for this node
        player: Player to act (-1 for terminal, 0 for chance)
        actions: Available actions at this node
        children: Map from actions to child nodes
        payoffs: Payoffs at terminal nodes (tuple)
        infoset: Information set identifier
        chance_probs: Probabilities for chance nodes
    """
    node_id: str
    player: int  # -1 for terminal, 0 for chance
    actions: List[str] = None
    children: Dict[str, 'GameNode'] = None
    payoffs: Optional[Tuple[float, ...]] = None
    infoset: Optional[str] = None
    chance_probs: Optional[Dict[str, float]] = None

    def __post_init__(self):
        if self.actions is None:
            self.actions = []
        if self.children is None:
            self.children = {}

    def is_terminal(self) -> bool:
        """Check if this is a terminal node."""
        return self.player == -1

    def is_chance(self) -> bool:
        """Check if this is a chance node."""
        return self.player == 0


class ExtensiveFormGame:
    """
    Representation of an extensive form game.

    Attributes:
        name: Name of the game
        num_players: Number of players
        root: Root node of the game tree
        nodes: Dictionary of all nodes
        infosets: Mapping from infoset id to list of node ids
    """

    def __init__(self, name: str, num_players: int):
        self.name = name
        self.num_players = num_players
        self.root: Optional[GameNode] = None
        self.nodes: Dict[str, GameNode] = {}
        self.infosets: Dict[str, List[str]] = defaultdict(list)

    def add_node(self, node: GameNode):
        """Add a node to the game."""
        self.nodes[node.node_id] = node
        if node.infoset:
            self.infosets[node.infoset].append(node.node_id)

    def set_root(self, node: GameNode):
        """Set the root node."""
        self.root = node
        self.add_node(node)

    def get_terminal_nodes(self) -> List[GameNode]:
        """Get all terminal nodes."""
        return [n for n in self.nodes.values() if n.is_terminal()]

    def get_infoset_nodes(self, infoset_id: str) -> List[GameNode]:
        """Get all nodes in an information set."""
        return [self.nodes[nid] for nid in self.infosets[infoset_id]]

    def has_perfect_information(self) -> bool:
        """Check if the game has perfect information."""
        for infoset_id, nodes in self.infosets.items():
            if len(nodes) > 1:
                return False
        return True


def backward_induction(game: ExtensiveFormGame) -> Tuple[Dict[str, Tuple[str, Tuple]], Tuple]:
    """
    Solve a perfect information game by backward induction.

    Args:
        game: Extensive form game with perfect information

    Returns:
        (solution_dict, equilibrium_payoffs)
        solution_dict maps node_id to (optimal_action, payoffs_from_here)
    """
    solution = {}

    def solve(node: GameNode) -> Tuple[float, ...]:
        if node.is_terminal():
            return node.payoffs

        if node.is_chance():
            expected = np.zeros(game.num_players)
            for action, prob in node.chance_probs.items():
                child_payoffs = solve(node.children[action])
                expected += prob * np.array(child_payoffs)
            return tuple(expected)

        # Decision node: player maximizes their payoff
        player = node.player
        best_action = None
        best_payoffs = None
        best_value = float('-inf')

        for action in node.actions:
            child_payoffs = solve(node.children[action])
            player_value = child_payoffs[player - 1]  # 0-based index

            if player_value > best_value:
                best_value = player_value
                best_action = action
                best_payoffs = child_payoffs

        solution[node.node_id] = (best_action, best_payoffs)
        return best_payoffs

    equilibrium_payoffs = solve(game.root)
    return solution, equilibrium_payoffs


def create_entry_game() -> ExtensiveFormGame:
    """
    Create the classic entry game.

    Structure:
    - Entrant: Enter or Out
    - If Enter, Incumbent: Fight or Accommodate

    Payoffs: (Entrant, Incumbent)
    - Out: (0, 2)
    - Enter + Fight: (-1, -1)
    - Enter + Accommodate: (1, 1)
    """
    game = ExtensiveFormGame("Entry Game", num_players=2)

    out = GameNode("out", player=-1, payoffs=(0, 2))
    fight = GameNode("fight", player=-1, payoffs=(-1, -1))
    accommodate = GameNode("accommodate", player=-1, payoffs=(1, 1))

    incumbent = GameNode("incumbent", player=2, actions=["Fight", "Accommodate"], infoset="I2")
    incumbent.children = {"Fight": fight, "Accommodate": accommodate}

    entrant = GameNode("root", player=1, actions=["Enter", "Out"], infoset="I1")
    entrant.children = {"Enter": incumbent, "Out": out}

    game.set_root(entrant)
    for node in [incumbent, out, fight, accommodate]:
        game.add_node(node)

    return game


def create_centipede_game(n_rounds: int = 6) -> ExtensiveFormGame:
    """
    Create the centipede game.

    Players alternate, can Take (end game) or Pass (continue).
    Payoffs increase as the game continues.

    Args:
        n_rounds: Number of decision points

    Returns:
        Extensive form game
    """
    game = ExtensiveFormGame("Centipede", num_players=2)
    nodes = []

    def payoffs_at_round(t):
        # Classic centipede formulation:
        # - Taker gets big pile = t + 1
        # - Other gets small pile = max(0, t - 1)
        # This ensures backward induction predicts "everyone takes"
        big_pile = t + 1
        small_pile = max(0, t - 1)
        player = 1 if t % 2 == 0 else 2
        if player == 1:
            # P1 takes: P1 gets big, P2 gets small
            return (big_pile, small_pile)
        else:
            # P2 takes: P1 gets small, P2 gets big
            return (small_pile, big_pile)

    # Final node if everyone passes - equal split
    final_payoffs = (n_rounds, n_rounds)
    last_pass = GameNode("end", player=-1, payoffs=final_payoffs)
    nodes.append(last_pass)

    next_node = last_pass
    for t in range(n_rounds - 1, -1, -1):
        player = 1 if t % 2 == 0 else 2
        payoffs = payoffs_at_round(t)

        take_terminal = GameNode(f"take_{t}", player=-1, payoffs=payoffs)
        nodes.append(take_terminal)

        decision = GameNode(f"node_{t}", player=player,
                           actions=["Take", "Pass"], infoset=f"I{player}_{t}")
        decision.children = {"Take": take_terminal, "Pass": next_node}
        nodes.append(decision)

        next_node = decision

    game.set_root(next_node)
    for node in nodes[:-1]:
        game.add_node(node)

    return game


# =============================================================================
# PHASE 3: CFR AND IMPERFECT INFORMATION
# =============================================================================

class CFRSolver:
    """
    Counterfactual Regret Minimization solver for imperfect information games.

    This is a simplified version for small games like Kuhn Poker.
    """

    def __init__(self, num_actions: int = 2):
        self.num_actions = num_actions
        self.regret_sum: Dict[str, np.ndarray] = defaultdict(
            lambda: np.zeros(num_actions)
        )
        self.strategy_sum: Dict[str, np.ndarray] = defaultdict(
            lambda: np.zeros(num_actions)
        )
        self.iterations = 0

    def get_strategy(self, info_set: str) -> np.ndarray:
        """Get current strategy for an information set via regret matching."""
        regrets = self.regret_sum[info_set]
        positive_regrets = np.maximum(regrets, 0)
        normalizing_sum = positive_regrets.sum()

        if normalizing_sum > 0:
            return positive_regrets / normalizing_sum
        else:
            return np.ones(self.num_actions) / self.num_actions

    def get_average_strategy(self, info_set: str) -> np.ndarray:
        """Get average strategy (converges to Nash)."""
        strategy_sum = self.strategy_sum[info_set]
        normalizing_sum = strategy_sum.sum()

        if normalizing_sum > 0:
            return strategy_sum / normalizing_sum
        else:
            return np.ones(self.num_actions) / self.num_actions

    def update_regrets(self, info_set: str, regrets: np.ndarray,
                       reach_prob: float = 1.0):
        """Update cumulative regrets for an information set."""
        self.regret_sum[info_set] += regrets
        self.strategy_sum[info_set] += reach_prob * self.get_strategy(info_set)


# =============================================================================
# PHASE 3: STACKELBERG EQUILIBRIUM
# =============================================================================

def stackelberg_duopoly(a: float, b: float, c_L: float, c_F: float
                       ) -> Tuple[float, float, float, float]:
    """
    Compute Stackelberg equilibrium for linear duopoly.

    Demand: P(Q) = a - b*Q
    Costs: C_i(q) = c_i * q

    Args:
        a: Demand intercept
        b: Demand slope
        c_L: Leader's marginal cost
        c_F: Follower's marginal cost

    Returns:
        (q_leader, q_follower, profit_leader, profit_follower)
    """
    # Leader's optimal quantity
    q_L = (a - 2*c_L + c_F) / (2*b)
    q_L = max(0, q_L)

    # Follower's reaction
    q_F = (a - c_F - b*q_L) / (2*b)
    q_F = max(0, q_F)

    # Compute profits
    Q = q_L + q_F
    P = max(0, a - b*Q)
    pi_L = (P - c_L) * q_L
    pi_F = (P - c_F) * q_F

    return q_L, q_F, pi_L, pi_F


def cournot_duopoly(a: float, b: float, c1: float, c2: float
                   ) -> Tuple[float, float, float, float]:
    """
    Compute Cournot equilibrium for linear duopoly.

    Args:
        a: Demand intercept
        b: Demand slope
        c1, c2: Marginal costs

    Returns:
        (q1, q2, profit1, profit2)
    """
    q1 = (a - 2*c1 + c2) / (3*b)
    q2 = (a - 2*c2 + c1) / (3*b)
    q1, q2 = max(0, q1), max(0, q2)

    Q = q1 + q2
    P = max(0, a - b*Q)
    pi1 = (P - c1) * q1
    pi2 = (P - c2) * q2

    return q1, q2, pi1, pi2


# =============================================================================
# PHASE 3: MECHANISM DESIGN
# =============================================================================

class VCGAuction:
    """
    Vickrey-Clarke-Groves auction mechanism.

    Allocates items to highest bidders and charges externality-based payments.
    """

    def __init__(self, n_items: int = 1):
        self.n_items = n_items

    def allocate_single(self, bids: List[float]) -> Tuple[int, float]:
        """
        Single item allocation.

        Returns:
            (winner_index, payment)
        """
        if len(bids) < 2:
            return 0, 0.0

        sorted_indices = np.argsort(bids)[::-1]
        winner = sorted_indices[0]
        payment = bids[sorted_indices[1]]  # Second-price

        return winner, payment

    def allocate_multi(self, valuations: List[List[float]]
                      ) -> Tuple[List[List[float]], List[float]]:
        """
        Multi-item allocation with VCG payments.

        Args:
            valuations: valuations[i][j] = agent i's value for item j

        Returns:
            (allocations, payments)
        """
        n_agents = len(valuations)
        allocations = [[0.0] * self.n_items for _ in range(n_agents)]

        # Allocate each item to highest bidder
        for j in range(self.n_items):
            bids = [valuations[i][j] for i in range(n_agents)]
            winner = int(np.argmax(bids))
            allocations[winner][j] = 1.0

        # VCG payments
        payments = []
        for i in range(n_agents):
            # Social welfare of others with i present
            sw_others_with = sum(
                allocations[k][j] * valuations[k][j]
                for k in range(n_agents) if k != i
                for j in range(self.n_items)
            )

            # Social welfare of others without i
            valuations_without = [v for k, v in enumerate(valuations) if k != i]
            if valuations_without:
                alloc_without = [[0.0] * self.n_items for _ in range(len(valuations_without))]
                for j in range(self.n_items):
                    bids = [valuations_without[k][j] for k in range(len(valuations_without))]
                    winner = int(np.argmax(bids))
                    alloc_without[winner][j] = 1.0

                sw_others_without = sum(
                    alloc_without[k][j] * valuations_without[k][j]
                    for k in range(len(valuations_without))
                    for j in range(self.n_items)
                )
            else:
                sw_others_without = 0.0

            payments.append(sw_others_without - sw_others_with)

        return allocations, payments


def gale_shapley(proposer_prefs: Dict[str, List[str]],
                 receiver_prefs: Dict[str, List[str]]) -> Dict[str, str]:
    """
    Gale-Shapley deferred acceptance algorithm for stable matching.

    Args:
        proposer_prefs: Proposer -> ordered list of receivers
        receiver_prefs: Receiver -> ordered list of proposers

    Returns:
        Matching {proposer: receiver}
    """
    remaining_prefs = {p: list(prefs) for p, prefs in proposer_prefs.items()}
    free_proposers = list(proposer_prefs.keys())
    engaged = {}  # receiver -> proposer

    while free_proposers:
        proposer = free_proposers[0]

        if not remaining_prefs[proposer]:
            free_proposers.pop(0)
            continue

        receiver = remaining_prefs[proposer].pop(0)

        if receiver not in engaged:
            engaged[receiver] = proposer
            free_proposers.pop(0)
        else:
            current = engaged[receiver]
            r_prefs = receiver_prefs[receiver]
            if r_prefs.index(proposer) < r_prefs.index(current):
                engaged[receiver] = proposer
                free_proposers.pop(0)
                free_proposers.append(current)

    return {p: r for r, p in engaged.items()}


# =============================================================================
# PHASE 3: MULTI-AGENT LEARNING
# =============================================================================

class FictitiousPlay:
    """
    Fictitious Play algorithm for learning in games.

    Each player plays best response to empirical distribution of opponent.
    """

    def __init__(self, payoff_matrix: np.ndarray):
        """
        Initialize for a zero-sum matrix game.

        Args:
            payoff_matrix: Row player's payoffs
        """
        self.A = np.array(payoff_matrix)
        self.n_actions_p1 = self.A.shape[0]
        self.n_actions_p2 = self.A.shape[1]

        # Action counts (Laplace smoothing)
        self.counts_p1 = np.ones(self.n_actions_p1)
        self.counts_p2 = np.ones(self.n_actions_p2)

    def get_average_strategy(self, player: int) -> np.ndarray:
        """Get empirical strategy distribution."""
        if player == 0:
            return self.counts_p1 / self.counts_p1.sum()
        return self.counts_p2 / self.counts_p2.sum()

    def step(self):
        """One iteration of fictitious play."""
        avg_p1 = self.get_average_strategy(0)
        avg_p2 = self.get_average_strategy(1)

        # Best responses
        payoffs_p1 = self.A @ avg_p2
        action_p1 = np.argmax(payoffs_p1)

        payoffs_p2 = -self.A.T @ avg_p1  # Zero-sum
        action_p2 = np.argmax(payoffs_p2)

        self.counts_p1[action_p1] += 1
        self.counts_p2[action_p2] += 1

    def train(self, iterations: int):
        """Run fictitious play for n iterations."""
        for _ in range(iterations):
            self.step()

    def exploitability(self) -> float:
        """Compute exploitability of current average strategy."""
        avg_p1 = self.get_average_strategy(0)
        avg_p2 = self.get_average_strategy(1)

        # Best response gain for P1
        br_value_p1 = np.max(self.A @ avg_p2)
        current_value_p1 = avg_p1 @ self.A @ avg_p2
        gain_p1 = br_value_p1 - current_value_p1

        # Best response gain for P2
        br_value_p2 = np.max(-self.A.T @ avg_p1)
        current_value_p2 = -avg_p1 @ self.A @ avg_p2
        gain_p2 = br_value_p2 - current_value_p2

        return gain_p1 + gain_p2


def create_rps_matrix() -> np.ndarray:
    """Create Rock-Paper-Scissors payoff matrix."""
    return np.array([
        [0, -1, 1],
        [1, 0, -1],
        [-1, 1, 0]
    ])
