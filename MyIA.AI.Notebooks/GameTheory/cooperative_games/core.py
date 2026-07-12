"""
Core Computation for Cooperative Games
======================================

The Core is the set of allocations that no coalition can improve upon.

Definition:
    Core(v) = {x ∈ R^n : Σx_i = v(N) and Σ_{i∈S} x_i >= v(S) for all S ⊆ N}

Properties:
- May be empty (e.g., 3-player majority game)
- Always non-empty for convex games
- For convex games, Shapley value is in the Core

This module uses Linear Programming to:
- Check if the Core is non-empty
- Find a point in the Core (if it exists)
- Check if a specific allocation is in the Core
- Generate Core constraints for visualization
"""

from typing import List, Optional, Tuple, Set
import numpy as np
from scipy.optimize import linprog
from scipy.spatial import ConvexHull
from .coalition_games import CoalitionGame


def core_constraints(game: CoalitionGame) -> Tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    """
    Generate the LP constraints for the Core.

    The Core is defined by:
    - Efficiency: Σx_i = v(N)
    - Coalition rationality: Σ_{i∈S} x_i >= v(S) for all S ⊆ N

    Returns:
        Tuple of (A_ub, b_ub, A_eq, b_eq) for scipy.optimize.linprog
        where A_ub @ x <= b_ub and A_eq @ x == b_eq
    """
    n = game.n_players

    # Inequality constraints: -Σ_{i∈S} x_i <= -v(S) for all proper subsets S
    # (We negate because linprog uses <= form)
    inequalities = []
    rhs = []

    for coalition in game.all_coalitions():
        if len(coalition) > 0 and len(coalition) < n:  # Proper non-empty subsets
            row = np.zeros(n)
            for i in coalition:
                row[i] = -1  # Negate for <= form
            inequalities.append(row)
            rhs.append(-game.value(coalition))

    A_ub = np.array(inequalities) if inequalities else np.zeros((0, n))
    b_ub = np.array(rhs) if rhs else np.zeros(0)

    # Equality constraint: Σx_i = v(N)
    A_eq = np.ones((1, n))
    b_eq = np.array([game.grand_coalition_value()])

    return A_ub, b_ub, A_eq, b_eq


def is_in_core(
    game: CoalitionGame,
    allocation: np.ndarray,
    tolerance: float = 1e-8
) -> Tuple[bool, Optional[Set[int]]]:
    """
    Check if an allocation is in the Core.

    Args:
        game: The cooperative game
        allocation: Proposed allocation vector
        tolerance: Numerical tolerance

    Returns:
        Tuple of (is_in_core, blocking_coalition)
        If not in core, blocking_coalition is a coalition that can improve
    """
    n = game.n_players

    # Check efficiency
    if abs(allocation.sum() - game.grand_coalition_value()) > tolerance:
        return False, None

    # Check coalition rationality
    for coalition in game.all_coalitions():
        if len(coalition) > 0:
            coalition_value = game.value(coalition)
            allocated = sum(allocation[i] for i in coalition)
            if allocated < coalition_value - tolerance:
                return False, set(coalition)

    return True, None


def compute_core(
    game: CoalitionGame,
    objective: str = 'center'
) -> Tuple[bool, Optional[np.ndarray]]:
    """
    Find a point in the Core using Linear Programming.

    Args:
        game: The cooperative game
        objective: How to choose the point:
            - 'center': Maximize minimum slack (Chebyshev center)
            - 'equal': Closest to equal division
            - 'any': Any feasible point (fastest)

    Returns:
        Tuple of (core_is_nonempty, allocation)
    """
    n = game.n_players
    A_ub, b_ub, A_eq, b_eq = core_constraints(game)

    if objective == 'any':
        # Just find any feasible point
        c = np.zeros(n)
        result = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, method='highs')

        if result.success:
            return True, result.x
        return False, None

    elif objective == 'center':
        # Find Chebyshev center (maximize minimum slack)
        # Add variable t for the minimum slack
        # Maximize t subject to: A_ub @ x + t * ||row|| <= b_ub

        # Normalize rows for proper Chebyshev center
        if len(A_ub) == 0:
            # No inequality constraints, just return equal division
            allocation = np.full(n, game.grand_coalition_value() / n)
            return True, allocation

        row_norms = np.linalg.norm(A_ub, axis=1, keepdims=True)
        row_norms[row_norms == 0] = 1  # Avoid division by zero

        # Extended problem: variables are [x_1, ..., x_n, t]
        c_ext = np.zeros(n + 1)
        c_ext[-1] = -1  # Maximize t (minimize -t)

        A_ub_ext = np.hstack([A_ub, row_norms])
        A_eq_ext = np.hstack([A_eq, np.zeros((1, 1))])

        # Bounds: t >= 0 for Chebyshev center
        bounds = [(None, None)] * n + [(0, None)]

        result = linprog(c_ext, A_ub=A_ub_ext, b_ub=b_ub,
                        A_eq=A_eq_ext, b_eq=b_eq,
                        bounds=bounds, method='highs')

        if result.success and result.x[-1] >= -1e-8:
            return True, result.x[:n]
        return False, None

    elif objective == 'equal':
        # Find point closest to equal division
        equal_div = game.grand_coalition_value() / n

        # Minimize ||x - equal_div||^2
        # This is QP, but we can approximate with LP using L1 norm
        # Minimize Σ|x_i - equal_div|

        # Add slack variables for absolute values
        # Variables: [x_1, ..., x_n, s_1+, s_1-, ..., s_n+, s_n-]
        # x_i - equal_div = s_i+ - s_i-
        # Minimize Σ(s_i+ + s_i-)

        c_ext = np.zeros(n + 2*n)
        c_ext[n:] = 1  # Minimize sum of slacks

        # Constraints: x_i - s_i+ + s_i- = equal_div
        A_slack = np.zeros((n, 3*n))
        for i in range(n):
            A_slack[i, i] = 1
            A_slack[i, n + 2*i] = -1
            A_slack[i, n + 2*i + 1] = 1
        b_slack = np.full(n, equal_div)

        # Combine with original equality constraint
        A_eq_ext = np.zeros((1 + n, 3*n))
        A_eq_ext[0, :n] = A_eq[0]
        A_eq_ext[1:, :] = A_slack
        b_eq_ext = np.concatenate([b_eq, b_slack])

        # Extend inequality constraints
        A_ub_ext = np.zeros((len(A_ub), 3*n))
        A_ub_ext[:, :n] = A_ub

        # Bounds: slacks >= 0
        bounds = [(None, None)] * n + [(0, None)] * (2*n)

        result = linprog(c_ext, A_ub=A_ub_ext, b_ub=b_ub,
                        A_eq=A_eq_ext, b_eq=b_eq_ext,
                        bounds=bounds, method='highs')

        if result.success:
            return True, result.x[:n]
        return False, None

    else:
        raise ValueError(f"Unknown objective: {objective}")


def core_vertices_2d(
    game: CoalitionGame,
) -> Optional[np.ndarray]:
    """
    For 2-player games, compute the Core vertices.

    The Core of a 2-player game is an interval on the efficiency line.

    Returns:
        Array of shape (2, 2) with the two endpoints, or None if empty
    """
    if game.n_players != 2:
        raise ValueError("This function only works for 2-player games")

    v_N = game.grand_coalition_value()
    v_1 = game.value({0})
    v_2 = game.value({1})

    # Core: x_1 >= v_1, x_2 >= v_2, x_1 + x_2 = v_N
    # => x_1 >= v_1, x_1 <= v_N - v_2
    # Core is non-empty iff v_1 + v_2 <= v_N

    if v_1 + v_2 > v_N + 1e-10:
        return None

    x1_min = v_1
    x1_max = v_N - v_2

    return np.array([
        [x1_min, v_N - x1_min],
        [x1_max, v_N - x1_max]
    ])


def core_vertices_3d(
    game: CoalitionGame,
    n_points: int = 100
) -> Optional[np.ndarray]:
    """
    For 3-player games, sample the Core boundary.

    The Core lives on the 2-simplex (efficiency plane).
    This function samples points and finds which are in the Core.

    Returns:
        Array of Core vertices, or None if empty
    """
    if game.n_players != 3:
        raise ValueError("This function only works for 3-player games")

    # Check if Core is non-empty
    is_nonempty, _ = compute_core(game, objective='any')
    if not is_nonempty:
        return None

    v_N = game.grand_coalition_value()

    # Sample points on the efficiency simplex
    core_points = []

    for i in range(n_points + 1):
        for j in range(n_points + 1 - i):
            x1 = (i / n_points) * v_N
            x2 = (j / n_points) * v_N
            x3 = v_N - x1 - x2

            allocation = np.array([x1, x2, x3])
            in_core, _ = is_in_core(game, allocation)

            if in_core:
                core_points.append(allocation)

    if not core_points:
        return None

    return np.array(core_points)


def bondareva_shapley_condition(game: CoalitionGame) -> Tuple[bool, float]:
    """
    Check the Bondareva-Shapley condition for Core non-emptiness.

    The Core is non-empty if and only if the game is balanced.
    A game is balanced if for every balanced collection of coalitions,
    the sum of weighted values does not exceed v(N).

    This function uses LP duality to check the condition.

    Returns:
        Tuple of (is_balanced, gap)
        where gap is v(N) minus the maximum weighted sum
    """
    n = game.n_players

    # The dual LP checks if there exist weights λ_S >= 0 such that:
    # Σ_{S: i∈S} λ_S = 1 for all i (balanced collection)
    # and Σ_S λ_S · v(S) > v(N) (blocking)

    # Variables: λ_S for each non-empty proper subset S
    coalitions = [frozenset(c) for c in game.all_coalitions()
                  if 0 < len(c) < n]
    m = len(coalitions)

    if m == 0:
        # Only trivial coalitions, Core is always non-empty
        return True, game.grand_coalition_value()

    # Objective: maximize Σ λ_S · v(S)
    c = np.array([-game.value(S) for S in coalitions])  # Negate for minimization

    # Constraints: Σ_{S: i∈S} λ_S = 1 for all i
    A_eq = np.zeros((n, m))
    for j, S in enumerate(coalitions):
        for i in S:
            A_eq[i, j] = 1
    b_eq = np.ones(n)

    # λ_S >= 0
    bounds = [(0, None)] * m

    result = linprog(c, A_eq=A_eq, b_eq=b_eq, bounds=bounds, method='highs')

    if result.success:
        max_weighted_sum = -result.fun
        gap = game.grand_coalition_value() - max_weighted_sum
        is_balanced = gap >= -1e-8
        return is_balanced, gap

    # LP infeasible means the constraint set is empty
    # This shouldn't happen for a valid game
    return True, game.grand_coalition_value()
