# -*- coding: utf-8 -*-
"""Tests for examples/stag_hunt_forward_induction.py.

The module had zero dedicated tests. Its algorithm functions
(create_stag_hunt, find_equilibria, risk_dominance_analysis) are correct and
are pinned here against known game-theory invariants. The suite also pins the
prose-honesty fix in ``main()``: a prior version hardcoded "(Hare, Hare) is
risk-dominant" which, for the module's own payoff matrices, contradicted the
computed verdict (Stag, Stag) -- the demo printed two opposite claims.

Run with: pytest tests/test_stag_hunt_forward_induction.py -v
"""

import sys
from pathlib import Path

import numpy as np
import pytest

sys.path.insert(0, str(Path(__file__).parent.parent))

from examples.stag_hunt_forward_induction import (  # noqa: E402
    create_stag_hunt,
    find_equilibria,
    risk_dominance_analysis,
    main,
)

try:
    import nashpy as nash  # noqa: F401
    HAS_NASHPY = True
except Exception:
    HAS_NASHPY = False


# ----------------------------------------------------------------------------
# Payoff structure
# ----------------------------------------------------------------------------

class TestCreateStagHunt:
    """create_stag_hunt builds a symmetric 2x2 coordination game."""

    def test_shapes(self):
        A, B = create_stag_hunt()
        assert A.shape == (2, 2)
        assert B.shape == (2, 2)

    def test_symmetric_game_B_is_A_transpose(self):
        """A symmetric game has B = A^T (both players share the payoff matrix)."""
        A, B = create_stag_hunt()
        np.testing.assert_array_equal(B, A.T)

    def test_default_both_stag_is_payoff_dominant(self):
        """(Stag, Stag) is the Pareto-optimal outcome: highest joint payoff."""
        A, B = create_stag_hunt()
        # (Stag, Stag) = (0,0): both get stag_reward (4).
        assert A[0, 0] == 4.0 and B[0, 0] == 4.0
        # It strictly Pareto-dominates (Hare, Hare) = (1,1): both get 2.
        assert A[0, 0] > A[1, 1] and B[0, 0] > B[1, 1]

    def test_custom_rewards_propagate(self):
        A, _ = create_stag_hunt(stag_reward=10.0, hare_reward=5.0)
        assert A[0, 0] == 10.0          # both stag
        assert A[1, 1] == 5.0           # both hare
        assert A[1, 0] == 5.0 - 1       # hare_reward - 1 (off-diagonal)


# ----------------------------------------------------------------------------
# Nash equilibria
# ----------------------------------------------------------------------------

class TestFindEquilibria:
    """find_equilibria locates the two pure NE + the mixed NE of Stag Hunt."""

    def test_two_pure_nash(self):
        """Stag Hunt has exactly two pure NE: (Stag,Stag) and (Hare,Hare)."""
        A, B = create_stag_hunt()
        eq = find_equilibria(A, B)
        assert (0, 0) in eq['pure']
        assert (1, 1) in eq['pure']
        assert len(eq['pure']) == 2

    def test_pure_nash_verified_by_unilateral_deviation(self):
        """Independently re-derive pure NE: no player gains by deviating alone."""
        A, B = create_stag_hunt()
        eq = find_equilibria(A, B)
        for (i, j) in eq['pure']:
            # P1 cannot improve by switching row: A[i,j] >= A[1-i, j]
            assert A[i, j] >= A[1 - i, j]
            # P2 cannot improve by switching col: B[i,j] >= B[i, 1-j]
            assert B[i, j] >= B[i, 1 - j]

    def test_off_diagonals_are_not_nash(self):
        """(Stag, Hare) and (Hare, Stag) are NOT equilibria."""
        A, B = create_stag_hunt()
        eq = find_equilibria(A, B)
        assert (0, 1) not in eq['pure']
        assert (1, 0) not in eq['pure']

    @pytest.mark.skipif(not HAS_NASHPY, reason="nashpy not installed")
    def test_one_mixed_nash_with_interior_probabilities(self):
        """There is exactly one mixed NE, fully interior (0 < p < 1)."""
        A, B = create_stag_hunt()
        eq = find_equilibria(A, B)
        mixed = [m for m in eq['mixed']
                 if not (np.allclose(m[0], [1, 0]) or np.allclose(m[0], [0, 1]))]
        assert len(mixed) >= 1
        s1, s2 = mixed[0]
        # Interior: both actions played with positive probability.
        assert 0.0 < s1[0] < 1.0
        assert 0.0 < s2[0] < 1.0


# ----------------------------------------------------------------------------
# Risk dominance (Harsanyi-Selten) -- the function is correct; pinned here.
# ----------------------------------------------------------------------------

class TestRiskDominance:
    """risk_dominance_analysis implements the deviation-loss-product criterion."""

    def test_default_game_stag_stag_is_risk_dominant(self):
        """For the default payoffs, (Stag,Stag) risk-dominates (Hare,Hare).

        Deviation-loss products:
          from (Stag,Stag): (4-1)*(4-1) = 9
          from (Hare,Hare): (2-0)*(2-0) = 4
        9 > 4 -> (Stag, Stag) risk-dominant. (This is what the computation
        returns; the old hardcoded demo prose claimed the opposite.)
        """
        A, B = create_stag_hunt()
        verdict = risk_dominance_analysis(A, B, (0, 0), (1, 1))
        assert "Equilibrium 1" in verdict
        assert "Equilibrium 2" not in verdict.split("is")[0]  # eq1 named dominant

    def test_deviation_loss_products(self):
        """The decision tracks the unilateral-deviation-loss products directly."""
        A, B = create_stag_hunt()
        # product from eq1=(0,0): (A[0,0]-A[1,0]) * (B[0,0]-B[0,1])
        p1 = (A[0, 0] - A[1, 0]) * (B[0, 0] - B[0, 1])
        # product from eq2=(1,1): (A[1,1]-A[0,1]) * (B[1,1]-B[1,0])
        p2 = (A[1, 1] - A[0, 1]) * (B[1, 1] - B[1, 0])
        assert p1 == pytest.approx(9.0)
        assert p2 == pytest.approx(4.0)
        assert p1 > p2  # eq1 risk-dominant

    def test_reversed_argument_order_flips_verdict(self):
        """Passing the equilibria in the opposite order flips which is "1"."""
        A, B = create_stag_hunt()
        # eq1=(1,1), eq2=(0,0): now (1,1) is "Equilibrium 1" but (0,0) is still
        # the risk-dominant outcome -> verdict names Equilibrium 2.
        verdict = risk_dominance_analysis(A, B, (1, 1), (0, 0))
        assert "Equilibrium 2" in verdict

    def test_tie_when_products_equal(self):
        """Equal deviation-loss products -> neither strictly risk-dominant."""
        # Symmetric anti-coordination (Hawk-Dove-ish) with equal products.
        A = np.array([[0.0, 2.0], [2.0, 0.0]])
        B = np.array([[0.0, 2.0], [2.0, 0.0]])
        verdict = risk_dominance_analysis(A, B, (0, 0), (1, 1))
        assert "Neither" in verdict


# ----------------------------------------------------------------------------
# Prose-honesty regression: main() must not contradict the computed verdict.
# ----------------------------------------------------------------------------

class TestMainDemoHonesty:
    """main()'s risk-dominance prose must agree with the computed verdict.

    Pins the fix: the previous hardcoded "(Hare, Hare) is risk-dominant"
    contradicted the computed "(Stag, Stag) is risk-dominant".
    """

    def test_main_runs_without_contradictory_prose(self, capsys):
        A, B = create_stag_hunt()
        verdict = risk_dominance_analysis(A, B, (0, 0), (1, 1))
        main()
        out = capsys.readouterr().out
        # The computed verdict is present.
        assert "Risk Dominance" in out
        # The false hardcoded claim has been removed.
        assert "is risk-dominant despite lower payoffs" not in out
        # Whatever the demo prints about dominance must agree with the function.
        if "Equilibrium 1" in verdict:  # (Stag, Stag) dominant
            assert "(Hare, Hare) is risk-dominant" not in out


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
