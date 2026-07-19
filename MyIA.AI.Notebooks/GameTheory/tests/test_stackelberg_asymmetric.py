# -*- coding: utf-8 -*-
"""Regression tests for examples/stackelberg_leader_follower.py.

Pins the asymmetric-cost follower-quantity fix. The follower's Stackelberg
quantity is its Cournot reaction curve evaluated at the leader's equilibrium
quantity: q_F = (a - c_F - q_L) / 2, with q_L = (a - 2*c_L + c_F) / 2.

The previous closed form ``(a + c_L - 2*c_F) / 4`` was correct ONLY in the
symmetric case c_L == c_F (where it collapses to (a - c)/4) and diverged from
the reaction curve for any cost asymmetry. For example with (a, c_L, c_F) =
(100, 10, 20): q_L = 50, the follower's true best response is 15, but the old
formula returned 17.5.

These tests assert the INVARIANT (follower best-responds to the leader
quantity) for several asymmetric cost pairs, so they would have failed on the
buggy version and are robust to the exact closed-form expression chosen.

Run with: pytest tests/test_stackelberg_asymmetric.py -v
"""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).parent.parent))

from examples.stackelberg_leader_follower import (  # noqa: E402
    stackelberg_equilibrium,
    cournot_reaction_curve,
)


# ----------------------------------------------------------------------------
# Symmetric costs (textbook Stackelberg): q_L = (a-c)/2, q_F = (a-c)/4.
# ----------------------------------------------------------------------------

class TestSymmetricStackelberg:
    """Symmetric-cost Stackelberg matches the textbook closed forms."""

    def test_symmetric_leader_is_half(self):
        qL, qF = stackelberg_equilibrium(100, 10, 10)
        assert qL == pytest.approx((100 - 10) / 2)  # 45.0

    def test_symmetric_follower_is_quarter(self):
        qL, qF = stackelberg_equilibrium(100, 10, 10)
        assert qF == pytest.approx((100 - 10) / 4)  # 22.5

    def test_leader_produces_more_than_follower(self):
        """First-mover advantage: the leader sells more than the follower."""
        qL, qF = stackelberg_equilibrium(100, 10, 10)
        assert qL > qF


# ----------------------------------------------------------------------------
# Asymmetric costs: the follower MUST best-respond to the leader quantity.
# This is the regression pin -- the buggy closed form failed here.
# ----------------------------------------------------------------------------

class TestAsymmetricFollowerBestResponds:
    """q_F must equal the Cournot reaction curve at the leader quantity."""

    @pytest.mark.parametrize("a,cL,cF", [
        (100, 10, 20),   # follower costlier -> smaller q_F (bug gave 17.5, true 15)
        (100, 20, 10),   # leader costlier -> larger q_F (bug gave 25.0, true 27.5)
        (100, 5, 30),    # strong asymmetry (bug gave 11.25, true 5.0)
        (100, 30, 5),    # reversed asymmetry (bug gave 30.0, true 36.25)
        (120, 8, 16),
    ])
    def test_follower_equals_reaction_curve(self, a, cL, cF):
        qL, qF = stackelberg_equilibrium(a, cL, cF)
        # Ground truth: the follower's best response to the leader quantity.
        reaction = cournot_reaction_curve(qL, demand_intercept=a, marginal_cost=cF)
        assert qF == pytest.approx(reaction), (
            f"asymmetric a={a},cL={cL},cF={cF}: follower qF={qF} != reaction {reaction} "
            f"at leader qL={qL}"
        )

    def test_asymmetric_diverges_from_buggy_formula(self):
        """Explicit pin: the old (a + cL - 2cF)/4 is NOT what we return."""
        a, cL, cF = 100, 10, 20
        qL, qF = stackelberg_equilibrium(a, cL, cF)
        buggy = (a + cL - 2 * cF) / 4  # 17.5 -- the previous (wrong) closed form
        assert qF != pytest.approx(buggy)
        assert qF == pytest.approx(15.0)  # true reaction-curve value


# ----------------------------------------------------------------------------
# Leader quantity closed form (was already correct; pinned for completeness).
# ----------------------------------------------------------------------------

class TestLeaderClosedForm:
    """q_L = (a - 2*c_L + c_F) / 2 for the general asymmetric case."""

    @pytest.mark.parametrize("a,cL,cF,expected", [
        (100, 10, 10, 45.0),
        (100, 10, 20, 50.0),
        (100, 20, 10, 35.0),
    ])
    def test_leader_closed_form(self, a, cL, cF, expected):
        qL, _ = stackelberg_equilibrium(a, cL, cF)
        assert qL == pytest.approx(expected)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
