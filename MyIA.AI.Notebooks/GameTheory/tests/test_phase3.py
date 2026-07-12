"""
Tests for Phase 3 Game Theory utilities.

Covers:
- CFR and regret matching
- Stackelberg equilibrium
- Mechanism design (VCG, Gale-Shapley)
- Multi-agent learning (Fictitious Play)

Run with: pytest tests/test_phase3.py
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from game_theory_utils import (
    CFRSolver,
    stackelberg_duopoly, cournot_duopoly,
    VCGAuction, gale_shapley,
    FictitiousPlay, create_rps_matrix
)


class TestCFRSolver:
    """Tests for CFR solver."""

    def test_regret_matching_uniform(self):
        """Initial strategy should be uniform."""
        cfr = CFRSolver(num_actions=3)
        strategy = cfr.get_strategy("test_infoset")
        np.testing.assert_array_almost_equal(strategy, [1/3, 1/3, 1/3])

    def test_regret_matching_positive(self):
        """Strategy should favor actions with positive regret."""
        cfr = CFRSolver(num_actions=3)
        cfr.regret_sum["test"] = np.array([0.0, 1.0, 2.0])
        strategy = cfr.get_strategy("test")

        assert strategy[0] == 0.0
        assert strategy[1] < strategy[2]
        np.testing.assert_almost_equal(strategy.sum(), 1.0)

    def test_average_strategy(self):
        """Average strategy should accumulate correctly."""
        cfr = CFRSolver(num_actions=2)
        cfr.strategy_sum["test"] = np.array([3.0, 1.0])
        avg = cfr.get_average_strategy("test")
        np.testing.assert_array_almost_equal(avg, [0.75, 0.25])


class TestStackelberg:
    """Tests for Stackelberg equilibrium."""

    def test_symmetric_duopoly(self):
        """Symmetric duopoly should have leader advantage."""
        a, b = 100, 1
        c = 10  # Same costs

        q_L, q_F, pi_L, pi_F = stackelberg_duopoly(a, b, c, c)
        q1_c, q2_c, pi1_c, pi2_c = cournot_duopoly(a, b, c, c)

        # Leader produces more than Cournot
        assert q_L > q1_c
        # Follower produces less
        assert q_F < q2_c
        # Leader profit higher than Cournot
        assert pi_L > pi1_c
        # Follower profit lower than Cournot
        assert pi_F < pi2_c

    def test_stackelberg_quantities_positive(self):
        """Quantities should be non-negative."""
        q_L, q_F, _, _ = stackelberg_duopoly(100, 1, 10, 10)
        assert q_L >= 0
        assert q_F >= 0

    def test_cournot_symmetric(self):
        """Symmetric Cournot should give equal quantities."""
        q1, q2, pi1, pi2 = cournot_duopoly(100, 1, 10, 10)
        np.testing.assert_almost_equal(q1, q2)
        np.testing.assert_almost_equal(pi1, pi2)


class TestVCGAuction:
    """Tests for VCG mechanism."""

    def test_single_item_second_price(self):
        """Single item VCG should be second-price auction."""
        vcg = VCGAuction(n_items=1)
        bids = [100.0, 80.0, 60.0]
        winner, payment = vcg.allocate_single(bids)

        assert winner == 0  # Highest bidder wins
        assert payment == 80.0  # Pays second price

    def test_multi_item_allocation(self):
        """Multi-item VCG should allocate to highest bidders."""
        vcg = VCGAuction(n_items=2)
        valuations = [
            [50, 30],  # Agent 0
            [40, 60],  # Agent 1
            [35, 25]   # Agent 2
        ]

        allocations, payments = vcg.allocate_multi(valuations)

        # Agent 0 should get item 0 (highest: 50)
        assert allocations[0][0] == 1.0
        # Agent 1 should get item 1 (highest: 60)
        assert allocations[1][1] == 1.0
        # Payments should be non-negative
        for p in payments:
            assert p >= 0

    def test_vcg_incentive_compatibility(self):
        """Truthful bidding should be optimal in VCG."""
        vcg = VCGAuction(n_items=1)

        true_value = 100
        other_bids = [80, 60]

        # Truthful utility
        all_bids = [true_value] + other_bids
        winner, payment = vcg.allocate_single(all_bids)
        truthful_utility = true_value - payment if winner == 0 else 0

        # Try lying (overbid)
        lie_bids = [150] + other_bids
        winner_lie, payment_lie = vcg.allocate_single(lie_bids)
        # Payment is still 80 (second price)
        lie_utility = true_value - payment_lie if winner_lie == 0 else 0

        # Utility should be the same (can't gain by lying)
        assert truthful_utility == lie_utility


class TestGaleShapley:
    """Tests for stable matching."""

    def test_basic_matching(self):
        """Basic stable matching should work."""
        men_prefs = {
            'A': ['X', 'Y', 'Z'],
            'B': ['Y', 'X', 'Z'],
            'C': ['Y', 'Z', 'X']
        }
        women_prefs = {
            'X': ['B', 'A', 'C'],
            'Y': ['A', 'B', 'C'],
            'Z': ['A', 'B', 'C']
        }

        matching = gale_shapley(men_prefs, women_prefs)

        # Should have 3 pairs
        assert len(matching) == 3
        # All men should be matched
        assert set(matching.keys()) == {'A', 'B', 'C'}
        # All women should be matched (unique)
        assert set(matching.values()) == {'X', 'Y', 'Z'}

    def test_matching_stability(self):
        """Matching should be stable (no blocking pairs)."""
        men_prefs = {
            'A': ['X', 'Y'],
            'B': ['Y', 'X']
        }
        women_prefs = {
            'X': ['A', 'B'],
            'Y': ['B', 'A']
        }

        matching = gale_shapley(men_prefs, women_prefs)

        # Expected stable matching: A-X, B-Y
        assert matching['A'] == 'X'
        assert matching['B'] == 'Y'


class TestFictitiousPlay:
    """Tests for Fictitious Play algorithm."""

    def test_rps_convergence(self):
        """FP should converge to Nash in RPS."""
        rps = create_rps_matrix()
        fp = FictitiousPlay(rps)
        fp.train(500)

        avg_p1 = fp.get_average_strategy(0)
        avg_p2 = fp.get_average_strategy(1)

        # Should be close to uniform (1/3, 1/3, 1/3)
        nash = np.array([1/3, 1/3, 1/3])
        np.testing.assert_array_almost_equal(avg_p1, nash, decimal=1)
        np.testing.assert_array_almost_equal(avg_p2, nash, decimal=1)

    def test_exploitability_stays_low(self):
        """Exploitability should stay low after training in RPS."""
        rps = create_rps_matrix()
        fp = FictitiousPlay(rps)

        # Train and check exploitability remains small
        fp.train(500)
        final_expl = fp.exploitability()

        # In RPS, Nash is uniform distribution, exploitability should be small
        # (approaches 0 as training increases)
        assert final_expl < 0.2

    def test_rps_matrix(self):
        """RPS matrix should be correct."""
        rps = create_rps_matrix()

        # Rock vs Paper: -1
        assert rps[0, 1] == -1
        # Paper vs Rock: 1
        assert rps[1, 0] == 1
        # Rock vs Rock: 0
        assert rps[0, 0] == 0
        # Zero-sum property
        np.testing.assert_array_almost_equal(rps, -rps.T)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
