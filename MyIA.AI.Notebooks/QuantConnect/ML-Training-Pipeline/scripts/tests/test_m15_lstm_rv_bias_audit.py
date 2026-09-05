"""Regression tests for cross-seed aggregation in m15_lstm_rv_bias_audit (#14749).

The decision jambe is `dm_cen_p_median` (median per-seed centered-DM p-value),
NOT a single significant seed and NOT the pooled concat. These tests pin the
adjoint preflight correction: a 1/4 BEATEN or the real 2/4 h=5 case must stay
INCONCLUSIVE; only a significant median (p<0.05) in the lstm_worse direction
yields NO BEATS.
"""

from __future__ import annotations

import numpy as np
import pytest

from m15_lstm_rv_bias_audit import _precision_verdict


def _verdict(pvalues, stats, edge_pct=15.0, edge_std_pct=5.0):
    return _precision_verdict(list(pvalues), list(stats), edge_pct, edge_std_pct)


def test_single_significant_seed_does_not_flip_horizon() -> None:
    # 1/4 BEATEN: one p<0.05 seed among three non-significant ones. The median
    # is not significant (0.35 >= 0.05), so the horizon must stay INCONCLUSIVE.
    verdict, p_med, stat_med, direction = _verdict(
        pvalues=[0.01, 0.5, 0.4, 0.3], stats=[1.0, -0.2, -0.3, -0.1],
    )
    assert p_med == pytest.approx(0.35)
    assert direction == "lstm_better"
    assert verdict == "INCONCLUSIVE"


def test_24_beaten_h5_case_reproduces_adjoint_median() -> None:
    # Real committed h=5 data: 2/4 BEATEN, median p ≈ 0.2076 >= 0.05.
    verdict, p_med, stat_med, direction = _verdict(
        pvalues=[0.3962, 0.0189, 0.0098, 0.4477], stats=[1.5, 2.0, 2.2, 0.5],
    )
    assert p_med == pytest.approx(0.20757, rel=1e-3)
    assert direction == "lstm_worse"
    assert verdict == "INCONCLUSIVE"


def test_34_beaten_h10_case_is_no_beats() -> None:
    # Real committed h=10 data: 3/4 BEATEN, median p ≈ 0.00311 < 0.05,
    # direction lstm_worse -> the precision jambe is significant against LSTM.
    verdict, p_med, stat_med, direction = _verdict(
        pvalues=[0.0027, 0.0003, 0.0035, 0.061], stats=[2.5, 3.0, 2.7, 1.5],
    )
    assert p_med == pytest.approx(0.0031, abs=1e-4)
    assert p_med < 0.05
    assert direction == "lstm_worse"
    assert verdict == "NO BEATS"


def test_beats_requires_median_significance_and_edge() -> None:
    verdict, p_med, stat_med, direction = _verdict(
        pvalues=[0.01, 0.02, 0.03, 0.04], stats=[-2.0, -1.5, -2.5, -1.0],
        edge_pct=15.0, edge_std_pct=4.0,
    )
    assert p_med == pytest.approx(0.025)
    assert direction == "lstm_better"
    assert verdict == "BEATS"


def test_beats_rejected_without_edge_even_if_significant() -> None:
    # Median significant + lstm_better direction, but edge < 2*sigma.
    verdict, p_med, stat_med, direction = _verdict(
        pvalues=[0.01, 0.02, 0.03, 0.04], stats=[-2.0, -1.5, -2.5, -1.0],
        edge_pct=2.0, edge_std_pct=5.0,
    )
    assert p_med == pytest.approx(0.025)
    assert direction == "lstm_better"
    assert verdict == "INCONCLUSIVE"


def test_pooled_concat_median_is_not_the_decision() -> None:
    # Guard against re-introducing the pooled concat as the decision variable:
    # even when the pooled p-value would be tiny, the median per-seed p is used.
    # A single dramatic seed must not outweigh three calm seeds.
    verdict, p_med, stat_med, direction = _verdict(
        pvalues=[0.0001, 0.9, 0.95, 0.99], stats=[3.0, -0.1, -0.2, -0.05],
    )
    assert p_med == pytest.approx(0.925)
    assert verdict == "INCONCLUSIVE"
