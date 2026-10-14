"""Tests for meta_labeling_tsmom.py -- the pieces of experiment 5b (issue #18922).

Synthetic prices only: no download, no model fit on the full panel.
"""

from __future__ import annotations

import numpy as np
import pandas as pd
import pytest

import meta_labeling_tsmom as ml


def _sessions(n: int, start: str = "2019-01-02") -> pd.DatetimeIndex:
    return pd.bdate_range(start, periods=n)


# ------------------------------------------------------------------ labels

def test_triple_barrier_upper_first():
    assert ml.triple_barrier(np.array([0.01, 0.05, -0.2]), 0.04) == 1


def test_triple_barrier_lower_first():
    assert ml.triple_barrier(np.array([-0.01, -0.05, 0.2]), 0.04) == 0


def test_triple_barrier_no_touch_uses_last_sign():
    assert ml.triple_barrier(np.array([0.01, -0.02, 0.003]), 0.04) == 1
    assert ml.triple_barrier(np.array([0.01, 0.02, -0.003]), 0.04) == 0
    assert ml.triple_barrier(np.array([0.01, 0.0]), 0.04) == 0


def test_decision_dates_are_last_session_of_each_month():
    days = _sessions(70, "2020-01-01")
    dec = ml.decision_dates(days)
    assert list(dec[:3]) == [pd.Timestamp("2020-01-31"), pd.Timestamp("2020-02-28"),
                             pd.Timestamp("2020-03-31")]
    assert all(d in days for d in dec)


# -------------------------------------------------------------- simulation

def test_simulate_long_position_and_fees():
    days = _sessions(5)
    closes = pd.DataFrame({"A": [100.0, 110.0, 121.0, 121.0, 121.0],
                           "B": [50.0] * 5}, index=days)
    weights = {days[0]: pd.Series({"A": 1.0, "B": 0.0})}
    sim = ml.simulate(closes, weights, end=f"{days[-1]:%Y-%m-%d}")
    entry = 1.0 - ml.FEE_RATE
    assert sim["net_return"].iloc[0] == pytest.approx(-ml.FEE_RATE)
    assert sim["turnover"].iloc[0] == pytest.approx(1.0)
    assert sim["net_return"].iloc[1] == pytest.approx(0.10)
    assert sim["net_return"].iloc[2] == pytest.approx(0.10)
    assert sim["fee"].sum() == pytest.approx(ml.FEE_RATE)
    assert (1.0 + sim["net_return"]).prod() == pytest.approx(entry * 1.21)


def test_simulate_short_loses_when_price_rises():
    days = _sessions(3)
    closes = pd.DataFrame({"A": [100.0, 110.0, 99.0]}, index=days)
    sim = ml.simulate(closes, {days[0]: pd.Series({"A": -1.0})},
                      end=f"{days[-1]:%Y-%m-%d}")
    # equity after entry e0 = 1 - fee ; day 1: pnl = -e0 * 0.10
    assert sim["net_return"].iloc[1] == pytest.approx(-0.10)
    # holdings drift: v = -e0 * 1.1, equity e0 * 0.9 ; day 2 return -10 %
    assert sim["net_return"].iloc[2] == pytest.approx(-1.1 * -0.10 / 0.9)


def test_simulate_drift_then_rebalance_turnover():
    days = _sessions(3)
    closes = pd.DataFrame({"A": [100.0, 200.0, 200.0], "B": [100.0, 100.0, 100.0]}, index=days)
    w = pd.Series({"A": 0.5, "B": 0.5})
    sim = ml.simulate(closes, {days[0]: w, days[1]: w}, end=f"{days[-1]:%Y-%m-%d}")
    # after day 1, A weighs 2/3 of equity, B 1/3: trading back to 1/2-1/2 is 1/3 of equity
    assert sim["turnover"].iloc[1] == pytest.approx(1.0 / 3.0)


def test_cash_weight_stays_flat():
    days = _sessions(3)
    closes = pd.DataFrame({"A": [100.0, 150.0, 75.0]}, index=days)
    sim = ml.simulate(closes, {days[0]: pd.Series({"A": 0.0})}, end=f"{days[-1]:%Y-%m-%d}")
    assert (sim["net_return"] == 0.0).all()
    assert sim["fee"].sum() == 0.0


# ------------------------------------------------------------- variants

def _toy_block():
    t = pd.Timestamp(ml.BLOCK_FIRST_DECISION)
    block = pd.DataFrame({"date": [t, t], "asset": ["A", "B"], "weight": [0.6, -0.4]})
    weights = {t: pd.Series({"A": 0.6, "B": -0.4, "C": 0.0})}
    return block, weights, t


def test_filter_variant_zeroes_low_probability():
    block, weights, t = _toy_block()
    w = ml.variant_weights(weights, block, np.array([0.7, 0.3]), "filter")[t]
    assert w["A"] == pytest.approx(0.6)
    assert w["B"] == 0.0
    assert w["C"] == 0.0


def test_size_variant_scales_without_renormalising():
    block, weights, t = _toy_block()
    w = ml.variant_weights(weights, block, np.array([0.7, 0.3]), "size")[t]
    assert w["A"] == pytest.approx(0.42)
    assert w["B"] == pytest.approx(-0.12)
    assert w.abs().sum() == pytest.approx(0.54)


def test_primary_variant_is_unchanged_and_drops_decisions_outside_block():
    block, weights, t = _toy_block()
    weights[pd.Timestamp("2021-11-30")] = pd.Series({"A": 1.0})
    out = ml.variant_weights(weights, block, None, None)
    assert list(out) == [t]
    pd.testing.assert_series_equal(out[t], weights[t])


# ------------------------------------------------------------ cross-val

def test_purged_folds_remove_overlapping_training_events():
    days = _sessions(400, "2018-01-01")
    dec = ml.decision_dates(days)
    dev = pd.DataFrame({"date": dec[:-1], "end": dec[1:]})
    folds = ml.purged_folds(dev, days, n_folds=4, embargo=21)
    for train, test in folds:
        assert not set(train) & set(test)
        lo, hi = dev.loc[test, "date"].min(), dev.loc[test, "end"].max()
        tr = dev.loc[train]
        # every kept training window ends >21 sessions before the test span or
        # starts >21 sessions after it
        for _, row in tr.iterrows():
            gap_before = days.get_loc(lo) - days.get_loc(row["end"])
            gap_after = days.get_loc(row["date"]) - days.get_loc(hi)
            assert gap_before > 21 or gap_after > 21
    assert sorted(np.concatenate([t for _, t in folds])) == list(range(len(dev)))


def test_month_block_permutation_keeps_months_together():
    dates = np.repeat(pd.bdate_range("2020-01-31", periods=6, freq="BME"), 3)
    labels = np.array([0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 1])
    dev = pd.DataFrame({"date": dates, "label": labels})
    perm = ml.month_block_permutation(dev, seed=7)
    assert sorted(perm) == sorted(labels)
    chunks = {tuple(perm[i:i + 3]) for i in range(0, 18, 3)}
    original = {tuple(labels[i:i + 3]) for i in range(0, 18, 3)}
    assert chunks <= original
    assert np.array_equal(perm, ml.month_block_permutation(dev, seed=7))


# ------------------------------------------------------------- verdicts

@pytest.mark.parametrize("diff,p,placebo,seeds,expected", [
    (-0.01, 0.01, -1.0, 8, "NO BEATS"),
    (0.0, 0.01, -1.0, 8, "NO BEATS"),
    (0.30, 0.01, 0.10, 7, "BEATS"),
    (0.30, 0.06, 0.10, 8, "INCONCLUSIVE"),
    (0.30, 0.01, 0.35, 8, "INCONCLUSIVE"),
    (0.30, 0.01, 0.10, 6, "INCONCLUSIVE"),
])
def test_strategy_gate(diff, p, placebo, seeds, expected):
    assert ml.strategy_gate(diff, p, placebo, seeds) == expected


def test_forecast_verdict_detects_informative_probabilities():
    rng = np.random.default_rng(0)
    y = rng.integers(0, 2, 600)
    probs = {s: np.clip(0.5 + 0.3 * (2 * y - 1) + rng.normal(0, 0.05, 600), 0.01, 0.99)
             for s in ml.SEEDS}
    out = ml.forecast_verdict(y, probs, base_rate=0.5)
    assert out["verdict"] == "prévision BEATS"
    assert out["edge_mean"] > 0


def test_forecast_verdict_detects_harmful_probabilities():
    rng = np.random.default_rng(1)
    y = rng.integers(0, 2, 600)
    probs = {s: np.clip(0.5 - 0.3 * (2 * y - 1) + rng.normal(0, 0.05, 600), 0.01, 0.99)
             for s in ml.SEEDS}
    out = ml.forecast_verdict(y, probs, base_rate=0.5)
    assert out["verdict"] == "prévision BEATEN"


def test_forecast_verdict_noise_is_not_beats():
    rng = np.random.default_rng(2)
    y = rng.integers(0, 2, 600)
    probs = {s: np.clip(rng.uniform(0.45, 0.55, 600), 0.01, 0.99) for s in ml.SEEDS}
    out = ml.forecast_verdict(y, probs, base_rate=float(y.mean()))
    assert out["verdict"] != "prévision BEATS"


# ---------------------------------------------------------------- events

def test_build_events_signs_features_and_weights():
    n = 420
    days = _sessions(n, "2015-01-02")
    up = 100.0 * np.exp(np.linspace(0, 0.5, n)) * (1 + 0.01 * np.sin(np.arange(n)))
    down = 100.0 * np.exp(np.linspace(0, -0.5, n)) * (1 + 0.01 * np.cos(np.arange(n)))
    closes = pd.DataFrame({s: up for s in ml.SYMBOLS}, index=days)
    closes["TLT"] = down
    closes.loc[days[:300], "XLC"] = np.nan  # listed late: not eligible at first
    vix = pd.Series(20.0 + np.sin(np.arange(n)), index=days)
    events, weights = ml.build_events(closes, vix)
    assert not events.empty
    first = events["date"].min()
    assert first >= days[ml.LOOKBACK]
    tlt = events[events["asset"] == "TLT"]
    assert (tlt["side"] == -1).all()
    assert (tlt["r252"] > 0).all()          # signed: a falling asset held short
    assert (tlt["ma200_gap"] > 0).all()
    assert "XLC" not in set(events.loc[events["date"] == first, "asset"])
    for t, w in weights.items():
        assert w.abs().sum() == pytest.approx(1.0)
    assert set(ml.FEATURES) <= set(events.columns)
    assert events[ml.FEATURES].notna().all().all()
