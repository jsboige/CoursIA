"""Tests for multiscale_gnn_features.py — cross-asset HAR panel + adjacency.

Uses synthetic intraday data + monkey-patched loaders to avoid hitting
G:/ drive or yfinance. Validates shape contracts, no-leakage HAR features,
adjacency normalization invariants.
"""

from __future__ import annotations

import numpy as np
import pandas as pd
import pytest

from intraday_loader import synthesize_intraday, hourly_log_returns
from multiscale_gnn_features import (
    CrossAssetPanel,
    _aligned_log_rv_panel,
    _build_har_features_panel,
    _rolling_correlation_adjacency,
    to_pyg_batches,
)


@pytest.fixture
def synth_panel() -> dict[str, pd.Series]:
    """Three synthetic 'coins' with controlled correlations."""
    out = {}
    for i, name in enumerate(["BTC-USD", "ETH-USD", "SOL-USD"]):
        out[name] = hourly_log_returns(
            synthesize_intraday(
                n_days=120, obs_per_day=24, seed=10 + i, annualized_vol=0.6 + 0.1 * i
            )
        )
    return out


class TestAlignedLogRvPanel:
    def test_three_coin_aligned(self, synth_panel):
        log_rv, rv = _aligned_log_rv_panel(synth_panel)
        assert log_rv.shape[1] == 3
        assert rv.shape[1] == 3
        assert (log_rv.index == rv.index).all()
        assert log_rv.index.is_monotonic_increasing
        assert rv.notna().all().all()


class TestBuildHarFeaturesPanel:
    def test_shape_T_N_F4(self, synth_panel):
        log_rv, _ = _aligned_log_rv_panel(synth_panel)
        X, dates = _build_har_features_panel(log_rv)
        assert X.shape[1] == 3  # N
        assert X.shape[2] == 4  # log_rv, rv_d, rv_w, rv_m
        assert X.shape[0] == len(dates)

    def test_dropna_removes_first_22_rows(self, synth_panel):
        log_rv, _ = _aligned_log_rv_panel(synth_panel)
        n_full = len(log_rv)
        X, dates = _build_har_features_panel(log_rv)
        # rv_m needs 22 lags ⇒ at least 22 rows dropped
        assert n_full - len(dates) >= 22
        assert np.isfinite(X).all()

    def test_rv_d_equals_log_rv_lag1(self, synth_panel):
        log_rv, _ = _aligned_log_rv_panel(synth_panel)
        X, dates = _build_har_features_panel(log_rv)
        # X[..., 1] (rv_d) at row t should equal log_rv at row t-1 of full series
        # Pick a row well past warmup
        idx = 30
        date_t = dates[idx]
        date_prev = log_rv.index[log_rv.index.get_loc(date_t) - 1]
        for n_idx in range(3):
            np.testing.assert_allclose(
                X[idx, n_idx, 1], log_rv.iloc[:, n_idx].loc[date_prev], rtol=1e-6
            )

    def test_no_lookahead_log_rv_at_t_is_observable(self, synth_panel):
        # X[t, n, 0] = log_rv at t (current day) — that's OK for inputs
        # rv_d/w/m all use shift(1), so they're past-only
        log_rv, _ = _aligned_log_rv_panel(synth_panel)
        X, dates = _build_har_features_panel(log_rv)
        idx = 50
        date_t = dates[idx]
        for n_idx in range(3):
            np.testing.assert_allclose(
                X[idx, n_idx, 0],
                log_rv.iloc[:, n_idx].loc[date_t],
                rtol=1e-6,
            )


class TestRollingCorrelationAdjacency:
    def test_shape_T_N_N(self, synth_panel):
        log_rv, _ = _aligned_log_rv_panel(synth_panel)
        X, dates = _build_har_features_panel(log_rv)
        A = _rolling_correlation_adjacency(log_rv, dates, window=60, top_k=2)
        assert A.shape == (len(dates), 3, 3)

    def test_rows_sum_to_1(self, synth_panel):
        log_rv, _ = _aligned_log_rv_panel(synth_panel)
        X, dates = _build_har_features_panel(log_rv)
        A = _rolling_correlation_adjacency(log_rv, dates, window=60, top_k=2)
        for t in range(0, len(dates), 20):
            row_sums = A[t].sum(axis=1)
            np.testing.assert_allclose(row_sums, np.ones(3), atol=1e-5)

    def test_self_loops_present(self, synth_panel):
        log_rv, _ = _aligned_log_rv_panel(synth_panel)
        X, dates = _build_har_features_panel(log_rv)
        A = _rolling_correlation_adjacency(log_rv, dates, window=60, top_k=2)
        n = len(dates)
        for t in [0, n // 4, n // 2, n - 1]:
            assert (np.diag(A[t]) > 0).all()

    def test_warmup_uses_uniform_off_diagonal(self, synth_panel):
        log_rv, _ = _aligned_log_rv_panel(synth_panel)
        X, dates = _build_har_features_panel(log_rv)
        A = _rolling_correlation_adjacency(log_rv, dates, window=60, top_k=2)
        # Window=60 ⇒ first ~38 rows of dates correspond to insufficient
        # history (because dates is already past 22-row warmup of HAR)
        # We just check warmup rows have non-zero off-diag values
        assert (A[0] > 0).sum() > 3  # more than just diagonal


class TestPyGBatches:
    def test_returns_n_steps_dicts(self, synth_panel):
        log_rv, _ = _aligned_log_rv_panel(synth_panel)
        X, dates = _build_har_features_panel(log_rv)
        A = _rolling_correlation_adjacency(log_rv, dates, window=60, top_k=2)
        panel = CrossAssetPanel(
            X=X, A=A, dates=dates,
            coins=("BTC-USD", "ETH-USD", "SOL-USD"),
            log_rv_raw=log_rv.loc[dates],
        )
        batches = to_pyg_batches(panel)
        assert len(batches) == X.shape[0]
        b0 = batches[0]
        for k in ("x", "edge_index", "edge_weight", "date", "n_nodes"):
            assert k in b0
        assert tuple(b0["x"].shape) == (3, 4)
        assert b0["edge_index"].shape[0] == 2
        assert b0["edge_weight"].shape[0] == b0["edge_index"].shape[1]


class TestPanelTargetsHStep:
    def test_target_aligned_one_step(self, synth_panel):
        log_rv, _ = _aligned_log_rv_panel(synth_panel)
        X, dates = _build_har_features_panel(log_rv)
        A = _rolling_correlation_adjacency(log_rv, dates, window=60, top_k=2)
        panel = CrossAssetPanel(
            X=X, A=A, dates=dates,
            coins=("BTC-USD", "ETH-USD", "SOL-USD"),
            log_rv_raw=log_rv.loc[dates],
        )
        target, target_idx = panel.targets_h_step(horizon=1)
        # h=1: target at row t = log_rv at t+1; alignment loses last row
        assert len(target) == len(panel.dates) - 1
        # First target value matches log_rv at second date
        for c_idx, coin in enumerate(panel.coins):
            np.testing.assert_allclose(
                target.iloc[0][coin],
                panel.log_rv_raw.iloc[1][coin],
                rtol=1e-6,
            )

    def test_target_h5_drops_last_5(self, synth_panel):
        log_rv, _ = _aligned_log_rv_panel(synth_panel)
        X, dates = _build_har_features_panel(log_rv)
        A = _rolling_correlation_adjacency(log_rv, dates, window=60, top_k=2)
        panel = CrossAssetPanel(
            X=X, A=A, dates=dates,
            coins=("BTC-USD", "ETH-USD", "SOL-USD"),
            log_rv_raw=log_rv.loc[dates],
        )
        target, _ = panel.targets_h_step(horizon=5)
        assert len(target) == len(panel.dates) - 5

    def test_horizon_must_be_positive(self, synth_panel):
        log_rv, _ = _aligned_log_rv_panel(synth_panel)
        X, dates = _build_har_features_panel(log_rv)
        A = _rolling_correlation_adjacency(log_rv, dates, window=60, top_k=2)
        panel = CrossAssetPanel(
            X=X, A=A, dates=dates,
            coins=("BTC-USD", "ETH-USD", "SOL-USD"),
            log_rv_raw=log_rv.loc[dates],
        )
        with pytest.raises(ValueError):
            panel.targets_h_step(horizon=0)
