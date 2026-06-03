"""Cross-asset HAR feature panel for multi-scale GNN (Issue #834 M5).

Aligns BTC + ETH + SOL hourly returns to a common-date daily log-RV panel,
computes Corsi (2009) HAR features (rv_d / rv_w / rv_m) per coin, and
builds dynamic correlation adjacency for graph spillover.

The output tensor has shape (T, N=n_coins, F=4) where F = [log_rv, rv_d,
rv_w, rv_m]. Adjacency is (T, N, N) rolling-correlation, top-K thresholded.

Designed to plug into PyTorch Geometric: see `to_pyg_batches`.

Usage:
    from multiscale_gnn_features import build_panel
    panel = build_panel()
    print(panel.X.shape, panel.A.shape, panel.coins)
"""

from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
from typing import Sequence

import numpy as np
import pandas as pd

from intraday_loader import (
    hourly_log_returns,
    load_binance_eth,
    load_bitstamp_btc,
    load_yf_intraday,
)
from realized_variance import (
    daily_realized_variance,
    har_lag_features,
    realized_variance_to_log,
)


@dataclass(frozen=True)
class CrossAssetPanel:
    """Aligned cross-asset HAR panel.

    Attributes
    ----------
    X : np.ndarray, shape (T, N, F=4)
        Per-coin features [log_rv, rv_d, rv_w, rv_m]. F=4. Float32.
    A : np.ndarray, shape (T, N, N)
        Dynamic adjacency (rolling correlation, top-K thresholded). Float32.
    dates : pd.DatetimeIndex, len T
    coins : tuple[str, ...], len N
    log_rv_raw : pd.DataFrame, shape (T, N)
        Untransformed log-RV panel, useful for targets.
    """

    X: np.ndarray
    A: np.ndarray
    dates: pd.DatetimeIndex
    coins: tuple[str, ...]
    log_rv_raw: pd.DataFrame = field(repr=False)

    def targets_h_step(self, horizon: int) -> tuple[pd.DataFrame, pd.DatetimeIndex]:
        """Return per-coin h-step-ahead averaged log-RV target (T-h, N).

        target_t = mean(log_rv_{t+1}, ..., log_rv_{t+h})

        Aligned with X[:T-h] / A[:T-h]. Drops last `horizon` rows.
        """
        if horizon < 1:
            raise ValueError(f"horizon must be >=1, got {horizon}")
        df = self.log_rv_raw
        # rolled at row j = mean(log_rv[j-h+1..j])
        rolled = df.rolling(window=horizon, min_periods=horizon).mean()
        # target at t = mean(log_rv[t+1..t+h]) = rolled at row (t+h)
        target = rolled.shift(-horizon).dropna()
        return target, target.index


def _aligned_log_rv_panel(
    coins_data: dict[str, pd.Series],
) -> tuple[pd.DataFrame, pd.DataFrame]:
    """Compute log-RV per coin and align on common date index.

    Returns
    -------
    log_rv : DataFrame (T, N) — log-RV daily per coin
    rv : DataFrame (T, N) — raw RV (for downstream target alternatives)
    """
    log_rvs: dict[str, pd.Series] = {}
    rvs: dict[str, pd.Series] = {}
    for coin, hourly_rets in coins_data.items():
        rv = daily_realized_variance(hourly_rets)
        log_rv = realized_variance_to_log(rv)
        rvs[coin] = rv
        log_rvs[coin] = log_rv
    rv_df = pd.DataFrame(rvs).dropna()
    log_rv_df = pd.DataFrame(log_rvs).reindex(rv_df.index)
    return log_rv_df, rv_df


def _build_har_features_panel(log_rv_df: pd.DataFrame) -> np.ndarray:
    """Stack per-coin HAR lag features into (T, N, F=4) tensor.

    Each coin contributes [log_rv, rv_d, rv_w, rv_m]. Drops the first 22 rows
    where rv_m is undefined (NaN).
    """
    coins = list(log_rv_df.columns)
    feats_per_coin: list[pd.DataFrame] = []
    for coin in coins:
        # har_lag_features expects raw RV — but we want HAR on log-RV directly
        # because Corsi HAR is fitted on log RV, not RV. Reuse helper by
        # passing log-RV in: it computes lag/mean features which are scale-free.
        s = log_rv_df[coin].rename("rv")  # treated as input series
        df = pd.DataFrame(index=log_rv_df.index)
        df["log_rv"] = s
        df["rv_d"] = s.shift(1)
        df["rv_w"] = s.shift(1).rolling(window=5, min_periods=5).mean()
        df["rv_m"] = s.shift(1).rolling(window=22, min_periods=22).mean()
        feats_per_coin.append(df)
    aligned = pd.concat({c: f for c, f in zip(coins, feats_per_coin)}, axis=1)
    aligned = aligned.dropna()
    # Stack: (T, N, F)
    arr = np.stack(
        [aligned[coin].values for coin in coins], axis=1
    ).astype(np.float32)
    return arr, aligned.index


def _rolling_correlation_adjacency(
    log_rv_df: pd.DataFrame,
    dates: pd.DatetimeIndex,
    window: int = 60,
    top_k: int = 2,
) -> np.ndarray:
    """Compute (T, N, N) dynamic adjacency from rolling correlation of log-RV.

    Top-K per row, symmetrized, self-loops added. Float32.
    """
    n = log_rv_df.shape[1]
    arr = np.zeros((len(dates), n, n), dtype=np.float32)
    for i, t in enumerate(dates):
        end = log_rv_df.index.get_loc(t)
        if end + 1 < window:
            # warm-up: equal-weight adjacency
            adj = (np.ones((n, n)) - np.eye(n)) / max(n - 1, 1)
        else:
            sub = log_rv_df.iloc[end + 1 - window : end + 1].values
            corr = np.corrcoef(sub, rowvar=False)
            adj_full = np.abs(corr)
            np.fill_diagonal(adj_full, 0.0)
            # Top-K per row
            adj = np.zeros_like(adj_full)
            for r in range(n):
                top = np.argsort(adj_full[r])[-top_k:]
                adj[r, top] = adj_full[r, top]
            # Symmetrize
            adj = np.maximum(adj, adj.T)
        # Add self-loops + row-normalize
        adj = adj + np.eye(n)
        row_sum = adj.sum(axis=1, keepdims=True)
        row_sum[row_sum == 0] = 1.0
        adj = adj / row_sum
        arr[i] = adj.astype(np.float32)
    return arr


DEFAULT_COINS: tuple[str, ...] = ("BTC-USD", "ETH-USD", "SOL-USD")


def build_panel(
    coins: Sequence[str] = DEFAULT_COINS,
    skip_remote: bool = False,
    window_corr: int = 60,
    top_k: int = 2,
) -> CrossAssetPanel:
    """Load BTC + ETH + SOL, build aligned cross-asset HAR panel + adjacency.

    Parameters
    ----------
    coins : sequence of str
        Coin tickers. Default: ("BTC-USD", "ETH-USD", "SOL-USD").
    skip_remote : bool
        If True, skip yfinance fetches (SOL). For tests / offline runs.
    window_corr : int
        Rolling-correlation window for dynamic adjacency.
    top_k : int
        Number of top neighbors kept per node before symmetrization.
    """
    rets: dict[str, pd.Series] = {}
    for coin in coins:
        if coin == "BTC-USD":
            rets[coin] = hourly_log_returns(load_bitstamp_btc())
        elif coin == "ETH-USD":
            rets[coin] = hourly_log_returns(load_binance_eth())
        elif coin == "SOL-USD":
            if skip_remote:
                continue
            rets[coin] = hourly_log_returns(load_yf_intraday("SOL-USD"))
        else:
            if skip_remote:
                raise ValueError(
                    f"unknown coin {coin} and skip_remote=True; cannot fetch"
                )
            rets[coin] = hourly_log_returns(load_yf_intraday(coin))

    if not rets:
        raise RuntimeError("No coin data loaded; check skip_remote and inputs")

    log_rv_df, _rv_df = _aligned_log_rv_panel(rets)
    X, dates = _build_har_features_panel(log_rv_df)
    A = _rolling_correlation_adjacency(log_rv_df, dates, window_corr, top_k)
    return CrossAssetPanel(
        X=X, A=A, dates=dates,
        coins=tuple(rets.keys()),
        log_rv_raw=log_rv_df.loc[dates].copy(),
    )


def to_pyg_batches(panel: CrossAssetPanel) -> list[dict]:
    """Lazy converter: returns a list of per-timestep dicts ready for PyG.

    Each dict: {"x": tensor(N, F), "edge_index": LongTensor(2, E),
    "edge_weight": tensor(E), "date": pd.Timestamp}.

    Note: prefers PyG Batch only at training time (avoids torch import here
    when only feature panel is needed by tests).
    """
    import torch

    out: list[dict] = []
    n = panel.X.shape[1]
    for t in range(panel.X.shape[0]):
        adj = panel.A[t]
        rows, cols = np.nonzero(adj)
        edge_index = torch.tensor(np.stack([rows, cols]), dtype=torch.long)
        edge_weight = torch.tensor(adj[rows, cols], dtype=torch.float32)
        out.append({
            "x": torch.tensor(panel.X[t], dtype=torch.float32),
            "edge_index": edge_index,
            "edge_weight": edge_weight,
            "date": panel.dates[t],
            "n_nodes": n,
        })
    return out
