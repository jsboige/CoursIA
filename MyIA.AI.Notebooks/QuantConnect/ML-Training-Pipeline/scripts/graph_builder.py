"""
Graph construction utilities for multi-asset GNN on crypto panier.

Builds dynamic adjacency matrices from rolling correlations and other
distance measures for use with GCN/GAT/RGCN models.

Crypto panier: 10 coins (BTC, ETH, LTC, XRP, ADA, LINK, SOL, MATIC, AVAX, DOT)
Data: daily OHLCV, 2018-2026.

References:
    - MDGNN (AAAI 2024): multi-relational dynamic graphs
    - Temporal GAT (Mathematics 14(2), 2026): GAT with temporal spillover
    - Kipf & Welling, "Semi-Supervised Classification with GCN" (ICLR 2017)

Usage:
    from graph_builder import CryptoGraphBuilder

    builder = CryptoGraphBuilder(returns_df, window=60)
    adj = builder.build_adjacency(method="correlation", threshold=0.3)
    edge_index, edge_attr = builder.to_edge_index(adj)
"""

from __future__ import annotations

from pathlib import Path

import numpy as np
import pandas as pd

CRYPTO_PANIER_SYMBOLS = [
    "BTC-USD", "ETH-USD", "LTC-USD", "XRP-USD", "ADA-USD",
    "LINK-USD", "SOL-USD", "MATIC-USD", "AVAX-USD", "DOT-USD",
]

CRYPTO_PANIER_DIR = (
    Path(__file__).resolve().parent.parent.parent
    / "datasets" / "yfinance" / "crypto_panier"
)


def load_crypto_panier(
    start: str | None = None,
    end: str | None = None,
    symbols: list[str] | None = None,
) -> pd.DataFrame:
    """Load aligned close prices for crypto panier.

    Returns DataFrame indexed by Date with columns = symbols.
    Only includes dates where ALL selected symbols have data.
    """
    symbols = symbols or CRYPTO_PANIER_SYMBOLS
    closes = {}
    for symbol in symbols:
        matches = list(CRYPTO_PANIER_DIR.glob(f"{symbol}_*.csv"))
        if not matches:
            continue
        df = pd.read_csv(matches[0], index_col=0, parse_dates=True)
        closes[symbol] = df["Close"]

    panel = pd.DataFrame(closes).dropna()
    if start:
        panel = panel[panel.index >= start]
    if end:
        panel = panel[panel.index <= end]
    return panel


class CryptoGraphBuilder:
    """Build dynamic graph structures from multi-asset return data.

    Parameters
    ----------
    returns : pd.DataFrame
        Asset returns, shape (T, N) where N = number of assets.
    window : int
        Rolling window size for dynamic adjacency computation.
    """

    def __init__(self, returns: pd.DataFrame, window: int = 60):
        self.returns = returns
        self.window = window
        self.symbols = list(returns.columns)
        self.n_assets = len(self.symbols)

    def build_static_adjacency(
        self,
        method: str = "correlation",
        threshold: float = 0.3,
    ) -> np.ndarray:
        """Build a single static adjacency matrix from full-sample stats.

        Parameters
        ----------
        method : str
            "correlation" | "partial_correlation" | "distance"
        threshold : float
            Minimum absolute value to keep an edge.

        Returns
        -------
        np.ndarray, shape (N, N), values in [0, 1].
        """
        if method == "correlation":
            corr = self.returns.corr().values
            adj = np.abs(corr)
            np.fill_diagonal(adj, 0.0)
            adj[adj < threshold] = 0.0

        elif method == "partial_correlation":
            corr = self.returns.corr().values
            try:
                prec = np.linalg.inv(corr)
                d = np.diag(1.0 / np.sqrt(np.diag(prec)))
                partial = -d @ prec @ d
                np.fill_diagonal(partial, 1.0)
                adj = np.abs(partial)
                np.fill_diagonal(adj, 0.0)
                adj[adj < threshold] = 0.0
            except np.linalg.LinAlgError:
                adj = np.abs(corr)
                np.fill_diagonal(adj, 0.0)
                adj[adj < threshold] = 0.0

        elif method == "distance":
            corr = self.returns.corr().values
            dist = np.sqrt(2.0 * (1.0 - corr))
            np.fill_diagonal(dist, 0.0)
            max_dist = dist.max()
            adj = 1.0 - dist / max_dist if max_dist > 0 else dist
            adj[adj < threshold] = 0.0

        else:
            raise ValueError(f"Unknown method: {method}")

        # Row-normalize (symmetric normalization for GCN)
        adj = self._sym_normalize(adj)
        return adj.astype(np.float32)

    def build_dynamic_adjacency(
        self,
        method: str = "correlation",
        threshold: float = 0.3,
        continuous: bool = False,
    ) -> np.ndarray:
        """Build dynamic adjacency matrices via rolling correlations.

        Parameters
        ----------
        continuous : bool
            If True, keep continuous correlation values instead of
            binary thresholding. Preserves edge weight magnitude.

        Returns
        -------
        np.ndarray, shape (T - window + 1, N, N).
        One adjacency matrix per valid time step.
        """
        T = len(self.returns)
        n_valid = T - self.window + 1
        adjs = np.zeros((n_valid, self.n_assets, self.n_assets), dtype=np.float32)

        returns_arr = self.returns.values

        for t in range(n_valid):
            window_data = returns_arr[t : t + self.window]
            if method == "correlation":
                corr = np.corrcoef(window_data, rowvar=False)
                adj = np.abs(corr)
                np.fill_diagonal(adj, 0.0)
                if not continuous:
                    adj[adj < threshold] = 0.0
            elif method == "distance":
                corr = np.corrcoef(window_data, rowvar=False)
                dist = np.sqrt(np.maximum(2.0 * (1.0 - corr), 0.0))
                np.fill_diagonal(dist, 0.0)
                max_dist = dist.max()
                adj = 1.0 - dist / max_dist if max_dist > 0 else dist
                if not continuous:
                    adj[adj < threshold] = 0.0
            else:
                corr = np.corrcoef(window_data, rowvar=False)
                adj = np.abs(corr)
                np.fill_diagonal(adj, 0.0)
                if not continuous:
                    adj[adj < threshold] = 0.0

            adj = self._sym_normalize(adj)
            adjs[t] = adj.astype(np.float32)

        return adjs

    def to_edge_index(self, adj: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
        """Convert dense adjacency matrix to PyG-compatible edge_index + edge_attr.

        Parameters
        ----------
        adj : np.ndarray, shape (N, N)
            Adjacency matrix with values in [0, 1].

        Returns
        -------
        edge_index : np.ndarray, shape (2, E)
            Source/target node indices.
        edge_attr : np.ndarray, shape (E,)
            Edge weights.
        """
        rows, cols = np.where(adj > 0)
        edge_index = np.stack([rows, cols], axis=0)
        edge_attr = adj[rows, cols]
        return edge_index.astype(np.int64), edge_attr.astype(np.float32)

    @staticmethod
    def _sym_normalize(adj: np.ndarray) -> np.ndarray:
        """Symmetric normalization: D^{-1/2} A D^{-1/2}."""
        degree = adj.sum(axis=1)
        safe_degree = np.where(degree > 0, degree, 1.0)
        d_inv_sqrt = np.where(degree > 0, 1.0 / np.sqrt(safe_degree), 0.0)
        d_mat = np.diag(d_inv_sqrt)
        return d_mat @ adj @ d_mat


def build_sector_adjacency_crypto() -> np.ndarray:
    """Build sector-based adjacency for crypto panier.

    Groups:
        - majors: BTC, ETH
        - payment: LTC, XRP, ADA
        - defi: LINK, DOT, AVAX
        - l2: SOL, MATIC

    Fully connected within group, 0 between groups.
    """
    n = len(CRYPTO_PANIER_SYMBOLS)
    groups = {
        "majors": [0, 1],       # BTC, ETH
        "payment": [2, 3, 4],   # LTC, XRP, ADA
        "defi": [5, 7, 8],      # LINK, DOT, AVAX
        "l2": [6, 9],           # SOL, MATIC
    }

    adj = np.zeros((n, n), dtype=np.float32)
    for indices in groups.values():
        for i in indices:
            for j in indices:
                if i != j:
                    adj[i, j] = 1.0

    np.fill_diagonal(adj, 1.0)
    return adj


def compute_graph_features(
    closes: pd.DataFrame,
    lookback: int = 20,
) -> pd.DataFrame:
    """Compute per-asset features suitable for GNN node features.

    For each asset: returns, volatility, volume change, RSI-like momentum.
    """
    features = pd.DataFrame(index=closes.index)
    returns = closes.pct_change()

    for col in closes.columns:
        features[f"ret_{col}"] = returns[col]
        features[f"vol_{col}"] = returns[col].rolling(lookback).std()
        features[f"mom_{col}"] = returns[col].rolling(lookback).sum()
        features[f"skew_{col}"] = returns[col].rolling(lookback).skew()

    return features.dropna()
