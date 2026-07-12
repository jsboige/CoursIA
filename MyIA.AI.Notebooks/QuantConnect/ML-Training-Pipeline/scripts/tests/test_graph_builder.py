"""Tests for graph_builder module."""

import numpy as np
import pandas as pd
import pytest

from graph_builder import (
    CRYPTO_PANIER_SYMBOLS,
    CryptoGraphBuilder,
    build_sector_adjacency_crypto,
    compute_graph_features,
)


@pytest.fixture
def synthetic_returns():
    """4-asset synthetic returns, 500 days."""
    np.random.seed(42)
    T, N = 500, 4
    symbols = ["BTC-USD", "ETH-USD", "LTC-USD", "XRP-USD"]
    data = np.random.randn(T, N).astype(np.float32) * 0.02
    # Add correlation between BTC and ETH
    data[:, 1] += 0.5 * data[:, 0]
    return pd.DataFrame(data, columns=symbols)


class TestCryptoGraphBuilder:
    def test_init(self, synthetic_returns):
        builder = CryptoGraphBuilder(synthetic_returns, window=60)
        assert builder.n_assets == 4
        assert builder.window == 60

    def test_static_correlation(self, synthetic_returns):
        builder = CryptoGraphBuilder(synthetic_returns, window=60)
        adj = builder.build_static_adjacency(method="correlation", threshold=0.3)
        assert adj.shape == (4, 4)
        assert np.allclose(np.diag(adj), 0.0)  # no self-loops after threshold
        # BTC-ETH should be connected (correlated)
        assert adj[0, 1] > 0 or adj[1, 0] > 0

    def test_static_distance(self, synthetic_returns):
        builder = CryptoGraphBuilder(synthetic_returns, window=60)
        adj = builder.build_static_adjacency(method="distance", threshold=0.1)
        assert adj.shape == (4, 4)
        assert np.all(adj >= 0) and np.all(adj <= 1)

    def test_static_partial_correlation(self, synthetic_returns):
        builder = CryptoGraphBuilder(synthetic_returns, window=60)
        adj = builder.build_static_adjacency(method="partial_correlation", threshold=0.1)
        assert adj.shape == (4, 4)

    def test_unknown_method_raises(self, synthetic_returns):
        builder = CryptoGraphBuilder(synthetic_returns, window=60)
        with pytest.raises(ValueError, match="Unknown method"):
            builder.build_static_adjacency(method="invalid")

    def test_symmetric_normalization(self, synthetic_returns):
        builder = CryptoGraphBuilder(synthetic_returns, window=60)
        adj = builder.build_static_adjacency(method="correlation", threshold=0.1)
        # Symmetric
        assert np.allclose(adj, adj.T, atol=1e-5)

    def test_dynamic_adjacency_shape(self, synthetic_returns):
        builder = CryptoGraphBuilder(synthetic_returns, window=60)
        adjs = builder.build_dynamic_adjacency(method="correlation", threshold=0.3)
        assert adjs.shape[0] == len(synthetic_returns) - 60 + 1
        assert adjs.shape[1] == 4
        assert adjs.shape[2] == 4

    def test_to_edge_index(self, synthetic_returns):
        builder = CryptoGraphBuilder(synthetic_returns, window=60)
        adj = builder.build_static_adjacency(method="correlation", threshold=0.3)
        edge_index, edge_attr = builder.to_edge_index(adj)
        assert edge_index.shape[0] == 2
        assert edge_index.shape[1] == edge_attr.shape[0]
        assert edge_index.dtype == np.int64
        assert edge_attr.dtype == np.float32


class TestSectorAdjacency:
    def test_shape(self):
        adj = build_sector_adjacency_crypto()
        assert adj.shape == (10, 10)

    def test_self_loops(self):
        adj = build_sector_adjacency_crypto()
        assert np.all(np.diag(adj) == 1.0)

    def test_btc_eth_connected(self):
        adj = build_sector_adjacency_crypto()
        # BTC=0, ETH=1 (majors group)
        assert adj[0, 1] == 1.0
        assert adj[1, 0] == 1.0

    def test_symmetric(self):
        adj = build_sector_adjacency_crypto()
        assert np.allclose(adj, adj.T)


class TestComputeGraphFeatures:
    def test_output_shape(self, synthetic_returns):
        closes = (1 + synthetic_returns).cumprod() * 100
        features = compute_graph_features(closes, lookback=20)
        assert len(features.columns) == len(closes.columns) * 4  # ret, vol, mom, skew
        assert len(features) < len(closes)  # NaN dropped

    def test_no_nan(self, synthetic_returns):
        closes = (1 + synthetic_returns).cumprod() * 100
        features = compute_graph_features(closes, lookback=20)
        assert not features.isna().any().any()


class TestCryptoPanierSymbols:
    def test_10_symbols(self):
        assert len(CRYPTO_PANIER_SYMBOLS) == 10

    def test_btc_first(self):
        assert CRYPTO_PANIER_SYMBOLS[0] == "BTC-USD"
