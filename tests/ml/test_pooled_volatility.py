"""Unit tests for pooled multi-asset volatility model (M3).

Tests verify:
    1. PanelDataset construction, date_range filtering, rolling windows
    2. Diebold-Mariano test with known cases
    3. Panel feature computation (shape, NaN handling, multi-asset)
    4. Per-asset normalization correctness
    5. Model forward pass shape
    6. Verdict logic (BEATS / NO BEATS / INCONCLUSIVE)
    7. End-to-end dry-run with synthetic data
"""

import numpy as np
import pandas as pd
import pytest

from pathlib import Path
import sys

SCRIPT_DIR = (
    Path(__file__).resolve().parent.parent.parent
    / "MyIA.AI.Notebooks"
    / "QuantConnect"
    / "ML-Training-Pipeline"
    / "scripts"
)
sys.path.insert(0, str(SCRIPT_DIR))

from train_pooled_volatility import (
    compute_panel_features,
    get_feature_columns,
    normalize_panel,
    build_model,
    PanelDataset,
    diebold_mariano_test,
    compute_verdict,
)


@pytest.fixture
def synthetic_returns_dict():
    """3 coins x 800 obs synthetic returns."""
    np.random.seed(42)
    coins = ["COIN-A", "COIN-B", "COIN-C"]
    returns_dict = {}
    for i, symbol in enumerate(coins):
        n = 800
        vol = 0.02 + i * 0.01
        ret = pd.Series(
            np.random.randn(n) * vol,
            index=pd.date_range("2022-01-01", periods=n, freq="B"),
            name=symbol,
        )
        returns_dict[symbol] = ret
    return returns_dict


@pytest.fixture
def synthetic_panel(synthetic_returns_dict):
    return compute_panel_features(synthetic_returns_dict)


# ---------------------------------------------------------------------------
# PanelDataset tests
# ---------------------------------------------------------------------------


class TestPanelDataset:
    def test_basic_construction(self, synthetic_panel):
        feat_cols = get_feature_columns(synthetic_panel)
        ds = PanelDataset(synthetic_panel, feat_cols, "target_5d", lookback=30)
        assert len(ds) > 0, "Dataset should have samples"

    def test_sample_shapes(self, synthetic_panel):
        feat_cols = get_feature_columns(synthetic_panel)
        lookback = 30
        ds = PanelDataset(synthetic_panel, feat_cols, "target_5d", lookback=lookback)
        features, asset_id, target = ds[0]
        assert features.shape == (lookback, len(feat_cols)), (
            f"Expected ({lookback}, {len(feat_cols)}), got {features.shape}"
        )
        assert isinstance(asset_id, (int, np.integer))
        assert isinstance(target, (float, np.floating))

    def test_date_range_filtering(self, synthetic_panel):
        feat_cols = get_feature_columns(synthetic_panel)
        lookback = 30

        ds_full = PanelDataset(synthetic_panel, feat_cols, "target_5d", lookback)
        ds_filtered = PanelDataset(
            synthetic_panel, feat_cols, "target_5d", lookback,
            date_range=("2023-01-01", "2023-06-30"),
        )
        assert len(ds_filtered) < len(ds_full), (
            "Filtered dataset should be smaller"
        )
        assert len(ds_filtered) > 0, "Filtered dataset should have some samples"

    def test_multi_asset_samples(self, synthetic_panel):
        feat_cols = get_feature_columns(synthetic_panel)
        ds = PanelDataset(synthetic_panel, feat_cols, "target_5d", lookback=30)
        asset_ids = set()
        # Sample across the whole dataset (panel is sorted by asset)
        for i in range(0, len(ds), max(1, len(ds) // 100)):
            _, aid, _ = ds[i]
            asset_ids.add(int(aid))
        assert len(asset_ids) == 3, f"Expected 3 distinct assets, got {len(asset_ids)}"

    def test_short_series_produces_no_samples(self):
        short_ret = pd.Series(
            np.random.randn(25) * 0.02,
            index=pd.date_range("2024-01-01", periods=25, freq="B"),
            name="SHORT",
        )
        panel = compute_panel_features({"SHORT": short_ret})
        feat_cols = get_feature_columns(panel)
        ds = PanelDataset(panel, feat_cols, "target_5d", lookback=60)
        assert len(ds) == 0, "Short series should produce no samples with lookback=60"


# ---------------------------------------------------------------------------
# Diebold-Mariano test
# ---------------------------------------------------------------------------


class TestDieboldMariano:
    def test_model_clearly_better(self):
        """When model errors are much smaller, DM should detect significance."""
        np.random.seed(42)
        n = 500
        y_true = np.random.randn(n)
        errors_model = np.random.randn(n) * 0.1
        errors_baseline = np.random.randn(n) * 0.5

        result = diebold_mariano_test(errors_model, errors_baseline, h=1)
        # Model better => d = e_model^2 - e_baseline^2 < 0 on average
        assert result["dm_stat"] < 0, "DM stat should be negative when model is better"
        assert result["p_value"] < 0.05, "Should be significant"
        assert result["significant_05"] == True  # noqa: E712
        assert "better" in result["interpretation"].lower()

    def test_equal_accuracy(self):
        """When errors are identical, DM should report no significance."""
        np.random.seed(42)
        errors = np.random.randn(500) * 0.3
        result = diebold_mariano_test(errors, errors, h=1)
        assert result["p_value"] == 1.0 or result["dm_stat"] == 0.0

    def test_baseline_better(self):
        """When baseline errors are smaller, DM stat should be positive."""
        np.random.seed(42)
        n = 500
        errors_model = np.random.randn(n) * 0.5
        errors_baseline = np.random.randn(n) * 0.1

        result = diebold_mariano_test(errors_model, errors_baseline, h=1)
        assert result["dm_stat"] > 0, "DM stat should be positive when baseline is better"
        assert result["significant_05"] == True  # noqa: E712

    def test_multi_horizon_correction(self):
        """DM with h=5 should still work (uses lag correction)."""
        np.random.seed(42)
        n = 300
        e_model = np.random.randn(n) * 0.1
        e_base = np.random.randn(n) * 0.3
        result = diebold_mariano_test(e_model, e_base, h=5)
        assert "dm_stat" in result
        assert result["n_obs"] == n


# ---------------------------------------------------------------------------
# Panel features
# ---------------------------------------------------------------------------


class TestPanelFeatures:
    def test_output_shape(self, synthetic_returns_dict):
        panel = compute_panel_features(synthetic_returns_dict)
        n_coins = len(synthetic_returns_dict)
        min_obs_per_coin = min(len(r) for r in synthetic_returns_dict.values())
        # After dropna (rolling windows + targets), expect fewer rows
        assert len(panel) > n_coins * 100, (
            f"Expected many rows, got {len(panel)}"
        )
        assert panel["asset_id"].nunique() == n_coins

    def test_feature_columns_present(self, synthetic_panel):
        expected = {"ret_1d", "ret_5d", "ret_20d", "vol_5d", "vol_20d",
                    "rv_5d", "rv_20d", "skew_20d", "autocorr_5d"}
        feat_cols = set(get_feature_columns(synthetic_panel))
        assert expected == feat_cols, f"Missing: {expected - feat_cols}"

    def test_targets_present(self, synthetic_panel):
        for h in [1, 5, 20]:
            assert f"target_{h}d" in synthetic_panel.columns

    def test_no_nan_after_dropna(self, synthetic_panel):
        assert not synthetic_panel.isna().any().any(), "Panel should have no NaN"


# ---------------------------------------------------------------------------
# Normalization
# ---------------------------------------------------------------------------


class TestNormalizePanel:
    def test_per_asset_zero_mean_unit_var(self, synthetic_panel):
        feat_cols = get_feature_columns(synthetic_panel)
        normed, stats = normalize_panel(synthetic_panel, feat_cols, method="per_asset")
        for asset_id in normed["asset_id"].unique():
            mask = normed["asset_id"] == asset_id
            for col in feat_cols:
                vals = normed.loc[mask, col]
                np.testing.assert_allclose(
                    vals.mean(), 0.0, atol=0.02,
                    err_msg=f"Asset {asset_id} col {col} mean not ~0",
                )
                np.testing.assert_allclose(
                    vals.std(), 1.0, atol=0.02,
                    err_msg=f"Asset {asset_id} col {col} std not ~1",
                )

    def test_global_normalization(self, synthetic_panel):
        feat_cols = get_feature_columns(synthetic_panel)
        normed, stats = normalize_panel(synthetic_panel, feat_cols, method="global")
        for col in feat_cols:
            np.testing.assert_allclose(
                normed[col].mean(), 0.0, atol=0.02,
                err_msg=f"Global col {col} mean not ~0",
            )

    def test_stats_dict_populated(self, synthetic_panel):
        feat_cols = get_feature_columns(synthetic_panel)
        _, stats = normalize_panel(synthetic_panel, feat_cols, method="per_asset")
        assert len(stats) > 0
        # Should have (asset_id, col) keys
        for key in list(stats.keys())[:3]:
            assert len(key) == 2, f"Expected (asset_id, col) tuple key, got {key}"


# ---------------------------------------------------------------------------
# Model architecture
# ---------------------------------------------------------------------------


class TestBuildModel:
    def test_forward_pass_shape(self):
        import torch

        n_features = 9
        n_assets = 3
        batch = 16
        seq_len = 30

        model = build_model(n_features, n_assets, embed_dim=8, lstm_hidden=32, lstm_layers=1)
        x = torch.randn(batch, seq_len, n_features)
        ids = torch.randint(0, n_assets, (batch,))

        out = model(x, ids)
        assert out.shape == (batch,), f"Expected ({batch},), got {out.shape}"

    def test_embedding_dimension(self):
        import torch

        model = build_model(9, 5, embed_dim=16)
        emb = model.asset_embedding
        assert emb.weight.shape == (5, 16), f"Wrong embedding shape: {emb.weight.shape}"


# ---------------------------------------------------------------------------
# Verdict logic
# ---------------------------------------------------------------------------


class TestComputeVerdict:
    def _make_results(self, asset_mses, garch_mses, symbol_to_id):
        pooled = {
            "horizon": 5,
            "seeds": [
                {"seed": 0, "asset_mses": asset_mses, "mean_mse": 0.5, "fold_metrics": []},
                {"seed": 1, "asset_mses": asset_mses, "mean_mse": 0.5, "fold_metrics": []},
            ],
            "aggregate_mse": 0.5,
        }
        return compute_verdict(pooled, garch_mses, symbol_to_id)

    def test_beats_verdict(self):
        """When pooled beats GARCH on all assets by >5%."""
        symbol_to_id = {"A": 0, "B": 1, "C": 2}
        asset_mses = {0: 0.5, 1: 0.6, 2: 0.7}
        garch_mses = {"A": 1.0, "B": 1.0, "C": 1.0}
        result = self._make_results(asset_mses, garch_mses, symbol_to_id)
        assert result["verdict"] == "BEATS", f"Expected BEATS, got {result['verdict']}"
        assert result["n_pooled_better"] == 3

    def test_no_beats_verdict(self):
        """When GARCH beats pooled on most assets."""
        symbol_to_id = {"A": 0, "B": 1, "C": 2}
        asset_mses = {0: 2.0, 1: 2.0, 2: 2.0}
        garch_mses = {"A": 1.0, "B": 1.0, "C": 1.0}
        result = self._make_results(asset_mses, garch_mses, symbol_to_id)
        assert result["verdict"] == "NO BEATS", f"Expected NO BEATS, got {result['verdict']}"

    def test_inconclusive_verdict(self):
        """Mixed results = INCONCLUSIVE."""
        symbol_to_id = {"A": 0, "B": 1, "C": 2, "D": 3, "E": 4}
        asset_mses = {0: 0.9, 1: 0.9, 2: 1.1, 3: 1.1, 4: 1.1}
        garch_mses = {"A": 1.0, "B": 1.0, "C": 1.0, "D": 1.0, "E": 1.0}
        result = self._make_results(asset_mses, garch_mses, symbol_to_id)
        # 2/5 better = 40% => doesn't hit 60% threshold => INCONCLUSIVE or NO BEATS
        assert result["verdict"] in ("INCONCLUSIVE", "NO BEATS")

    def test_empty_comparisons(self):
        symbol_to_id = {"A": 0}
        pooled = {
            "horizon": 5,
            "seeds": [{"seed": 0, "asset_mses": {}, "mean_mse": 0.5, "fold_metrics": []}],
            "aggregate_mse": 0.5,
        }
        result = compute_verdict(pooled, {"Z": 1.0}, symbol_to_id)
        assert result["verdict"] == "INCONCLUSIVE"
