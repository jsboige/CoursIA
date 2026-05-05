"""Tests for data_utils.py -- data loading and generation utilities."""

import sys
from pathlib import Path

import numpy as np
import pandas as pd
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))

from data_utils import compute_data_hash, generate_synthetic_data, load_data


class TestGenerateSyntheticData:
    def test_shape(self):
        df = generate_synthetic_data(500)
        assert len(df) == 500

    def test_columns(self):
        df = generate_synthetic_data(100)
        for col in ["Close", "Open", "High", "Low", "Volume"]:
            assert col in df.columns

    def test_deterministic(self):
        df1 = generate_synthetic_data(100)
        df2 = generate_synthetic_data(100)
        pd.testing.assert_frame_equal(df1, df2)

    def test_positive_prices(self):
        df = generate_synthetic_data(500)
        assert (df["Close"] > 0).all()
        assert (df["High"] >= df["Close"]).all()
        assert (df["Low"] <= df["Close"]).all()

    def test_positive_volume(self):
        df = generate_synthetic_data(100)
        assert (df["Volume"] > 0).all()

    def test_datetime_index(self):
        df = generate_synthetic_data(100)
        assert isinstance(df.index, pd.DatetimeIndex)

    def test_default_size(self):
        df = generate_synthetic_data()
        assert len(df) == 5000


class TestComputeDataHash:
    def test_returns_string(self):
        df = generate_synthetic_data(50)
        h = compute_data_hash(df)
        assert isinstance(h, str)
        assert len(h) == 16

    def test_deterministic(self):
        df = generate_synthetic_data(50)
        h1 = compute_data_hash(df)
        h2 = compute_data_hash(df)
        assert h1 == h2

    def test_different_data_different_hash(self):
        df1 = generate_synthetic_data(50)
        df2 = generate_synthetic_data(100)
        assert compute_data_hash(df1) != compute_data_hash(df2)


class TestLoadData:
    def test_file_not_found(self, tmp_path):
        with pytest.raises(FileNotFoundError, match="No CSV files found"):
            load_data(tmp_path, "NOSUCH")

    def test_load_csv(self, tmp_path):
        dates = pd.date_range("2020-01-01", periods=50, freq="B")
        df = pd.DataFrame(
            {
                "Close": np.random.randn(50).cumsum() + 100,
                "Volume": np.abs(np.random.randn(50)) * 1e6,
            },
            index=dates,
        )
        csv_path = tmp_path / "SPY_2020-01-01_2020-03-01.csv"
        df.to_csv(csv_path)

        loaded = load_data(tmp_path, "SPY")
        assert len(loaded) == 50
        assert "Close" in loaded.columns

    def test_date_filter(self, tmp_path):
        dates = pd.date_range("2020-01-01", periods=100, freq="B")
        df = pd.DataFrame(
            {"Close": np.arange(100, dtype=float), "Volume": np.ones(100) * 1e6},
            index=dates,
        )
        csv_path = tmp_path / "SPY_2020.csv"
        df.to_csv(csv_path)

        loaded = load_data(tmp_path, "SPY", start="2020-02-01", end="2020-03-01")
        assert len(loaded) < 100
        assert loaded.index.min() >= pd.Timestamp("2020-02-01")
