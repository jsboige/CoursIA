"""Tests for qc_objectstore.py — QC ObjectStore integration."""

import sys
from pathlib import Path

import pandas as pd
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))

from qc_objectstore import generate_qc_loader_code, prepare_for_upload


@pytest.fixture
def dataset_v2_dir(tmp_path):
    """Create a minimal Dataset V2 directory with Parquet files."""
    for sym in ["SPY", "BTC_USD", "TLT"]:
        df = pd.DataFrame(
            {
                "ret_1d": [0.01, -0.02, 0.03],
                "rsi_14": [55.0, 45.0, 60.0],
                "target": [0.02, -0.01, 0.01],
                "regime_price": ["uptrend", "downtrend", "uptrend"],
            },
            index=pd.date_range("2024-01-01", periods=3),
        )
        df.to_parquet(tmp_path / f"{sym}_v2.parquet")
    return tmp_path


class TestPrepareForUpload:
    def test_discovers_parquet_files(self, dataset_v2_dir):
        files = prepare_for_upload(dataset_v2_dir)
        assert len(files) == 3
        assert all(k.startswith("ml-datasets/v2/") for k in files.keys())

    def test_filters_by_symbol(self, dataset_v2_dir):
        files = prepare_for_upload(dataset_v2_dir, symbols=["SPY"])
        assert len(files) == 1
        assert "SPY" in list(files.keys())[0]

    def test_validates_target_column(self, tmp_path):
        df = pd.DataFrame({"ret_1d": [0.01]}, index=pd.date_range("2024-01-01", periods=1))
        df.to_parquet(tmp_path / "BAD_v2.parquet")
        files = prepare_for_upload(tmp_path)
        assert len(files) == 0

    def test_skips_empty_files(self, tmp_path):
        df = pd.DataFrame({"target": pd.Series(dtype=float)})
        df.to_parquet(tmp_path / "EMPTY_v2.parquet")
        files = prepare_for_upload(tmp_path)
        assert len(files) == 0

    def test_missing_dir(self):
        with pytest.raises(FileNotFoundError):
            prepare_for_upload("/nonexistent/path")

    def test_no_parquet_files(self, tmp_path):
        with pytest.raises(FileNotFoundError):
            prepare_for_upload(tmp_path)

    def test_key_format(self, dataset_v2_dir):
        files = prepare_for_upload(dataset_v2_dir)
        for key in files.keys():
            assert key.startswith("ml-datasets/v2/")
            assert key.endswith("_v2.parquet")


class TestUploadViaMCP:
    def test_dry_run(self, dataset_v2_dir):
        from qc_objectstore import upload_via_mcp

        files = prepare_for_upload(dataset_v2_dir)
        result = upload_via_mcp(files, "test-org", dry_run=True)
        assert len(result) == 3


class TestGenerateQCLoaderCode:
    def test_returns_string(self):
        code = generate_qc_loader_code()
        assert isinstance(code, str)
        assert "load_features_from_objectstore" in code
        assert "ObjectStore" in code
        assert "read_parquet" in code
