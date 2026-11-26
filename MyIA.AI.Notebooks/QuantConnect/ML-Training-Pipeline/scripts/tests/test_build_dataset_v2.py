"""Tests for build_dataset_v2.py — dataset V2 builder."""

import inspect
import sys
from pathlib import Path

import numpy as np
import pandas as pd
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))

from build_dataset_v2 import (
    PANIER_SYMBOLS,
    build_arg_parser,
    build_dataset_v2,
    build_features_for_symbol,
    build_provenance_manifest,
    load_auxiliary_series,
)


@pytest.fixture
def synthetic_panier():
    """3-asset synthetic panier with enough rows for features."""
    np.random.seed(42)
    T = 500
    dates = pd.date_range("2020-01-01", periods=T, freq="B")
    panier = {}
    for sym, vol in [("SPY", 0.01), ("TLT", 0.008), ("DBC", 0.012)]:
        returns = np.random.randn(T).astype(np.float32) * vol
        close = (1 + pd.Series(returns)).cumprod() * 100
        panier[sym] = pd.DataFrame(
            {
                "Close": close.values,
                "Open": close.values * (1 + np.random.normal(0, 0.002, T)),
                "High": close.values * (1 + np.abs(np.random.normal(0, 0.005, T))),
                "Low": close.values * (1 - np.abs(np.random.normal(0, 0.005, T))),
                "Volume": np.abs(np.random.randn(T)) * 1e6,
            },
            index=dates,
        )
    return panier


class TestLoadAuxiliarySeries:
    def test_extracts_bond(self, synthetic_panier):
        aux = load_auxiliary_series(synthetic_panier)
        assert "bond" in aux
        assert len(aux["bond"]) > 0

    def test_extracts_commodity(self, synthetic_panier):
        aux = load_auxiliary_series(synthetic_panier)
        assert "commodity" in aux

    def test_extracts_equity(self, synthetic_panier):
        aux = load_auxiliary_series(synthetic_panier)
        assert "equity_index" in aux


class TestBuildFeaturesForSymbol:
    def test_price_regime(self, synthetic_panier):
        aux = load_auxiliary_series(synthetic_panier)
        features = build_features_for_symbol(
            "SPY", synthetic_panier["SPY"], aux, regime_method="price",
        )
        assert features is not None
        assert "regime_price" in features.columns
        assert "target" in features.columns
        assert len(features) > 0

    def test_hmm_regime(self, synthetic_panier):
        aux = load_auxiliary_series(synthetic_panier)
        features = build_features_for_symbol(
            "SPY", synthetic_panier["SPY"], aux, regime_method="hmm",
        )
        assert features is not None
        assert "regime_hmm" in features.columns

    def test_both_regimes(self, synthetic_panier):
        aux = load_auxiliary_series(synthetic_panier)
        features = build_features_for_symbol(
            "SPY", synthetic_panier["SPY"], aux, regime_method="both",
        )
        assert features is not None
        assert "regime_price" in features.columns
        assert "regime_hmm" in features.columns

    def test_cross_asset_features(self, synthetic_panier):
        aux = load_auxiliary_series(synthetic_panier)
        features = build_features_for_symbol(
            "SPY", synthetic_panier["SPY"], aux, regime_method="price",
        )
        assert "bond_equity_ratio" in features.columns
        assert "commodity_momentum" in features.columns
        assert "equity_strength" in features.columns

    def test_insufficient_data(self):
        short_df = pd.DataFrame(
            {"Close": [100, 101, 102], "Volume": [1e6, 1e6, 1e6]},
            index=pd.date_range("2020-01-01", periods=3),
        )
        result = build_features_for_symbol("SHORT", short_df, {})
        assert result is None

    def test_no_aux(self, synthetic_panier):
        features = build_features_for_symbol(
            "SPY", synthetic_panier["SPY"], {}, regime_method="price",
        )
        assert features is not None
        # Cross-asset features should be absent
        assert "bond_equity_ratio" not in features.columns

    def test_target_is_forward_return(self, synthetic_panier):
        aux = load_auxiliary_series(synthetic_panier)
        features = build_features_for_symbol(
            "SPY", synthetic_panier["SPY"], aux, regime_method="price",
        )
        assert "target" in features.columns
        # Target should be binary-like (forward return)
        valid = features["target"].dropna()
        assert valid.abs().max() < 1.0  # returns shouldn't exceed 100%

    def test_regime_labels_valid(self, synthetic_panier):
        aux = load_auxiliary_series(synthetic_panier)
        features = build_features_for_symbol(
            "SPY", synthetic_panier["SPY"], aux, regime_method="price",
        )
        valid_regimes = {"uptrend", "downtrend", "volatility", "black_swan", "normal"}
        regime_values = set(features["regime_price"].unique())
        assert regime_values.issubset(valid_regimes)


class TestRegimeDecodeProvenance:
    """#21054: the HMM decode mode is a recorded parameter, not a comment.

    A retrospective (Viterbi) label column and a causal (filtered) one are
    byte-indistinguishable once they live in a parquet. Before this change
    the only place the distinction existed was a source comment in
    ``regime_detector.py`` -- i.e. nowhere a *consumer of the dataset* would
    look. These tests hold the two halves together: the parameter must
    actually change the column (else the provenance record would lie), and
    the record must say which one produced it.
    """

    def test_default_decode_remains_viterbi(self):
        """Backward compatibility: existing dataset builds stay reproducible.

        Flipping the default would silently rewrite the content of every
        rebuilt dataset. The causal mode is opted into, never inherited.
        """
        sig = inspect.signature(build_dataset_v2)
        assert sig.parameters["regime_decode"].default == "viterbi"
        assert inspect.signature(build_features_for_symbol).parameters[
            "regime_decode"
        ].default == "viterbi"

    def test_decode_mode_is_operative(self, synthetic_panier):
        """The parameter must really change the column.

        Measured on this fixture: 14/300 labels differ between the two
        decodes. If a future refactor dropped the pass-through, the two
        columns would become identical while the manifest kept claiming a
        difference -- the provenance record would lie.
        """
        aux = load_auxiliary_series(synthetic_panier)
        vit = build_features_for_symbol(
            "SPY", synthetic_panier["SPY"], aux,
            regime_method="hmm", regime_decode="viterbi",
        )
        filt = build_features_for_symbol(
            "SPY", synthetic_panier["SPY"], aux,
            regime_method="hmm", regime_decode="filter",
        )
        assert vit is not None and filt is not None
        n_diff = int((vit["regime_hmm"].values != filt["regime_hmm"].values).sum())
        assert n_diff > 0, (
            "regime_decode is inoperative: viterbi and filter produced "
            "identical regime_hmm columns, so the provenance manifest "
            "would report a distinction that does not exist"
        )

    def test_decode_mode_recorded_in_attrs(self, synthetic_panier):
        """The mode travels with the frame until the manifest is written."""
        aux = load_auxiliary_series(synthetic_panier)
        filt = build_features_for_symbol(
            "SPY", synthetic_panier["SPY"], aux,
            regime_method="hmm", regime_decode="filter",
        )
        assert filt is not None
        assert filt.attrs["regime_decode"] == "filter"

    def test_invalid_decode_rejected_before_any_io(self, tmp_path):
        """An unknown mode fails fast, before data loading."""
        with pytest.raises(ValueError, match="regime_decode"):
            build_dataset_v2(regime_decode="smooth", output_dir=tmp_path)

    def test_manifest_marks_viterbi_retrospective(self):
        frame = pd.DataFrame({"a": [1.0, 2.0]})
        manifest = build_provenance_manifest(
            {"SPY": frame}, regime_method="hmm", regime_decode="viterbi",
            start="2020-01-01", end="2021-01-01",
        )
        assert manifest["regime_decode"] == "viterbi"
        assert manifest["regime_hmm_decode_forward_only"] is False
        assert "RETROSPECTIVE" in manifest["lookahead_note"]
        assert "Do NOT use it as a known-at-t" in manifest["lookahead_note"]
        assert manifest["symbols"]["SPY"] == {"rows": 2, "columns": 1}

    def test_manifest_filter_does_not_promise_known_at_t(self):
        """The manifest must not grant a guarantee the builder cannot keep.

        The filtered decode is forward-only at FIXED parameters; the HMM fit
        still sees the whole window, so past labels change when the window
        grows (measured on the synthetic fixture: 67/150 past labels flip
        when the series is extended). A note claiming the column is usable
        as a known-at-t walk-forward feature would therefore be false.
        """
        manifest = build_provenance_manifest(
            {"SPY": pd.DataFrame({"a": [1.0]})},
            regime_method="both", regime_decode="filter",
            start="2020-01-01", end="2021-01-01",
        )
        assert manifest["regime_hmm_decode_forward_only"] is True
        note = manifest["lookahead_note"]
        assert "FORWARD-ONLY DECODE" in note
        assert "whole window" in note
        assert "NOT known-at-t" in note
        assert "Do NOT use this column as a known-at-t" in note
        assert "regime_hmm_causal" not in manifest
        # The price-based column is causal by construction (#21111) and the
        # manifest says so, so a reader does not have to re-derive it.
        assert manifest["regime_price_causal"] is True

    def test_manifest_omits_regime_keys_for_absent_columns(self):
        """A price-only build has no regime_hmm column: no hmm keys, no note."""
        manifest = build_provenance_manifest(
            {"SPY": pd.DataFrame({"a": [1.0]})},
            regime_method="price", regime_decode="viterbi",
            start="2020-01-01", end="2021-01-01",
        )
        assert "regime_hmm_decode_forward_only" not in manifest
        assert "regime_hmm_causal" not in manifest
        assert "lookahead_note" not in manifest
        assert manifest["regime_price_causal"] is True

    def test_builder_writes_provenance_manifest_on_disk(
        self, synthetic_panier, tmp_path, monkeypatch
    ):
        """Cover the last mile: build_dataset_v2 -> _provenance.json on disk.

        The manifest builder is unit-tested on its own, but nothing held the
        write that follows the per-symbol loop (path, valid JSON, content).
        The panier loader is stubbed on the synthetic fixture so the test
        stays hermetic: a virgin CI runner has neither the local CSV cache
        nor a network provider for SPY.
        """
        monkeypatch.setattr(
            sys.modules["build_dataset_v2"],
            "load_panier_data",
            lambda symbols, start, end, data_dir=None: {
                "SPY": synthetic_panier["SPY"]
            },
        )
        out = tmp_path / "datasets"
        results = build_dataset_v2(
            symbols=["SPY"], regime_method="price", output_dir=out,
        )
        assert set(results) == {"SPY"}
        manifest_path = out / "_provenance.json"
        assert manifest_path.is_file()
        import json

        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        assert manifest["schema"] == 1
        assert manifest["regime_method"] == "price"
        assert "lookahead_note" not in manifest
        assert manifest["regime_price_causal"] is True
        assert manifest["symbols"]["SPY"]["rows"] == len(results["SPY"])

    def test_cli_flag_is_wired_to_the_parameter(self):
        parser = build_arg_parser()
        assert parser.parse_args([]).regime_decode == "viterbi"
        assert parser.parse_args(["--regime-decode", "filter"]).regime_decode == "filter"
        with pytest.raises(SystemExit):
            parser.parse_args(["--regime-decode", "smooth"])


class TestPanierSymbols:
    def test_has_crypto(self):
        assert any("BTC" in s for s in PANIER_SYMBOLS)

    def test_has_bonds(self):
        assert "TLT" in PANIER_SYMBOLS

    def test_has_commodities(self):
        assert "GLD" in PANIER_SYMBOLS

    def test_no_faang(self):
        faang = {"AAPL", "MSFT", "GOOG", "AMZN", "NVDA", "TSLA", "META"}
        assert not faang.intersection(set(PANIER_SYMBOLS))
