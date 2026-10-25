"""
Dataset V2 builder: panier + Stage 2 features + regime labels.

Integrates:
    1. Anti-bias panier data (26 symbols, 7 asset classes)
    2. Stage 2 feature engineering (cross-asset, VIX, macro)
    3. Regime labels (price-based + HMM)

Output: per-symbol Parquet files with features + regime columns,
ready for MoE walk-forward training.

Issue #754 Phase C: data quality + features + regime labels.

Usage:
    python build_dataset_v2.py --output-dir datasets_v2/
    python build_dataset_v2.py --symbols SPY,BTC-USD,TLT --regime-method both
"""

from __future__ import annotations

import argparse
import json
import logging
import sys
from pathlib import Path

import numpy as np
import pandas as pd

SCRIPTS_DIR = Path(__file__).resolve().parent
if str(SCRIPTS_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_DIR))

from data_sources import fetch_data, fetch_multi
from features import FeatureEngineer
from regime_detector import detect_regimes, detect_regimes_hmm, HMMRegimeResult

log = logging.getLogger(__name__)

PANIER_SYMBOLS = [
    # Equities (broad indices + sectors)
    "SPY", "RSP", "IWM", "QQQ", "XLF", "XLE", "XLK", "XLY", "XLP", "XLV",
    # Bonds
    "TLT", "IEF", "BND",
    # Commodities
    "GLD", "SLV", "DBC",
    # International
    "EFA", "EEM",
    # Crypto
    "BTC-USD",
]

BOND_PROXY = "TLT"
COMMODITY_PROXY = "DBC"
EQUITY_PROXY = "SPY"


def load_panier_data(
    symbols: list[str] | None = None,
    start: str = "2015-01-01",
    end: str = "2026-05-01",
    data_dir: str | Path | None = None,
) -> dict[str, pd.DataFrame]:
    """Load OHLCV data for panier symbols.

    Tries local CSV first, falls back to yfinance via data_sources.
    """
    symbols = symbols or PANIER_SYMBOLS
    results = {}

    for sym in symbols:
        try:
            if data_dir:
                df = fetch_data(
                    sym, start=start, end=end,
                    data_dir=Path(data_dir), use_cache=True,
                )
            else:
                df = fetch_data(sym, start=start, end=end, use_cache=True)

            if len(df) > 0:
                results[sym] = df
                log.info(f"  {sym}: {len(df)} rows loaded")
            else:
                log.warning(f"  {sym}: empty data, skipping")
        except FileNotFoundError:
            log.warning(f"  {sym}: no data found, skipping")
        except Exception as e:
            log.warning(f"  {sym}: error loading: {e}")

    return results


def load_auxiliary_series(
    panier: dict[str, pd.DataFrame],
) -> dict[str, pd.Series]:
    """Extract auxiliary price series from panier for cross-asset features."""
    aux = {}

    if BOND_PROXY in panier:
        aux["bond"] = panier[BOND_PROXY]["Close"]
    if COMMODITY_PROXY in panier:
        aux["commodity"] = panier[COMMODITY_PROXY]["Close"]
    if EQUITY_PROXY in panier:
        aux["equity_index"] = panier[EQUITY_PROXY]["Close"]

    return aux


def build_features_for_symbol(
    symbol: str,
    df: pd.DataFrame,
    aux: dict[str, pd.Series],
    regime_method: str = "both",
    lookback: int = 20,
    regime_decode: str = "viterbi",
) -> pd.DataFrame | None:
    """Build full feature set for a single symbol.

    Parameters
    ----------
    symbol : str
        Ticker symbol.
    df : pd.DataFrame
        OHLCV data for the symbol.
    aux : dict
        Auxiliary series (bond, commodity, equity_index).
    regime_method : str
        "price", "hmm", or "both".
    lookback : int
        Feature lookback window.
    regime_decode : {"viterbi", "filter"}, default "viterbi"
        Decoding scheme for the ``regime_hmm`` column (#21054).

        ``"viterbi"`` (default, historical behaviour) is **retrospective**:
        the label at ``t`` depends on observations after ``t`` through the
        end-backtracking, so the column must not be consumed as a
        known-at-``t`` signal feature in a walk-forward or live setting.
        ``"filter"`` is forward-only (``alpha[t]`` argmax), i.e. causal.

        The chosen mode is written to the dataset provenance manifest, so a
        reader of the parquet never has to guess which one produced the
        column.

    Returns
    -------
    pd.DataFrame with features + regime columns, or None if insufficient data.
    """
    if len(df) < 200:
        log.warning(f"  {symbol}: only {len(df)} rows, need >= 200, skipping")
        return None

    eng = FeatureEngineer(
        lookback=lookback,
        indicators=[
            "returns", "volatility", "volume_ratio", "ma_ratios",
            "rsi", "macd", "bollinger", "true_range_atr", "obv",
            "regime", "momentum", "statistical", "price_acceleration",
            "cross_asset_ratios",
        ],
        bond=aux.get("bond"),
        commodity=aux.get("commodity"),
        equity_index=aux.get("equity_index"),
    )

    features = eng.transform(df, add_target=True)
    if len(features) == 0:
        log.warning(f"  {symbol}: no valid features after NaN drop, skipping")
        return None

    # Add regime labels
    prices_aligned = df["Close"].reindex(features.index)

    if regime_method in ("price", "both"):
        regimes_price = detect_regimes(prices_aligned, method="price")
        features["regime_price"] = regimes_price.values

    if regime_method in ("hmm", "both"):
        try:
            # #21054: the decode mode is a parameter, not a comment. A
            # retrospective (Viterbi) column looks identical to a causal
            # (filtered) one in the parquet; the mode is recorded in the
            # provenance manifest written by `build_dataset_v2`.
            regimes_hmm = detect_regimes(
                prices_aligned, method="hmm", n_states=3,
                decode_mode=regime_decode,
            )
            features["regime_hmm"] = regimes_hmm.values
            features.attrs["regime_decode"] = regime_decode
        except Exception as e:
            log.warning(f"  {symbol}: HMM failed ({e}), using price-only")

    features.attrs["symbol"] = symbol
    log.info(f"  {symbol}: {len(features)} rows, {len(features.columns)} columns")
    return features


def build_dataset_v2(
    symbols: list[str] | None = None,
    start: str = "2015-01-01",
    end: str = "2026-05-01",
    regime_method: str = "both",
    output_dir: str | Path = "datasets_v2",
    data_dir: str | Path | None = None,
    regime_decode: str = "viterbi",
) -> dict[str, pd.DataFrame]:
    """Build Dataset V2 for all panier symbols.

    Parameters
    ----------
    regime_decode : {"viterbi", "filter"}, default "viterbi"
        Decoding scheme for the ``regime_hmm`` column (#21054). ``"viterbi"``
        (default, historical behaviour) is retrospective; ``"filter"`` is
        forward-only and is the causal choice when the column is consumed as
        a known-at-``t`` signal in a walk-forward evaluation. The mode is
        recorded in ``<output_dir>/_provenance.json``.

    Returns dict of {symbol: features_df}.
    """
    if regime_decode not in ("viterbi", "filter"):
        raise ValueError(
            f"regime_decode must be 'viterbi' or 'filter', got {regime_decode!r}"
        )

    output_dir = Path(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)

    if regime_decode == "viterbi" and regime_method in ("hmm", "both"):
        log.warning(
            "regime_hmm is built from a RETROSPECTIVE (Viterbi) decode: the "
            "label at t depends on observations after t (#21054). Use "
            "--regime-decode filter for a walk-forward or live signal."
        )

    log.info("Loading panier data...")
    panier = load_panier_data(symbols, start=start, end=end, data_dir=data_dir)
    log.info(f"Loaded {len(panier)}/{len(symbols or PANIER_SYMBOLS)} symbols")

    if len(panier) == 0:
        log.error("No data loaded, aborting")
        return {}

    aux = load_auxiliary_series(panier)
    log.info(f"Auxiliary series: {list(aux.keys())}")

    results = {}
    for sym, df in panier.items():
        log.info(f"Building features for {sym}...")
        features = build_features_for_symbol(
            sym, df, aux, regime_method=regime_method, regime_decode=regime_decode
        )
        if features is not None:
            # Save per-symbol Parquet
            out_path = output_dir / f"{sym.replace('-', '_').replace('.', '_')}_v2.parquet"
            try:
                features.to_parquet(out_path)
                log.info(f"  Saved {out_path.name}")
            except ImportError:
                csv_path = out_path.with_suffix(".csv")
                features.to_csv(csv_path)
                log.info(f"  Saved {csv_path.name} (no pyarrow)")

            results[sym] = features

    # Summary
    log.info(f"\n=== Dataset V2 Summary ===")
    log.info(f"Symbols: {len(results)}/{len(panier)}")
    for sym, feat in results.items():
        regime_cols = [c for c in feat.columns if c.startswith("regime_")]
        log.info(f"  {sym}: {len(feat)} rows, {len(feat.columns)} cols, regimes: {regime_cols}")

    manifest = build_provenance_manifest(
        results, regime_method=regime_method, regime_decode=regime_decode,
        start=start, end=end,
    )
    manifest_path = output_dir / "_provenance.json"
    manifest_path.write_text(
        json.dumps(manifest, indent=2, ensure_ascii=True) + "\n", encoding="utf-8"
    )
    log.info(f"Provenance written to {manifest_path.name}")

    return results


def build_provenance_manifest(
    results: dict[str, pd.DataFrame],
    regime_method: str,
    regime_decode: str,
    start: str,
    end: str,
) -> dict:
    """Record how the regime columns of a Dataset V2 were produced (#21054).

    A retrospective (Viterbi) label column is byte-indistinguishable from a
    causal (filtered) one once it lives in the parquet. Without this record,
    the only place the distinction existed was a source comment -- i.e.
    nowhere a consumer of the dataset would look. The manifest travels with
    the data (ObjectStore upload carries the directory), so the warning
    reaches the reader who builds a signal on `regime_hmm`.
    """
    causal = regime_decode == "filter"
    return {
        "schema": 1,
        "generated_by": "build_dataset_v2.py",
        "window": {"start": start, "end": end},
        "regime_method": regime_method,
        "regime_decode": regime_decode,
        "regime_hmm_causal": causal,
        "lookahead_note": (
            "regime_hmm is FORWARD-ONLY (filtered decode): the label at t is a "
            "function of observations up to t only, so it may be used as a "
            "known-at-t feature in a walk-forward evaluation."
            if causal else
            "regime_hmm is RETROSPECTIVE (Viterbi backtracking): the label at t "
            "depends on observations after t. Do NOT use it as a known-at-t "
            "signal feature in a walk-forward or live evaluation; rebuild the "
            "dataset with regime_decode='filter' for that use."
        ),
        "regime_price_causal": True,
        "symbols": {
            sym: {"rows": int(len(feat)), "columns": int(len(feat.columns))}
            for sym, feat in results.items()
        },
    }


def build_arg_parser() -> argparse.ArgumentParser:
    """Command-line parser for the dataset builder.

    Kept separate from :func:`main` so the flags themselves are testable
    without running a build (#21054): a documented flag that no test ever
    parsed is a flag nobody has checked is wired to the parameter.
    """
    parser = argparse.ArgumentParser(description="Build Dataset V2")
    parser.add_argument(
        "--symbols", type=str, default=None,
        help="Comma-separated symbols (default: full panier)",
    )
    parser.add_argument("--start", type=str, default="2015-01-01")
    parser.add_argument("--end", type=str, default="2026-05-01")
    parser.add_argument(
        "--regime-method", type=str, default="both",
        choices=["price", "hmm", "both"],
    )
    parser.add_argument("--output-dir", type=str, default="datasets_v2")
    parser.add_argument("--data-dir", type=str, default=None)
    parser.add_argument(
        "--regime-decode", type=str, default="viterbi",
        choices=["viterbi", "filter"],
        help="Decoding of the regime_hmm column (#21054): 'viterbi' "
             "(default, retrospective -- not usable as a known-at-t "
             "signal) or 'filter' (forward-only, causal). Recorded in "
             "<output-dir>/_provenance.json.",
    )
    parser.add_argument("--verbose", action="store_true")
    return parser


def main():
    args = build_arg_parser().parse_args()

    level = logging.DEBUG if args.verbose else logging.INFO
    logging.basicConfig(level=level, format="%(asctime)s %(levelname)-8s %(message)s")

    symbols = args.symbols.split(",") if args.symbols else None
    build_dataset_v2(
        symbols=symbols,
        start=args.start,
        end=args.end,
        regime_method=args.regime_method,
        output_dir=args.output_dir,
        data_dir=args.data_dir,
        regime_decode=args.regime_decode,
    )


if __name__ == "__main__":
    main()
