"""
End-to-end MoE training pipeline for financial direction prediction.

Combines:
    1. data_sources.py — fetch price data (local CSV / yfinance / FRED)
    2. panier_loader.py — load anti-bias panier data
    3. regime_detector.py — label each timestep with market regime
    4. features.py — compute OHLCV features
    5. moe_experts.py — train per-regime expert models
    6. baselines.py — majority-class baseline comparison
    7. transaction_costs.py — apply costs to simulated trades

Output:
    - Per-regime and overall accuracy vs majority baseline
    - Walk-forward fold results
    - Trained MoERouter saved as pickle

Usage:
    python train_moe.py --symbol SPY --regime-method price --n-folds 5
    python train_moe.py --panier --regime-method hmm --n-folds 3

Issue #754 Phase B: MoE+régimes approach to beat majority baseline.
"""

from __future__ import annotations

import argparse
import json
import logging
import sys
import time
from pathlib import Path

import numpy as np
import pandas as pd

# Add scripts dir to path for imports
SCRIPTS_DIR = Path(__file__).resolve().parent
if str(SCRIPTS_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_DIR))

from baselines import majority_class_baseline
from moe_experts import MoEConfig, MoERouter, train_moe_walk_forward

log = logging.getLogger(__name__)


def _setup_logging(verbose: bool = False) -> None:
    level = logging.DEBUG if verbose else logging.INFO
    logging.basicConfig(
        level=level,
        format="%(asctime)s %(levelname)-8s %(message)s",
        datefmt="%H:%M:%S",
    )


def _compute_direction_target(
    df: pd.DataFrame, horizon: int = 1, threshold: float = 0.0
) -> pd.Series:
    """Compute binary direction target: 1 if forward return > threshold."""
    fwd = df["Close"].pct_change(horizon).shift(-horizon)
    return (fwd > threshold).astype(int)


def _prepare_features(
    df: pd.DataFrame,
    lookback: int = 20,
) -> pd.DataFrame:
    """Prepare feature matrix from OHLCV data.

    Features: returns (1/5/10/20d), volatility, volume ratio, MA ratios.
    """
    feat = pd.DataFrame(index=df.index)

    close = df["Close"]
    for w in [1, 5, 10, 20]:
        feat[f"ret_{w}d"] = close.pct_change(w)

    feat["vol_5d"] = close.pct_change().rolling(5).std()
    feat["vol_20d"] = close.pct_change().rolling(20).std()

    if "Volume" in df.columns:
        feat["vol_ratio"] = df["Volume"] / df["Volume"].rolling(20).mean()

    for w in [5, 10, 20, 60]:
        feat[f"ma_ratio_{w}"] = close / close.rolling(w).mean()

    return feat.dropna()


def _load_symbol_data(
    symbol: str,
    data_dir: str | None = None,
    start: str = "2015-01-01",
    end: str = "2025-01-01",
) -> pd.DataFrame:
    """Load data for a single symbol using data_sources or panier_loader."""
    # Try panier first (for anti-bias data)
    try:
        from panier_loader import load_panier
        panier = load_panier(start=start, end=end)
        if symbol in panier:
            return panier[symbol]
    except Exception:
        pass

    # Fall back to data_sources
    try:
        from data_sources import fetch_data
        df = fetch_data(
            symbol=symbol,
            start=start,
            end=end,
            source="auto",
            data_dir=data_dir,
        )
        if df is not None and len(df) > 0:
            return df
    except Exception as e:
        import logging
        logging.getLogger(__name__).warning("fetch_data failed for %s: %s", symbol, e)

    raise FileNotFoundError(
        f"No data found for {symbol}. "
        "Ensure panier data or local CSVs are available."
    )


def train_moe_pipeline(
    symbol: str = "SPY",
    panier_mode: bool = False,
    regime_method: str = "price",
    n_folds: int = 5,
    lookback: int = 20,
    horizon: int = 1,
    hidden_sizes: tuple[int, ...] = (64, 32),
    min_samples_per_expert: int = 50,
    max_iter: int = 200,
    seed: int = 42,
    start: str = "2015-01-01",
    end: str = "2025-01-01",
    data_dir: str | None = None,
    output_dir: str | None = None,
) -> dict:
    """Run full MoE training pipeline.

    Returns dict with results: walk-forward folds, overall stats, baseline comparison.
    """
    np.random.seed(seed)
    t0 = time.time()

    # --- Load data ---
    log.info(f"Loading data for {symbol}...")
    df = _load_symbol_data(symbol, data_dir=data_dir, start=start, end=end)
    log.info(f"Loaded {len(df)} rows for {symbol}")

    if len(df) < 500:
        raise ValueError(f"Insufficient data: {len(df)} rows (need >= 500)")

    # --- Features ---
    features = _prepare_features(df, lookback=lookback)
    target = _compute_direction_target(df, horizon=horizon)

    # Align features and target
    common_idx = features.index.intersection(target.dropna().index)
    features = features.loc[common_idx]
    target = target.loc[common_idx]

    X = features.values.astype(np.float32)
    y = target.values.astype(int)

    log.info(f"Features: {X.shape[1]} cols, {X.shape[0]} samples")
    log.info(f"Target balance: {y.mean():.3f} positive")

    # --- Regime detection ---
    log.info(f"Detecting regimes (method={regime_method})...")
    from regime_detector import detect_regimes

    prices = df["Close"].loc[common_idx]
    regime_series = detect_regimes(prices, method=regime_method)
    regime_labels = regime_series.values

    regime_counts = pd.Series(regime_labels).value_counts()
    log.info(f"Regime distribution:\n{regime_counts.to_string()}")

    # --- Walk-forward MoE training ---
    log.info(f"Starting walk-forward MoE training ({n_folds} folds)...")
    config = MoEConfig(
        expert_type="mlp",
        hidden_sizes=hidden_sizes,
        max_iter=max_iter,
        min_samples_per_expert=min_samples_per_expert,
        random_state=seed,
        regime_method=regime_method,
    )

    wf_results = train_moe_walk_forward(
        features=X,
        targets=y,
        regime_labels=regime_labels,
        n_folds=n_folds,
        config=config,
    )

    # --- Baseline comparison ---
    log.info("Computing majority baseline...")
    majority_train = int(np.mean(y[: len(y) // 2]) > 0.5)
    majority_preds = np.full(len(y), majority_train)
    majority_acc = float(np.mean(majority_preds == y))

    # --- Aggregate results ---
    fold_accuracies = [r["overall_accuracy"] for r in wf_results]
    mean_acc = np.mean(fold_accuracies) if fold_accuracies else 0.0

    beats_majority = mean_acc > majority_acc
    elapsed = time.time() - t0

    result = {
        "symbol": symbol,
        "regime_method": regime_method,
        "n_folds": len(wf_results),
        "n_features": X.shape[1],
        "n_samples": X.shape[0],
        "target_balance": float(y.mean()),
        "majority_baseline": majority_acc,
        "moe_mean_accuracy": float(mean_acc),
        "moe_fold_accuracies": [float(a) for a in fold_accuracies],
        "beats_majority": bool(beats_majority),
        "regime_counts": {str(k): int(v) for k, v in regime_counts.items()},
        "config": {
            "hidden_sizes": list(hidden_sizes),
            "max_iter": max_iter,
            "min_samples_per_expert": min_samples_per_expert,
            "seed": seed,
            "lookback": lookback,
            "horizon": horizon,
        },
        "elapsed_seconds": round(elapsed, 1),
    }

    # --- Save results ---
    if output_dir:
        out_path = Path(output_dir)
        out_path.mkdir(parents=True, exist_ok=True)
        result_file = out_path / f"moe_{symbol}_{regime_method}_results.json"
        with open(result_file, "w") as f:
            json.dump(result, f, indent=2, default=str)
        log.info(f"Results saved to {result_file}")

    log.info(
        f"\n{'='*60}\n"
        f"MoE Results for {symbol} ({regime_method} regimes)\n"
        f"{'='*60}\n"
        f"Folds: {len(wf_results)} | Samples: {X.shape[0]}\n"
        f"Majority baseline: {majority_acc:.3f}\n"
        f"MoE mean accuracy: {mean_acc:.3f}\n"
        f"BEATS MAJORITY: {'YES' if beats_majority else 'NO'}\n"
        f"Per fold: {[f'{a:.3f}' for a in fold_accuracies]}\n"
        f"Elapsed: {elapsed:.1f}s\n"
        f"{'='*60}"
    )

    return result


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description="MoE training pipeline for financial direction prediction"
    )
    parser.add_argument(
        "--symbol", default="SPY",
        help="Ticker symbol (default: SPY)",
    )
    parser.add_argument(
        "--panier", action="store_true",
        help="Use panier anti-bias data",
    )
    parser.add_argument(
        "--regime-method", default="price",
        choices=["price", "hmm"],
        help="Regime detection method (default: price)",
    )
    parser.add_argument("--n-folds", type=int, default=5)
    parser.add_argument("--lookback", type=int, default=20)
    parser.add_argument("--horizon", type=int, default=1)
    parser.add_argument("--max-iter", type=int, default=200)
    parser.add_argument("--min-samples", type=int, default=50)
    parser.add_argument("--seed", type=int, default=42)
    parser.add_argument("--start", default="2015-01-01")
    parser.add_argument("--end", default="2025-01-01")
    parser.add_argument("--data-dir", default=None)
    parser.add_argument("--output-dir", default=None)
    parser.add_argument("-v", "--verbose", action="store_true")

    args = parser.parse_args()
    _setup_logging(args.verbose)

    train_moe_pipeline(
        symbol=args.symbol,
        panier_mode=args.panier,
        regime_method=args.regime_method,
        n_folds=args.n_folds,
        lookback=args.lookback,
        horizon=args.horizon,
        max_iter=args.max_iter,
        min_samples_per_expert=args.min_samples,
        seed=args.seed,
        start=args.start,
        end=args.end,
        data_dir=args.data_dir,
        output_dir=args.output_dir,
    )


if __name__ == "__main__":
    main()
