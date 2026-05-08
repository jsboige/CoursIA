"""
Stage 1 Feature Engineering: Enhanced indicators + HMM regime features on crypto panier.

Adds HMM regime features (regime labels, transition features, cross-asset regime)
on top of the default feature set (RSI, MACD, BB, etc.) from features.py.

Walk-forward 5-fold x 4 seeds with 10bps transaction costs.
Produces BEATS/NO BEATS/INCONCLUSIVE verdict per coin, compared to Stage 0 RF baseline.

Usage:
    python run_stage1_feature_eng.py
    python run_stage1_feature_eng.py --dry-run
    python run_stage1_feature_eng.py --seeds 0,1,7,42 --n-splits 5
    python run_stage1_feature_eng.py --symbols BTC-USD ETH-USD
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from datetime import datetime
from pathlib import Path

import numpy as np
import pandas as pd
from sklearn.ensemble import RandomForestClassifier
from sklearn.metrics import accuracy_score
from sklearn.preprocessing import StandardScaler

SCRIPT_DIR = Path(__file__).resolve().parent
CHECKPOINTS_DIR = SCRIPT_DIR.parent / "checkpoints"
DATA_DIR = SCRIPT_DIR.parent.parent / "datasets" / "yfinance" / "crypto_panier"

sys.path.insert(0, str(SCRIPT_DIR))
from features import FeatureEngineer
from graph_builder import CRYPTO_PANIER_SYMBOLS, load_crypto_panier
from regime_detector import (
    detect_regimes_hmm,
    detect_regimes_multivariate,
    compute_regime_transition_features,
)
from transaction_costs import TransactionCostModel
from walk_forward import WalkForwardSplitter

BASELINE_SEEDS = [0, 1, 7, 42]
BASELINE_N_SPLITS = 5
BASELINE_GAP = 5
DEFAULT_BASELINE_PATH = (
    CHECKPOINTS_DIR / "crypto_baselines" / "stage0_crypto_panier_results.json"
)


# ---------------------------------------------------------------------------
# Feature augmentation
# ---------------------------------------------------------------------------

BASE_INDICATORS = [
    "returns", "volatility", "volume_ratio", "ma_ratios",
    "rsi", "macd", "bollinger", "true_range_atr", "obv",
]


def compute_hmm_features_single(coin_prices: pd.Series, n_states: int = 3) -> pd.DataFrame:
    """Compute HMM regime features for a single coin.

    Features: regime label (one-hot), regime duration proxy.
    """
    result = detect_regimes_hmm(coin_prices, n_states=n_states)
    features = pd.DataFrame(index=coin_prices.index)

    # One-hot regime labels
    for i, name in enumerate(result.regime_names):
        features[f"hmm_regime_{name}"] = (result.labels == i).astype(float)

    return features


def compute_cross_asset_regime_features(
    closes: pd.DataFrame, n_states: int = 3, lookback: int = 20,
) -> pd.DataFrame:
    """Compute cross-asset regime features using multivariate HMM."""
    prices_dict = {col: closes[col] for col in closes.columns}
    mv_result = detect_regimes_multivariate(
        prices_dict, method="hmm", n_states=n_states,
    )
    return compute_regime_transition_features(mv_result, lookback=lookback)


def build_enhanced_features(
    coin_df: pd.DataFrame,
    coin_prices: pd.Series,
    closes_all: pd.DataFrame,
    lookback: int = 20,
    add_target: bool = True,
) -> pd.DataFrame:
    """Build Stage 1 features = base indicators + HMM regime + cross-asset regime."""
    # Base features from FeatureEngineer
    engineer = FeatureEngineer(lookback=lookback, indicators=BASE_INDICATORS)
    base = engineer.transform(coin_df, add_target=False)

    # Single-coin HMM regime features
    hmm_feat = compute_hmm_features_single(coin_prices)
    hmm_feat = hmm_feat.loc[base.index.intersection(hmm_feat.index)]

    # Cross-asset regime features
    cross_feat = compute_cross_asset_regime_features(closes_all)
    cross_feat = cross_feat.loc[base.index.intersection(cross_feat.index)]

    # Align all to common index
    common_idx = base.index.intersection(hmm_feat.index).intersection(cross_feat.index)
    features = pd.concat([
        base.loc[common_idx],
        hmm_feat.loc[common_idx],
        cross_feat.loc[common_idx],
    ], axis=1)

    if add_target:
        features["target"] = coin_df["Close"].pct_change().shift(-1).loc[common_idx]

    features = features.dropna()
    return features


# ---------------------------------------------------------------------------
# Walk-forward training with transaction costs
# ---------------------------------------------------------------------------

def train_walk_forward_with_costs(
    features: pd.DataFrame,
    seed: int = 0,
    n_splits: int = 5,
    gap: int = 5,
    cost_bps: float = 10.0,
    n_estimators: int = 200,
    max_depth: int = 8,
) -> dict:
    """Walk-forward RF training with transaction costs deducted from Sharpe."""
    np.random.seed(seed)

    X = features.drop(columns=["target"]).values
    y = features["target"].values

    # Binary direction target
    y_binary = (y > 0.001).astype(int)

    splitter = WalkForwardSplitter(n_splits=n_splits, gap=gap)

    fold_results = []
    oos_preds = np.full(len(y_binary), -1, dtype=int)
    oos_returns = np.full(len(y), np.nan, dtype=float)

    for fold_idx, (train_idx, test_idx) in enumerate(splitter.split(X)):
        if len(test_idx) == 0:
            continue

        # Internal train/val split (85/15)
        val_cutoff = int(len(train_idx) * 0.85)
        tr_idx = train_idx[:val_cutoff]
        val_idx = train_idx[val_cutoff:]

        scaler = StandardScaler()
        X_tr = scaler.fit_transform(X[tr_idx])
        X_val = scaler.transform(X[val_idx])
        X_te = scaler.transform(X[test_idx])

        model = RandomForestClassifier(
            n_estimators=n_estimators, max_depth=max_depth,
            random_state=seed, n_jobs=-1,
        )
        model.fit(X_tr, y_binary[tr_idx])

        fold_preds = model.predict(X_te)
        fold_acc = accuracy_score(y_binary[test_idx], fold_preds)
        val_preds = model.predict(X_val)
        val_acc = accuracy_score(y_binary[val_idx], val_preds)

        oos_preds[test_idx] = fold_preds
        # Strategy returns: long if predicted up, short if predicted down
        strategy_returns = np.where(fold_preds == 1, y[test_idx], -y[test_idx])
        oos_returns[test_idx] = strategy_returns

        fold_results.append({
            "fold": fold_idx,
            "val_accuracy": round(val_acc, 4),
            "oos_accuracy": round(fold_acc, 4),
            "train_size": len(tr_idx),
            "test_size": len(test_idx),
        })

    # Aggregate OOS
    valid_mask = oos_preds >= 0
    oos_predictions = oos_preds[valid_mask]
    oos_targets = y_binary[valid_mask]
    oos_rets = oos_returns[valid_mask]

    if len(oos_predictions) == 0:
        return {"seed": seed, "status": "no_oos_data"}

    oos_diracc = float(np.mean(oos_predictions == oos_targets))

    # Majority baseline
    majority_freq = float(np.mean(oos_targets == 1))
    majority_acc = max(majority_freq, 1.0 - majority_freq)

    # Sharpe computation
    gross_sharpe = _sharpe(oos_rets)
    cost_model = TransactionCostModel(commission_bps=cost_bps / 2)
    # Compute trade indicator: position change when prediction flips
    oos_positions = np.where(oos_predictions == 1, 1.0, -1.0)
    trade_indicators = np.abs(np.diff(oos_positions, prepend=oos_positions[0]))
    net_returns = cost_model.apply_to_returns(oos_rets, trades=trade_indicators)
    net_sharpe = _sharpe(net_returns)

    edge = oos_diracc - majority_acc

    return {
        "seed": seed,
        "oos_diracc": round(oos_diracc, 4),
        "majority_acc": round(majority_acc, 4),
        "edge_vs_majority": round(edge, 4),
        "gross_sharpe": round(gross_sharpe, 4),
        "net_sharpe": round(net_sharpe, 4),
        "n_oos": int(valid_mask.sum()),
        "n_folds": len(fold_results),
        "fold_details": fold_results,
    }


def _sharpe(returns: np.ndarray, annualize: bool = True) -> float:
    """Annualized Sharpe ratio from daily returns."""
    if len(returns) < 10:
        return 0.0
    mean_r = np.mean(returns)
    std_r = np.std(returns, ddof=1)
    if std_r < 1e-10:
        return 0.0
    sr = mean_r / std_r
    if annualize:
        sr *= np.sqrt(252)
    return float(sr)


# ---------------------------------------------------------------------------
# Verdict computation
# ---------------------------------------------------------------------------

def compute_verdict(seed_results: list[dict]) -> dict:
    """Compute BEATS/NO BEATS/INCONCLUSIVE verdict from multi-seed results.

    BEATS:      t_stat > 2.0 AND mean_edge > 0
    NO BEATS:   mean_edge < 0
    INCONCLUSIVE: otherwise
    """
    edges = [r["edge_vs_majority"] for r in seed_results]
    mean_edge = float(np.mean(edges))
    std_edge = float(np.std(edges, ddof=1)) if len(edges) > 1 else 0.0
    t_stat = mean_edge / std_edge if std_edge > 1e-10 else 0.0

    net_sharpes = [r["net_sharpe"] for r in seed_results]
    gross_sharpes = [r["gross_sharpe"] for r in seed_results]
    diraccs = [r["oos_diracc"] for r in seed_results]

    if mean_edge > 0 and t_stat > 2.0:
        verdict = "BEATS"
    elif mean_edge < 0:
        verdict = "NO BEATS"
    else:
        verdict = "INCONCLUSIVE"

    return {
        "verdict": verdict,
        "mean_edge_vs_majority": round(mean_edge, 4),
        "std_edge": round(std_edge, 4),
        "t_stat": round(t_stat, 4),
        "mean_net_sharpe": round(float(np.mean(net_sharpes)), 4),
        "mean_gross_sharpe": round(float(np.mean(gross_sharpes)), 4),
        "mean_diracc": round(float(np.mean(diraccs)), 4),
        "seeds": seed_results,
    }


# ---------------------------------------------------------------------------
# Baseline comparison
# ---------------------------------------------------------------------------

def load_baseline_results(path: Path | None = None) -> dict:
    """Load Stage 0 baseline results for comparison."""
    path = path or DEFAULT_BASELINE_PATH
    if not path.exists():
        return {}
    data = json.loads(path.read_text(encoding="utf-8"))
    baseline = {}
    for item in data:
        coin = item["coin"]
        rf = item.get("rf_walk_forward", {})
        baseline[coin] = {
            "verdict": rf.get("verdict", "UNKNOWN"),
            "mean_edge": rf.get("mean_edge_vs_majority", 0),
            "t_stat": rf.get("t_stat", 0),
            "mean_net_sharpe": rf.get("mean_net_sharpe", 0),
            "n_features": rf.get("n_features", 19),
            "n_folds": rf.get("seeds", [{}])[0].get("n_folds", 4) if rf.get("seeds") else 4,
        }
    return baseline


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def load_coin_data(symbol: str) -> pd.DataFrame:
    """Load OHLCV data for a single crypto coin."""
    matches = list(DATA_DIR.glob(f"{symbol}_*.csv"))
    if not matches:
        raise FileNotFoundError(f"No data file found for {symbol} in {DATA_DIR}")
    df = pd.read_csv(matches[0], index_col=0, parse_dates=True)
    # Ensure standard column names
    df.columns = [c.strip().capitalize() for c in df.columns]
    return df


def run_single_coin(
    symbol: str,
    closes_all: pd.DataFrame,
    seeds: list[int],
    n_splits: int,
    gap: int,
    cost_bps: float,
    lookback: int,
    dry_run: bool = False,
) -> dict:
    """Run Stage 1 experiment for a single coin."""
    print(f"\n{'='*60}")
    print(f"  {symbol}")
    print(f"{'='*60}")

    coin_df = load_coin_data(symbol)
    coin_prices = coin_df["Close"]

    if dry_run:
        coin_df = coin_df.iloc[-500:]
        coin_prices = coin_prices.iloc[-500:]

    print(f"  Data: {len(coin_df)} rows ({coin_df.index.min().date()} -> {coin_df.index.max().date()})")

    # Build features
    t0 = time.time()
    features = build_enhanced_features(coin_df, coin_prices, closes_all, lookback=lookback)
    n_features = len(features.columns) - 1  # minus target
    print(f"  Features: {n_features} columns, {len(features)} rows ({time.time()-t0:.1f}s)")

    # Multi-seed walk-forward
    seed_results = []
    for seed in seeds:
        t0 = time.time()
        result = train_walk_forward_with_costs(
            features, seed=seed, n_splits=n_splits, gap=gap,
            cost_bps=cost_bps,
        )
        elapsed = time.time() - t0
        if result.get("status") == "no_oos_data":
            print(f"    seed={seed}: NO OOS DATA")
            continue
        seed_results.append(result)
        print(
            f"    seed={seed}: DirAcc={result['oos_diracc']:.4f}  "
            f"edge={result['edge_vs_majority']:+.4f}  "
            f"net_sharpe={result['net_sharpe']:.4f}  "
            f"({elapsed:.1f}s)"
        )

    if not seed_results:
        return {"coin": symbol, "verdict": "ERROR", "error": "no valid seeds"}

    verdict_data = compute_verdict(seed_results)
    verdict_data["coin"] = symbol
    verdict_data["n_features"] = n_features
    verdict_data["n_seeds"] = len(seed_results)
    verdict_data["cost_bps"] = cost_bps
    verdict_data["n_splits"] = n_splits

    print(f"  VERDICT: {verdict_data['verdict']}")
    print(f"    mean_edge={verdict_data['mean_edge_vs_majority']:+.4f}  "
          f"t={verdict_data['t_stat']:.4f}  "
          f"net_sharpe={verdict_data['mean_net_sharpe']:.4f}")

    return verdict_data


def main():
    parser = argparse.ArgumentParser(description="Stage 1: Enhanced features + HMM regime")
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--symbols", nargs="+", default=None)
    parser.add_argument("--seeds", type=str, default=None, help="Comma-separated seeds")
    parser.add_argument("--n-splits", type=int, default=BASELINE_N_SPLITS)
    parser.add_argument("--gap", type=int, default=BASELINE_GAP)
    parser.add_argument("--cost-bps", type=float, default=10.0)
    parser.add_argument("--lookback", type=int, default=20)
    parser.add_argument("--output-dir", default=None)
    parser.add_argument("--baseline-path", default=None)
    args = parser.parse_args()

    symbols = args.symbols or CRYPTO_PANIER_SYMBOLS
    seeds = [int(s) for s in args.seeds.split(",")] if args.seeds else BASELINE_SEEDS

    print("Stage 1: Enhanced Features + HMM Regime")
    print(f"  Coins: {len(symbols)}, Seeds: {seeds}")
    print(f"  Walk-forward: {args.n_splits} folds, gap={args.gap}")
    print(f"  Costs: {args.cost_bps} bps")

    # Load all closes for cross-asset features
    if args.dry_run:
        closes_all = load_crypto_panier()
        closes_all = closes_all.iloc[-500:]
    else:
        closes_all = load_crypto_panier()

    print(f"  Cross-asset data: {len(closes_all)} days, {len(closes_all.columns)} coins")

    # Load baseline for comparison
    baseline_path = Path(args.baseline_path) if args.baseline_path else DEFAULT_BASELINE_PATH
    baseline = load_baseline_results(baseline_path)

    # Run experiments
    all_results = []
    for symbol in symbols:
        result = run_single_coin(
            symbol, closes_all, seeds,
            n_splits=args.n_splits, gap=args.gap,
            cost_bps=args.cost_bps, lookback=args.lookback,
            dry_run=args.dry_run,
        )
        all_results.append(result)

    # Print comparison table
    print(f"\n{'='*80}")
    print("STAGE 1 vs STAGE 0 COMPARISON")
    print(f"{'='*80}")
    print(f"{'Coin':10s} {'S1 Verdict':12s} {'S1 Edge':>8s} {'S1 t':>6s} {'S1 NetSR':>8s} "
          f"{'S0 Verdict':12s} {'S0 Edge':>8s} {'Delta':>7s}")
    print("-" * 80)

    for r in all_results:
        coin = r["coin"]
        s0 = baseline.get(coin, {})
        s1_edge = r.get("mean_edge_vs_majority", 0)
        s0_edge = s0.get("mean_edge", 0)
        delta = s1_edge - s0_edge
        print(
            f"{coin:10s} {r.get('verdict','?'):12s} {s1_edge:+8.4f} "
            f"{r.get('t_stat',0):6.3f} {r.get('mean_net_sharpe',0):8.4f} "
            f"{s0.get('verdict','N/A'):12s} {s0_edge:+8.4f} {delta:+7.4f}"
        )

    # Save results
    output_dir = Path(args.output_dir) if args.output_dir else CHECKPOINTS_DIR / "stage1_feature_eng"
    output_dir.mkdir(parents=True, exist_ok=True)
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    out_file = output_dir / f"stage1_results_{ts}.json"
    out_file.write_text(json.dumps(all_results, indent=2, default=str), encoding="utf-8")
    print(f"\nResults saved: {out_file}")

    # Also save latest as stable name
    latest = output_dir / "stage1_latest.json"
    latest.write_text(json.dumps(all_results, indent=2, default=str), encoding="utf-8")

    # Summary verdicts
    verdicts = [r.get("verdict", "ERROR") for r in all_results]
    print(f"\nSummary: BEATS={verdicts.count('BEATS')}  "
          f"NO BEATS={verdicts.count('NO BEATS')}  "
          f"INCONCLUSIVE={verdicts.count('INCONCLUSIVE')}  "
          f"ERROR={verdicts.count('ERROR')}")


if __name__ == "__main__":
    main()
