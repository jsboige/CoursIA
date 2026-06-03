"""
Stage 0 baselines for crypto panier anti-bias dataset (10 coins).

Computes majority class, buy-and-hold, naive momentum, random walk, and
Random Forest baselines with walk-forward 5-fold x 4 seeds validation.
Applies 10bps transaction costs for realistic evaluation.

Outputs per-coin and aggregate verdict: BEATS / NO BEATS / INCONCLUSIVE.

Usage:
    python train_baselines_crypto_panier.py
    python train_baselines_crypto_panier.py --dry-run
    python train_baselines_crypto_panier.py --coins BTC-USD ETH-USD
    python train_baselines_crypto_panier.py --seeds 0 1 7 42
"""

import argparse
import json
import sys
from pathlib import Path

import numpy as np
import pandas as pd

SCRIPTS_DIR = Path(__file__).resolve().parent
CRYPTO_DIR = SCRIPTS_DIR.parent.parent / "datasets" / "yfinance" / "crypto_panier"
CHECKPOINTS_DIR = SCRIPTS_DIR.parent / "checkpoints" / "crypto_baselines"

sys.path.insert(0, str(SCRIPTS_DIR))

from baselines import (
    buy_and_hold_baseline,
    majority_class_baseline,
    naive_momentum_baseline,
    random_walk_baseline,
    sharpe_from_returns,
)
from data_utils import compute_data_hash, load_data
from features import FeatureEngineer
from transaction_costs import TransactionCostModel, compare_gross_vs_net
from walk_forward import WalkForwardSplitter

CRYPTO_COINS = [
    "BTC-USD", "ETH-USD", "LTC-USD", "XRP-USD", "ADA-USD",
    "LINK-USD", "SOL-USD", "DOT-USD", "AVAX-USD", "MATIC-USD",
]

CRYPTO_COST_MODEL = TransactionCostModel(
    commission_bps=2.0,
    bid_ask_spread_bps=3.0,
    market_impact_coeff=0.05,
    daily_volume=1_000_000,
    slippage_bps=5.0,
)

INDICATORS = [
    "returns", "volatility", "volume_ratio", "ma_ratios",
    "rsi", "macd", "bollinger", "true_range_atr", "obv",
]


def run_classical_baselines(prices: pd.Series, coin: str) -> dict:
    """Run majority class, buy-and-hold, momentum, and random walk baselines."""
    returns = prices.pct_change().dropna()
    n = len(returns)
    split_idx = int(n * 0.8)

    y = (returns > 0).astype(int).values
    y_train, y_test = y[:split_idx], y[split_idx:]

    maj = majority_class_baseline(y_train, y_test)
    bh = buy_and_hold_baseline(prices, test_start=split_idx)
    mom = naive_momentum_baseline(prices, lookback=20, test_start=split_idx)
    rw = random_walk_baseline(prices, n_simulations=500, seed=42, test_start=split_idx)

    return {
        "coin": coin,
        "majority_class": maj,
        "buy_and_hold": bh,
        "momentum_20d": mom,
        "random_walk": rw,
        "n_train": split_idx,
        "n_test": n - split_idx,
    }


def run_rf_walk_forward(
    df: pd.DataFrame,
    coin: str,
    n_splits: int = 5,
    seeds: list[int] | None = None,
    cost_model: TransactionCostModel | None = None,
) -> dict:
    """Random Forest with walk-forward 5-fold x N seeds, transaction costs."""
    from sklearn.ensemble import RandomForestClassifier
    from sklearn.preprocessing import StandardScaler

    if seeds is None:
        seeds = [0, 1, 7, 42]
    if cost_model is None:
        cost_model = CRYPTO_COST_MODEL

    engineer = FeatureEngineer(lookback=20, indicators=INDICATORS)
    features = engineer.transform(df, add_target=False)

    # Binary target: next-day return > 0.1%
    features["target"] = (df["Close"].pct_change().shift(-1) > 0.001).astype(int)
    features = features.dropna()

    X = features.drop(columns=["target"]).values
    y = features["target"].values
    prices_test = df["Close"].reindex(features.index)

    all_seed_results = []

    for seed in seeds:
        rng = np.random.default_rng(seed)
        splitter = WalkForwardSplitter(n_splits=n_splits, gap=5)

        fold_oos_accs = []
        fold_oos_preds = np.full(len(y), np.nan)
        fold_positions = np.zeros(len(y))

        for fold_idx, (train_idx, test_idx) in enumerate(splitter.split(X)):
            if len(test_idx) == 0:
                continue

            X_train, X_test = X[train_idx], X[test_idx]
            y_train, y_test = y[train_idx], y[test_idx]

            scaler = StandardScaler()
            X_train_sc = scaler.fit_transform(X_train)
            X_test_sc = scaler.transform(X_test)

            model = RandomForestClassifier(
                n_estimators=200, max_depth=8,
                random_state=int(seed), n_jobs=-1,
            )
            model.fit(X_train_sc, y_train)
            preds = model.predict(X_test_sc)

            acc = float(np.mean(preds == y_test))
            fold_oos_accs.append(acc)
            fold_oos_preds[test_idx] = preds

            # Position tracking for transaction costs
            pos = np.zeros(len(test_idx))
            pos[preds == 1] = 1.0
            pos[preds == 0] = -1.0
            fold_positions[test_idx] = pos

        # Aggregate OOS
        valid = ~np.isnan(fold_oos_preds)
        oos_preds = fold_oos_preds[valid].astype(int)
        oos_y = y[valid]
        oos_positions = fold_positions[valid]

        oos_diracc = float(np.mean(oos_preds == oos_y))

        # Majority baseline on OOS
        majority_freq = float(np.mean(oos_y == 1))
        majority_acc = max(majority_freq, 1.0 - majority_freq)
        edge = oos_diracc - majority_acc

        # Strategy returns with transaction costs
        gross_returns = prices_test.pct_change().shift(-1).values
        gross_returns = gross_returns[:len(fold_positions)]

        min_len = min(len(oos_positions), len(gross_returns))
        pos_valid = oos_positions[:min_len]
        ret_valid = gross_returns[:min_len]

        strategy_returns = ret_valid * pos_valid
        valid_ret = ~np.isnan(strategy_returns) & ~np.isinf(strategy_returns)
        strategy_returns = strategy_returns[valid_ret]
        pos_for_cost = pos_valid[valid_ret]

        if len(strategy_returns) > 0:
            # Detect trades (position changes)
            pos_changes = np.diff(pos_for_cost, prepend=pos_for_cost[0])
            trades = (pos_changes != 0).astype(float)

            net_returns = cost_model.apply_to_returns(strategy_returns, trades)
            gross_sharpe = sharpe_from_returns(pd.Series(strategy_returns))
            net_sharpe = sharpe_from_returns(pd.Series(net_returns))
        else:
            gross_sharpe = 0.0
            net_sharpe = 0.0

        all_seed_results.append({
            "seed": seed,
            "oos_diracc": round(oos_diracc, 4),
            "majority_acc": round(majority_acc, 4),
            "edge_vs_majority": round(edge, 4),
            "gross_sharpe": round(gross_sharpe, 4),
            "net_sharpe": round(net_sharpe, 4),
            "n_oos": int(np.sum(valid)),
            "n_folds": len(fold_oos_accs),
            "fold_accs": [round(a, 4) for a in fold_oos_accs],
        })

    # Aggregate across seeds
    edges = [r["edge_vs_majority"] for r in all_seed_results]
    mean_edge = float(np.mean(edges))
    std_edge = float(np.std(edges)) if len(edges) > 1 else 0.0
    t_stat = mean_edge / std_edge if std_edge > 1e-10 else 0.0

    # Verdict: BEATS if edge > 0 AND t_stat > 2 (significant at 5%)
    # NO BEATS if edge < 0
    # INCONCLUSIVE if edge > 0 but not significant
    if mean_edge > 0 and t_stat > 2.0:
        verdict = "BEATS"
    elif mean_edge <= 0:
        verdict = "NO BEATS"
    else:
        verdict = "INCONCLUSIVE"

    net_sharpes = [r["net_sharpe"] for r in all_seed_results]
    gross_sharpes = [r["gross_sharpe"] for r in all_seed_results]

    return {
        "coin": coin,
        "model": "RF",
        "verdict": verdict,
        "mean_edge_vs_majority": round(mean_edge, 4),
        "std_edge": round(std_edge, 4),
        "t_stat": round(t_stat, 4),
        "mean_net_sharpe": round(float(np.mean(net_sharpes)), 4),
        "mean_gross_sharpe": round(float(np.mean(gross_sharpes)), 4),
        "seeds": all_seed_results,
        "n_features": X.shape[1],
        "total_samples": len(X),
    }


def run_single_coin(
    coin: str,
    seeds: list[int],
    dry_run: bool = False,
) -> dict:
    """Run all baselines for a single coin."""
    if dry_run:
        from data_utils import generate_synthetic_data
        df = generate_synthetic_data(1000)
        coin_label = f"{coin} (synthetic)"
    else:
        df = load_data(CRYPTO_DIR, coin)
        coin_label = coin

    prices = df["Close"]
    print(f"\n  {coin_label}: {len(df)} rows ({df.index.min().date()} -> {df.index.max().date()})")

    classical = run_classical_baselines(prices, coin)
    rf = run_rf_walk_forward(df, coin, n_splits=5, seeds=seeds)

    return {
        "coin": coin,
        "n_rows": len(df),
        "date_range": f"{df.index.min().date()} -> {df.index.max().date()}",
        "classical_baselines": classical,
        "rf_walk_forward": rf,
    }


def print_verdict_table(results: list[dict]):
    """Print the Stage 0 verdict table."""
    print("\n" + "=" * 90)
    print("STAGE 0 CRYPTO PANIER BASELINES — VERDICT TABLE")
    print("=" * 90)
    print(f"{'Coin':10s} {'DirAcc':>7s} {'MajAcc':>7s} {'Edge':>7s} {'t-stat':>7s} "
          f"{'GrossSR':>8s} {'NetSR':>7s} {'Verdict':14s}")
    print("-" * 90)

    for r in results:
        rf = r["rf_walk_forward"]
        classical = r["classical_baselines"]
        maj = classical["majority_class"]["accuracy"]

        verdict_str = rf["verdict"]
        print(f"{r['coin']:10s} {rf['mean_edge_vs_majority'] + maj:>7.4f} {maj:>7.4f} "
              f"{rf['mean_edge_vs_majority']:>+7.4f} {rf['t_stat']:>7.3f} "
              f"{rf['mean_gross_sharpe']:>8.4f} {rf['mean_net_sharpe']:>7.4f} {verdict_str:14s}")

    n_beats = sum(1 for r in results if r["rf_walk_forward"]["verdict"] == "BEATS")
    n_no = sum(1 for r in results if r["rf_walk_forward"]["verdict"] == "NO BEATS")
    n_inc = sum(1 for r in results if r["rf_walk_forward"]["verdict"] == "INCONCLUSIVE")

    print(f"\n{'='*90}")
    print(f"AGGREGATE: {len(results)} coins | BEATS: {n_beats} | NO BEATS: {n_no} | INCONCLUSIVE: {n_inc}")

    mean_edge = np.mean([r["rf_walk_forward"]["mean_edge_vs_majority"] for r in results])
    mean_net_sr = np.mean([r["rf_walk_forward"]["mean_net_sharpe"] for r in results])
    print(f"MEAN edge vs majority: {mean_edge:+.4f} | MEAN net Sharpe: {mean_net_sr:.4f}")
    print(f"{'='*90}")


def print_classical_table(results: list[dict]):
    """Print classical baselines comparison."""
    print("\n" + "=" * 80)
    print("CLASSICAL BASELINES (80/20 time-series split)")
    print("=" * 80)

    for r in results:
        c = r["classical_baselines"]
        bh = c["buy_and_hold"]
        mom = c["momentum_20d"]
        rw = c["random_walk"]
        print(f"\n  {r['coin']} (train={c['n_train']}, test={c['n_test']})")
        print(f"    Majority class:   acc={c['majority_class']['accuracy']:.4f} "
              f"(class={c['majority_class']['majority_class']}, freq={c['majority_class']['majority_freq']:.4f})")
        print(f"    Buy-and-hold:     sharpe={bh['sharpe']:.4f}  CAGR={bh['cagr']:.4f}  "
              f"MaxDD={bh['max_drawdown']:.4f}  vol={bh['volatility']:.4f}")
        print(f"    Momentum MA20:    acc={mom['accuracy']:.4f}  sharpe={mom['sharpe']:.4f}")
        print(f"    Random walk:      sharpe_mean={rw['sharpe_mean']:.4f}  "
              f"sharpe_std={rw['sharpe_std']:.4f}  p95={rw['sharpe_p95']:.4f}")


def main():
    parser = argparse.ArgumentParser(description="Stage 0 crypto panier baselines")
    parser.add_argument("--dry-run", action="store_true", help="Use synthetic data")
    parser.add_argument("--coins", nargs="+", default=None, help="Specific coins")
    parser.add_argument("--seeds", nargs="+", type=int, default=[0, 1, 7, 42],
                        help="Random seeds for walk-forward")
    parser.add_argument("--n-splits", type=int, default=5, help="Walk-forward folds")
    args = parser.parse_args()

    coins = args.coins or CRYPTO_COINS
    print(f"Stage 0 Crypto Panier Baselines")
    print(f"Coins: {len(coins)} | Seeds: {args.seeds} | WF folds: {args.n_splits}")
    print(f"Transaction costs: ~10bps (2bp commission + 3bp spread + 5bp slippage)")

    results = []
    for i, coin in enumerate(coins):
        print(f"\n[{i+1}/{len(coins)}] {coin}...", end="", flush=True)
        try:
            result = run_single_coin(coin, args.seeds, dry_run=args.dry_run)
            results.append(result)
            rf = result["rf_walk_forward"]
            print(f" verdict={rf['verdict']} edge={rf['mean_edge_vs_majority']:+.4f}")
        except Exception as e:
            print(f" ERROR: {e}")

    if not results:
        print("No results. Check data availability.")
        sys.exit(1)

    print_classical_table(results)
    print_verdict_table(results)

    # Save results
    CHECKPOINTS_DIR.mkdir(parents=True, exist_ok=True)
    out_path = CHECKPOINTS_DIR / "stage0_crypto_panier_results.json"
    out_path.write_text(json.dumps(results, indent=2, default=str), encoding="utf-8")
    print(f"\nResults saved: {out_path}")


if __name__ == "__main__":
    main()
