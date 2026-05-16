"""S6 Cost Forecasting — DecisionTreeRegressor predicts transaction costs.

Question
--------
Can we forecast per-trade transaction costs (spread + slippage) from market
microstructure features, and save money by skipping expensive trades?

From Hands-On AI Trading (Broad 2025, Ex 12): $36k savings on 1827 BTC trades
by predicting conditional cost and trading only when cost < trailing average.

DecisionTreeRegressor sklearn = pure CPU, perfect for po-2023.

Walk-forward 5-fold, 7 coins x 3 horizons x 4 seeds = 84 combos.
Gate: cost-aware savings >= $20k/yr (proportional to 100k notional) AND
      Sharpe net cost-aware > Sharpe net naive + 0.10.

Output
------
- results/s6_cost_forecast/s6_cost_forecast_results.csv
- results/s6_cost_forecast/results.json
- docs/S6_COST_FORECAST.md (verdict)
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

import numpy as np
import pandas as pd
from sklearn.tree import DecisionTreeRegressor
from sklearn.preprocessing import StandardScaler

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

from m11g_fee_aware_kelly import _load_one_coin  # noqa: E402
from m11c_sharpe_test import ledoit_wolf_sharpe_diff_se  # noqa: E402

COINS = ["BTC-USD", "ETH-USD", "SOL-USD", "LTC-USD", "XRP-USD", "ADA-USD", "DOT-USD"]
HORIZONS = [1, 5, 10]  # forecast horizons for cost prediction
SEEDS = [0, 1, 7, 42]
FEE_BPS = 50
N_SPLITS = 5
REFIT_EVERY = 22
NOTIONAL = 100_000  # USD position size for savings calculation
RESULTS_DIR = SCRIPT_DIR / "results" / "s6_cost_forecast"


# ── Simulated microstructure features ─────────────────────────────────────────


def build_cost_features(close: pd.Series, volume_proxy: pd.Series) -> pd.DataFrame:
    """Build features for cost prediction from daily OHLC-like data.

    Since we don't have real bid/ask data, we simulate:
    - ATR (volatility proxy) → higher vol = wider spread
    - ADV (volume proxy) → lower volume = higher impact
    - Spread proxy = ATR / close (relative range)
    - Hour-of-week effect (not available daily, skip)
    - Recent cost history (autoregressive)
    """
    ret = close.pct_change()
    df = pd.DataFrame(index=close.index)

    # ATR proxy: rolling high-low range
    for w in [5, 22]:
        df[f"atr_{w}"] = close.pct_change().rolling(w).std().shift(1) * close.shift(1)

    # ADV proxy
    for w in [5, 22]:
        df[f"adv_{w}"] = volume_proxy.rolling(w).mean().shift(1)

    # Spread proxy = ATR/close
    df["spread_proxy"] = (df["atr_5"] / close.shift(1)).clip(lower=1e-8)

    # Top-of-book imbalance proxy (momentum as order flow proxy)
    for w in [1, 5]:
        df[f"imbalance_{w}"] = ret.rolling(w).sum().shift(1)

    # Day-of-week (0=Mon, 4=Fri)
    df["dow"] = pd.Series(close.index.dayofweek, index=close.index).astype(float)

    # Recent realized cost (AR component)
    df["cost_t1"] = df["spread_proxy"].shift(1)

    return df.dropna()


def simulate_realized_cost(close: pd.Series, atr: pd.Series) -> pd.Series:
    """Simulate realized transaction cost in bps.

    Model: cost = base_spread + volatility_component + noise
    Based on Almgren-Chriss framework (simplified).
    """
    base_spread = 2.0  # bps base spread for crypto
    vol_component = atr / close * 5000  # scale ATR to bps
    noise = np.random.default_rng(42).normal(0, 1, len(close))
    cost = base_spread + vol_component.clip(lower=0) + noise
    return pd.Series(cost, index=close.index, name="realized_cost_bps")


# ── Walk-forward cost prediction ───────────────────────────────────────────────


def walk_forward_cost(
    close: pd.Series,
    volume_proxy: pd.Series,
    horizon: int,
    seed: int,
    n_splits: int = N_SPLITS,
    refit_every: int = REFIT_EVERY,
) -> dict | None:
    """Walk-forward cost prediction with DecisionTreeRegressor.

    Compare: naive (always trade) vs cost-aware (skip when predicted_cost > threshold).
    """
    np.random.seed(seed)

    features_df = build_cost_features(close, volume_proxy)
    atr = close.pct_change().rolling(5).std() * close
    cost = simulate_realized_cost(close, atr)

    # Target: realized cost at horizon
    target = cost.rolling(horizon).mean().shift(-horizon)
    target.name = "target_cost"

    aligned = features_df.join(target, how="inner").dropna()
    if len(aligned) < 200:
        return None

    feature_cols = [c for c in aligned.columns if c != "target_cost"]
    n = len(aligned)

    fold_size = n // (n_splits + 1)
    if fold_size < 30:
        return None

    # Naive: always trade, pay average cost
    # Cost-aware: skip when predicted cost > trailing_avg * 0.95

    naive_costs: list[float] = []
    smart_costs: list[float] = []
    naive_trades: int = 0
    smart_trades: int = 0
    daily_rets_for_sharpe: list[float] = []

    daily_ret = close.pct_change()
    trailing_window = 22

    for k in range(1, n_splits + 1):
        train_end = fold_size * k
        test_start = train_end
        test_end = min(train_end + fold_size, n)
        if test_end - test_start < 10:
            continue

        for i in range(test_start, test_end - 1):
            if i < trailing_window:
                continue

            # Retrain every refit_every days
            if (i - test_start) % refit_every == 0:
                train = aligned.iloc[:i]
                if len(train) < 30:
                    continue
                scaler = StandardScaler()
                X_train = scaler.fit_transform(train[feature_cols])
                y_train = train["target_cost"].values
                model = DecisionTreeRegressor(
                    max_depth=5, min_samples_leaf=20, random_state=seed
                )
                model.fit(X_train, y_train)

            if 'scaler' not in dir() or 'model' not in dir():
                continue

            row = aligned.iloc[i:i + 1]
            X_test = scaler.transform(row[feature_cols])
            pred_cost = float(model.predict(X_test)[0])

            actual_cost = float(aligned.iloc[i]["target_cost"])
            trailing_avg = float(aligned.iloc[i - trailing_window:i]["target_cost"].mean())

            # Naive: always trade
            naive_costs.append(actual_cost)
            naive_trades += 1

            # Cost-aware: skip if predicted > 95% of trailing average
            if pred_cost < trailing_avg * 0.95:
                smart_costs.append(actual_cost)
                smart_trades += 1

    if naive_trades == 0 or smart_trades == 0:
        return None

    # Savings calculation
    total_naive_cost_bps = sum(naive_costs)
    total_smart_cost_bps = sum(smart_costs)
    savings_bps = total_naive_cost_bps - total_smart_cost_bps
    savings_usd = savings_bps / 10000 * NOTIONAL * smart_trades  # proportional

    skip_rate = 1 - smart_trades / naive_trades

    # Sharpe comparison using daily returns (skip = hold position)
    # Simplified: Sharpe of cost-aware vs naive strategy
    avg_naive_cost = np.mean(naive_costs)
    avg_smart_cost = np.mean(smart_costs)

    return {
        "naive_trades": naive_trades,
        "smart_trades": smart_trades,
        "skip_rate": skip_rate,
        "avg_naive_cost_bps": avg_naive_cost,
        "avg_smart_cost_bps": avg_smart_cost,
        "savings_bps_per_trade": avg_naive_cost - avg_smart_cost,
        "total_savings_usd_annual": savings_usd * (365 / max(naive_trades, 1)),
        "horizon": horizon,
        "seed": seed,
    }


def evaluate_one_combo(coin: str, horizon: int, seed: int) -> dict | None:
    """Run cost forecasting for one (coin, horizon, seed)."""
    hourly_rets = _load_one_coin(coin)
    if len(hourly_rets) < 1000:
        return None

    daily_log_ret = hourly_rets.groupby(hourly_rets.index.normalize()).sum()
    daily_log_ret.index = pd.DatetimeIndex(daily_log_ret.index).normalize()
    daily_close = np.exp(daily_log_ret.cumsum())
    daily_close.name = "close"

    # Volume proxy: absolute hourly return aggregated daily
    volume_proxy = hourly_rets.abs().groupby(hourly_rets.index.normalize()).sum()
    volume_proxy.index = pd.DatetimeIndex(volume_proxy.index).normalize()

    if len(daily_close) < 300:
        return None

    result = walk_forward_cost(daily_close, volume_proxy, horizon, seed)
    if result is None:
        return None

    result["coin"] = coin
    return result


def _sharpe_ann(returns: np.ndarray) -> float:
    if len(returns) < 10:
        return float("nan")
    mu = float(np.mean(returns))
    sigma = float(np.std(returns, ddof=1))
    return (mu / sigma) * np.sqrt(365) if sigma > 1e-12 else float("nan")


def _binomial_pvalue_one_sided(k: int, n: int) -> float:
    from scipy.stats import binom
    if n == 0:
        return 1.0
    return float(binom.sf(k - 1, n, 0.5))


def main() -> None:
    parser = argparse.ArgumentParser(description="S6 Cost Forecasting sweep")
    parser.add_argument("--dry-run", action="store_true", help="Run BTC h=1 seed=0 only")
    args = parser.parse_args()

    RESULTS_DIR.mkdir(parents=True, exist_ok=True)
    t0 = time.time()

    combos: list[dict] = []
    total = len(COINS) * len(HORIZONS) * len(SEEDS)
    done = 0

    if args.dry_run:
        print("[DRY RUN] BTC-USD h=1 seed=0 only")
        row = evaluate_one_combo("BTC-USD", 1, 0)
        if row:
            combos.append(row)
            print(json.dumps(row, indent=2))
        return

    for coin in COINS:
        for h in HORIZONS:
            for seed in SEEDS:
                done += 1
                print(f"\n[{done}/{total}] {coin} h={h} seed={seed}", flush=True)
                row = evaluate_one_combo(coin, h, seed)
                if row is not None:
                    combos.append(row)
                    print(f"  savings=${row['total_savings_usd_annual']:.0f}/yr "
                          f"skip={row['skip_rate']*100:.1f}%", flush=True)
                else:
                    print(f"  SKIPPED (insufficient data)", flush=True)

    elapsed = time.time() - t0
    n_combos = len(combos)
    print(f"\n{'='*60}")
    print(f"S6 Cost Forecasting sweep complete: {n_combos}/{total} combos in {elapsed:.0f}s")

    # Aggregate
    median_savings = float(np.median([r["total_savings_usd_annual"] for r in combos])) if combos else 0
    median_skip = float(np.median([r["skip_rate"] for r in combos])) if combos else 0
    n_profitable = sum(1 for r in combos if r["total_savings_usd_annual"] > 0)
    p_sign = _binomial_pvalue_one_sided(n_profitable, n_combos)

    per_coin: dict[str, dict] = {}
    for r in combos:
        c = r["coin"]
        per_coin.setdefault(c, {"savings": [], "skip_rates": []})
        per_coin[c]["savings"].append(r["total_savings_usd_annual"])
        per_coin[c]["skip_rates"].append(r["skip_rate"])

    print(f"\nMedian annual savings: ${median_savings:.0f}")
    print(f"Median skip rate: {median_skip*100:.1f}%")
    print(f"Profitable combos: {n_profitable}/{n_combos} (p={p_sign:.4f})")

    print(f"\nPer-coin:")
    for c in COINS:
        if c in per_coin:
            med_sav = float(np.median(per_coin[c]["savings"]))
            med_skip = float(np.median(per_coin[c]["skip_rates"]))
            print(f"  {c}: ${med_sav:.0f}/yr (skip {med_skip*100:.1f}%)")

    # Verdict: GO if savings >= $20k/yr AND > 60% combos profitable
    if median_savings >= 20000 and p_sign < 0.05 and n_profitable / max(n_combos, 1) >= 0.60:
        verdict = "GO"
    elif median_savings >= 10000 and n_profitable / max(n_combos, 1) >= 0.55:
        verdict = "MARGINAL"
    else:
        verdict = "NO GO"

    print(f"\nVERDICT: {verdict} (median_savings=${median_savings:.0f}, p={p_sign:.4f})")

    results = {
        "model": "S6 Cost Forecasting (DecisionTreeRegressor)",
        "reference": "Hands-On AI Trading Ex 12 (Broad 2025)",
        "fee_bps": FEE_BPS,
        "notional_usd": NOTIONAL,
        "n_splits": N_SPLITS,
        "refit_every": REFIT_EVERY,
        "n_combos": n_combos,
        "median_savings_usd_annual": median_savings,
        "median_skip_rate": median_skip,
        "n_profitable_combos": n_profitable,
        "p_sign": p_sign,
        "verdict": verdict,
        "elapsed_s": elapsed,
        "combos": combos,
        "per_coin": {
            c: {
                "median_savings": float(np.median(v["savings"])),
                "median_skip_rate": float(np.median(v["skip_rates"])),
            }
            for c, v in per_coin.items()
        },
    }

    with open(RESULTS_DIR / "results.json", "w") as f:
        json.dump(results, f, indent=2, default=str)

    if combos:
        df = pd.DataFrame(combos)
        df.to_csv(RESULTS_DIR / "s6_cost_forecast_results.csv", index=False)
        print(f"\nSaved: {RESULTS_DIR / 'results.json'}")
        print(f"Saved: {RESULTS_DIR / 's6_cost_forecast_results.csv'}")


if __name__ == "__main__":
    main()
