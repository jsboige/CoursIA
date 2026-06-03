"""M14 HEAVY — Shephard & Sheppard (2010) bivariate volatility model.

Question
--------
Does the HEAVY model (High-frEquency-bAsed VolatilitY) beat HAR Classic for
crypto volatility forecasting? HEAVY jointly models returns and realized measures:

    HEAVY-r:   r_t^2 = omega_r + alpha_r * r_{t-1}^2 + beta_r * RM_{t-1}
    HEAVY-RV:  RV_t = omega_RV + alpha_RV * RM_{t-1} + beta_RV * RV_{t-1}

where RM = Realized Measure (here RV). 6 parameters total.

The HEAVY-RV equation provides volatility forecasts directly (no transform needed).
Forecast at horizon h: iterate the HEAVY-RV equation h steps.

Walk-forward 5-fold expanding, 7 coins x 3 horizons x 4 seeds = 84 combos.
Kelly cap=1.0, fee=50bps, sign-test paired Sharpe-diff vs HAR Classic baseline.

Output
------
- results/m14_heavy/results.json
- results/m14_heavy/m14_heavy_results.csv
- docs/M14_HEAVY.md (verdict)

Env: system Python 3.13 (no conda). Reuses har_model, realized_variance, m11g infra.

Reference
---------
Shephard, N. & Sheppard, K. (2010) "Realising the Future: Forecasting with
High-Frequency-Based Volatility (HEAVY) Models", J. Applied Econometrics 25(2), 197-231.
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

import numpy as np
import pandas as pd
from scipy.optimize import minimize

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

from har_model import HARModel, walk_forward_har  # noqa: E402
from intraday_loader import (  # noqa: E402
    load_yf_intraday,
)
from m11g_fee_aware_kelly import (  # noqa: E402
    _binomial_pvalue_one_sided,
    _kelly_weights_and_returns,
    _load_one_coin,
    _net_at_fee,
)
from m11c_sharpe_test import ledoit_wolf_sharpe_diff_se  # noqa: E402
from realized_variance import (  # noqa: E402
    daily_realized_variance,
    realized_variance_to_log,
)

COINS = ["BTC-USD", "ETH-USD", "SOL-USD", "LTC-USD", "XRP-USD", "ADA-USD", "DOT-USD"]
HORIZONS = [1, 5, 10]
SEEDS = [0, 1, 7, 42]
KELLY_CAP = 1.0
MU_WINDOW = 60
FEE_BPS = 50
N_SPLITS = 5
REFIT_EVERY = 22
RESULTS_DIR = SCRIPT_DIR / "results" / "m14_heavy"

# Parameter indices for clarity
# theta = [omega_r, alpha_r, beta_r, omega_RV, alpha_RV, beta_RV]


# -- HEAVY model estimation via QML -----------------------------------------

def _heavy_neg_loglik_full(
    theta: np.ndarray,
    r2: np.ndarray,
    rv: np.ndarray,
) -> float:
    """Full bivariate QML: both HEAVY-r and HEAVY-RV equations."""
    omega_r, alpha_r, beta_r, omega_RV, alpha_RV, beta_RV = theta

    n = len(r2) - 1
    if n < 20:
        return 1e12

    prev_r2 = r2[:-1]
    prev_rv = rv[:-1]
    target_r2 = r2[1:]
    target_rv = rv[1:]

    # HEAVY-r equation
    h_r = omega_r + alpha_r * prev_r2 + beta_r * prev_rv
    h_r = np.maximum(h_r, 1e-12)
    target_r2_safe = np.maximum(target_r2, 1e-12)

    # HEAVY-RV equation
    h_rv = omega_RV + alpha_RV * prev_rv + beta_RV * prev_rv
    h_rv = np.maximum(h_rv, 1e-12)
    target_rv_safe = np.maximum(target_rv, 1e-12)

    # Joint QML
    ll_r = -0.5 * np.sum(np.log(h_r) + target_r2_safe / h_r)
    ll_rv = -0.5 * np.sum(np.log(h_rv) + target_rv_safe / h_rv)

    total = ll_r + ll_rv
    if np.isnan(total) or np.isinf(total):
        return 1e12

    return -total


class HEAVYModel:
    """HEAVY (Shephard & Sheppard 2010) bivariate volatility model.

    Estimates via QML (quasi-maximum likelihood) with scipy.optimize.
    """

    def __init__(self) -> None:
        self.theta_: np.ndarray | None = None
        self.n_train_: int = 0

    def fit(self, r2: np.ndarray, rv: np.ndarray) -> "HEAVYModel":
        """Fit HEAVY model to squared returns and realized variance.

        Parameters
        ----------
        r2 : daily squared returns (r_t^2)
        rv : daily realized variance (RV_t)
        """
        r2 = np.asarray(r2, dtype=float)
        rv = np.asarray(rv, dtype=float)

        # Initialize with moment-based estimates
        rv_mean = np.mean(rv)
        r2_mean = np.mean(r2)

        # AR(1)-style init: rv_t = omega + phi * rv_{t-1}
        # phi = corr(rv_t, rv_{t-1})
        if len(rv) > 2:
            phi = np.corrcoef(rv[:-1], rv[1:])[0, 1]
            phi = max(0.1, min(phi, 0.99))
        else:
            phi = 0.8

        # Split persistence between alpha_RV and beta_RV
        alpha_rv_init = 0.3 * phi
        beta_rv_init = 0.7 * phi
        omega_rv_init = rv_mean * (1 - alpha_rv_init - beta_rv_init)

        # HEAVY-r init
        alpha_r_init = 0.1
        beta_r_init = 0.5
        omega_r_init = r2_mean * (1 - alpha_r_init - beta_r_init)

        theta0 = np.array([
            omega_r_init, alpha_r_init, beta_r_init,
            omega_rv_init, alpha_rv_init, beta_rv_init,
        ])

        # Bounds: omega > 0, alpha >= 0, beta >= 0, stationarity
        bounds = [
            (1e-8, None),   # omega_r
            (0.0, 0.99),    # alpha_r
            (0.0, 0.99),    # beta_r
            (1e-8, None),   # omega_RV
            (0.0, 0.99),    # alpha_RV
            (0.0, 0.99),    # beta_RV
        ]

        best_result = None
        best_nll = np.inf

        # Multi-start optimization
        for attempt in range(5):
            if attempt == 0:
                x0 = theta0
            else:
                # Random perturbation
                rng = np.random.RandomState(attempt * 7)
                x0 = theta0 * (1 + 0.3 * rng.randn(len(theta0)))
                x0 = np.maximum(x0, [1e-8, 0.0, 0.0, 1e-8, 0.0, 0.0])

            try:
                result = minimize(
                    _heavy_neg_loglik_full,
                    x0,
                    args=(r2, rv),
                    method="L-BFGS-B",
                    bounds=bounds,
                    options={"maxiter": 500, "ftol": 1e-10},
                )
                if result.fun < best_nll:
                    best_nll = result.fun
                    best_result = result
            except Exception:
                continue

        if best_result is None:
            raise ValueError("HEAVY optimization failed to converge")

        self.theta_ = best_result.x
        self.n_train_ = len(r2)

        # Stationarity warning
        _, _, _, omega_RV, alpha_RV, beta_RV = self.theta_
        if alpha_RV + beta_RV >= 0.999:
            import warnings
            warnings.warn(
                f"HEAVY-RV non-stationarity: alpha_RV ({alpha_RV:.4f})"
                f" + beta_RV ({beta_RV:.4f})"
                f" = {alpha_RV + beta_RV:.4f} >= 0.999"
            )

        return self

    def forecast_rv(self, rv_last: float, horizon: int = 1) -> float:
        """Iterate HEAVY-RV equation h steps for volatility forecast.

        HEAVY-RV: RV_{t+1} = omega_RV + (alpha_RV + beta_RV) * RV_t

        This is an AR(1) on RV, so h-step forecast is:
        E[RV_{t+h}] = mu * (1 - phi^h) / (1 - phi) + phi^h * RV_t
        where phi = alpha_RV + beta_RV, mu = omega_RV / (1 - phi)
        """
        _, _, _, omega_RV, alpha_RV, beta_RV = self.theta_
        phi = alpha_RV + beta_RV

        if not 0.001 <= phi <= 0.999:
            import warnings
            warnings.warn(
                f"phi={phi:.6f} clipped to [0.001, 0.999] in forecast_rv"
                " (possible estimation instability)"
            )
            phi = max(0.001, min(0.999, phi))

        # Unconditional mean
        mu = omega_RV / (1 - phi)

        # h-step ahead forecast (iterative)
        rv_cur = rv_last
        forecasts = []
        for _ in range(horizon):
            rv_cur = omega_RV + phi * rv_cur
            forecasts.append(rv_cur)

        # Average over horizon (matching HAR convention)
        return float(np.mean(forecasts))


def walk_forward_heavy(
    rv: pd.Series,
    r2_daily: pd.Series,
    horizon: int = 1,
    n_splits: int = 5,
    refit_every: int = 22,
) -> dict:
    """Walk-forward evaluation of HEAVY model.

    Returns aligned forecast series (log-RV scale) for comparison with HAR.
    """
    rv = rv.dropna().astype(float)
    r2_daily = r2_daily.dropna().astype(float)

    common_idx = rv.index.intersection(r2_daily.index)
    rv = rv.loc[common_idx]
    r2_daily = r2_daily.loc[common_idx]

    n = len(rv)
    if n < 200:
        raise ValueError(f"need >=200 daily obs, got {n}")

    log_rv = np.log(rv.clip(lower=1e-12))

    fold_size = n // (n_splits + 1)
    if fold_size < 30:
        raise ValueError(f"n={n} too small for {n_splits} splits")

    splits = []
    for k in range(1, n_splits + 1):
        train_end = fold_size * k
        test_start = train_end
        test_end = min(train_end + fold_size, n)
        splits.append((train_end, test_start, test_end))

    preds: list[float] = []
    truths: list[float] = []
    pred_dates: list[pd.Timestamp] = []
    fold_results: list[dict] = []

    for fold_idx, (train_end, test_start, test_end) in enumerate(splits):
        rv_train = rv.iloc[:train_end]
        r2_train = r2_daily.iloc[:train_end]
        if len(rv_train) < 60:
            continue

        try:
            model = HEAVYModel().fit(r2_train.values, rv_train.values)
        except Exception as e:
            print(f"    fold {fold_idx} HEAVY fit failed: {e}", flush=True)
            continue

        fold_preds: list[float] = []
        fold_truths: list[float] = []

        for i in range(test_start, test_end - horizon):
            target_window = log_rv.iloc[i : i + horizon].mean()
            rv_last = float(rv.iloc[i - 1]) if i > 0 else float(rv.iloc[0])

            rv_forecast = model.forecast_rv(rv_last, horizon=horizon)
            log_rv_forecast = float(np.log(max(rv_forecast, 1e-12)))

            fold_preds.append(log_rv_forecast)
            fold_truths.append(float(target_window))
            preds.append(log_rv_forecast)
            truths.append(float(target_window))
            pred_dates.append(rv.index[i])

            if (i - test_start) % refit_every == 0 and i > test_start:
                try:
                    model = HEAVYModel().fit(
                        r2_daily.iloc[:i].values, rv.iloc[:i].values
                    )
                except Exception:
                    pass  # keep previous model

        fp = np.asarray(fold_preds)
        ft = np.asarray(fold_truths)
        fold_mse = float(np.mean((fp - ft) ** 2)) if len(fp) else float("nan")
        fold_results.append({
            "fold": fold_idx,
            "n_test": len(fp),
            "mse_logrv": fold_mse,
        })

    preds_arr = np.asarray(preds)
    truths_arr = np.asarray(truths)
    aggregate_mse = (
        float(np.mean((preds_arr - truths_arr) ** 2)) if len(preds_arr) else float("nan")
    )
    forecasts = pd.Series(
        preds_arr, index=pd.DatetimeIndex(pred_dates), name="heavy_logrv_pred"
    )
    targets = pd.Series(
        truths_arr, index=pd.DatetimeIndex(pred_dates), name="logrv_target"
    )
    return {
        "horizon": horizon,
        "n_splits": n_splits,
        "n_total_preds": len(preds_arr),
        "aggregate_mse_logrv": aggregate_mse,
        "fold_results": fold_results,
        "forecasts": forecasts,
        "targets": targets,
    }


# -- Evaluation helpers -------------------------------------------------------

def _sharpe_ann(returns: np.ndarray) -> float:
    if len(returns) < 10:
        return float("nan")
    mu = float(np.mean(returns))
    sigma = float(np.std(returns, ddof=1))
    return (mu / sigma) * np.sqrt(365) if sigma > 1e-12 else float("nan")


def evaluate_one_combo(
    coin: str,
    horizon: int,
    seed: int,
) -> dict | None:
    """Run HEAVY vs HAR Classic for one (coin, horizon, seed) combo."""
    rng = np.random.default_rng(seed)
    hourly_rets = _load_one_coin(coin)
    if len(hourly_rets) < 1000:
        return None

    rv = daily_realized_variance(hourly_rets)
    if len(rv) < 300:
        return None

    # Daily squared returns (close-to-close)
    daily_rets_raw = hourly_rets.groupby(hourly_rets.index.normalize()).sum()
    daily_rets_raw.index = pd.DatetimeIndex(daily_rets_raw.index).normalize()
    r2_daily = (daily_rets_raw ** 2).rename("r2")

    # Align RV and r2
    common_idx = rv.index.intersection(r2_daily.index)
    rv = rv.loc[common_idx]
    r2_daily = r2_daily.loc[common_idx]

    # HAR Classic baseline
    try:
        har_out = walk_forward_har(rv, horizon=horizon, n_splits=N_SPLITS, refit_every=REFIT_EVERY)
    except Exception:
        return None

    # HEAVY
    try:
        heavy_out = walk_forward_heavy(
            rv, r2_daily, horizon=horizon, n_splits=N_SPLITS, refit_every=REFIT_EVERY
        )
    except Exception:
        return None

    har_fc = har_out["forecasts"]
    heavy_fc = heavy_out["forecasts"]
    common_fc_idx = har_fc.index.intersection(heavy_fc.index)
    if len(common_fc_idx) < 30:
        return None
    har_fc = har_fc.loc[common_fc_idx]
    heavy_fc = heavy_fc.loc[common_fc_idx]

    # Daily close returns
    daily_rets = hourly_rets.groupby(hourly_rets.index.normalize()).sum().rename("r_daily")
    daily_rets.index = pd.DatetimeIndex(daily_rets.index).normalize()
    daily_rets = daily_rets.reindex(common_fc_idx).dropna()
    if len(daily_rets) < 30:
        return None
    har_fc = har_fc.reindex(daily_rets.index)
    heavy_fc = heavy_fc.reindex(daily_rets.index)

    # Kelly weights for each model
    har_pair = _kelly_weights_and_returns(daily_rets, har_fc, MU_WINDOW, KELLY_CAP)
    heavy_pair = _kelly_weights_and_returns(daily_rets, heavy_fc, MU_WINDOW, KELLY_CAP)
    if har_pair is None or heavy_pair is None:
        return None
    har_w, r = har_pair
    heavy_w, _ = heavy_pair
    if len(r) < 50:
        return None

    # Net returns at FEE_BPS
    har_net = _net_at_fee(har_w, r, FEE_BPS)
    heavy_net = _net_at_fee(heavy_w, r, FEE_BPS)
    bh_net = r.copy()

    # Sharpe
    sharpe_har = _sharpe_ann(har_net)
    sharpe_heavy = _sharpe_ann(heavy_net)
    sharpe_bh = _sharpe_ann(bh_net)
    delta_sharpe_heavy_vs_har = sharpe_heavy - sharpe_har

    # LW2008 paired Sharpe-diff SE
    _, _, _, se = ledoit_wolf_sharpe_diff_se(heavy_net, har_net)
    t_stat = delta_sharpe_heavy_vs_har / se if isinstance(se, float) and se > 1e-12 else float("nan")

    # MSE comparison on log-RV
    target = har_out["targets"].reindex(common_fc_idx).dropna()
    har_pred_aligned = har_fc.reindex(target.index)
    heavy_pred_aligned = heavy_fc.reindex(target.index)
    mse_har = float(np.mean((har_pred_aligned - target) ** 2))
    mse_heavy = float(np.mean((heavy_pred_aligned - target) ** 2))
    mse_reduction_pct = (mse_heavy - mse_har) / mse_har * 100 if mse_har > 0 else float("nan")

    return {
        "coin": coin,
        "horizon": horizon,
        "seed": seed,
        "sharpe_har": sharpe_har,
        "sharpe_heavy": sharpe_heavy,
        "sharpe_bh": sharpe_bh,
        "delta_sharpe_heavy_vs_har": delta_sharpe_heavy_vs_har,
        "lw_se": se,
        "t_stat": t_stat,
        "mse_har": mse_har,
        "mse_heavy": mse_heavy,
        "mse_reduction_pct": mse_reduction_pct,
        "n_obs": len(r),
        "heavy_preds": len(heavy_fc),
        "har_preds": len(har_fc),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="M14 HEAVY sweep")
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
                else:
                    print(f"  SKIPPED (insufficient data)", flush=True)

    elapsed = time.time() - t0
    print(f"\n{'='*60}")
    print(f"M14 HEAVY sweep complete: {len(combos)}/{total} combos in {elapsed:.0f}s")

    # Aggregate sign-test
    n_combos = len(combos)
    n_heavy_beats_har = sum(1 for r in combos if r["delta_sharpe_heavy_vs_har"] > 0)
    median_delta = float(np.median([r["delta_sharpe_heavy_vs_har"] for r in combos])) if combos else float("nan")
    median_mse = float(np.median([r["mse_reduction_pct"] for r in combos])) if combos else float("nan")
    p_sign = _binomial_pvalue_one_sided(n_heavy_beats_har, n_combos)

    # Per-coin aggregation
    per_coin: dict[str, dict] = {}
    for r in combos:
        c = r["coin"]
        per_coin.setdefault(c, {"deltas": [], "mses": []})
        per_coin[c]["deltas"].append(r["delta_sharpe_heavy_vs_har"])
        per_coin[c]["mses"].append(r["mse_reduction_pct"])

    # Per-horizon aggregation
    per_horizon: dict[int, dict] = {}
    for r in combos:
        h = r["horizon"]
        per_horizon.setdefault(h, {"deltas": [], "mses": []})
        per_horizon[h]["deltas"].append(r["delta_sharpe_heavy_vs_har"])
        per_horizon[h]["mses"].append(r["mse_reduction_pct"])

    print(f"\nSign-test: {n_heavy_beats_har}/{n_combos} ({n_heavy_beats_har/n_combos*100:.1f}%) HEAVY>HAR")
    print(f"  p-value = {p_sign:.4f}")
    print(f"  median delta-Sharpe = {median_delta:+.4f}")
    print(f"  median MSE change = {median_mse:+.1f}%")
    print(f"\nPer-coin:")
    for c in COINS:
        if c in per_coin:
            med = float(np.median(per_coin[c]["deltas"]))
            med_mse = float(np.median(per_coin[c]["mses"]))
            n_beats = sum(1 for d in per_coin[c]["deltas"] if d > 0)
            n_total = len(per_coin[c]["deltas"])
            print(f"  {c}: {med:+.4f} (MSE {med_mse:+.1f}%, beats {n_beats}/{n_total})")

    print(f"\nPer-horizon:")
    for h in HORIZONS:
        if h in per_horizon:
            med = float(np.median(per_horizon[h]["deltas"]))
            n_beats = sum(1 for d in per_horizon[h]["deltas"] if d > 0)
            n_total = len(per_horizon[h]["deltas"])
            print(f"  h={h}: {med:+.4f} ({n_beats}/{n_total})")

    # Verdict (G.2 strict)
    if p_sign < 0.05 and n_heavy_beats_har / max(n_combos, 1) >= 0.60:
        verdict = "BEATS"
    elif p_sign < 0.10 and n_heavy_beats_har / max(n_combos, 1) >= 0.55:
        verdict = "INCONCLUSIVE"
    else:
        verdict = "NO BEATS"

    print(f"\nVERDICT: {verdict} (p={p_sign:.4f}, win_rate={n_heavy_beats_har/n_combos*100:.1f}%)")

    # Save
    results = {
        "model": "HEAVY",
        "reference": "Shephard & Sheppard (2010)",
        "kelly_cap": KELLY_CAP,
        "fee_bps": FEE_BPS,
        "mu_window": MU_WINDOW,
        "n_splits": N_SPLITS,
        "refit_every": REFIT_EVERY,
        "n_combos": n_combos,
        "n_heavy_beats_har": n_heavy_beats_har,
        "win_rate": n_heavy_beats_har / max(n_combos, 1),
        "p_sign": p_sign,
        "median_delta_sharpe": median_delta,
        "median_mse_reduction": median_mse,
        "verdict": verdict,
        "elapsed_s": elapsed,
        "combos": combos,
        "per_coin": {
            c: {
                "median_delta_sharpe": float(np.median(v["deltas"])),
                "median_mse_reduction": float(np.median(v["mses"])),
                "n_beats": sum(1 for d in v["deltas"] if d > 0),
                "n_total": len(v["deltas"]),
            }
            for c, v in per_coin.items()
        },
        "per_horizon": {
            str(h): {
                "median_delta_sharpe": float(np.median(v["deltas"])),
                "median_mse_reduction": float(np.median(v["mses"])),
                "n_beats": sum(1 for d in v["deltas"] if d > 0),
                "n_total": len(v["deltas"]),
            }
            for h, v in per_horizon.items()
        },
    }

    with open(RESULTS_DIR / "results.json", "w") as f:
        json.dump(results, f, indent=2, default=str)

    # CSV
    if combos:
        df = pd.DataFrame(combos)
        df.to_csv(RESULTS_DIR / "m14_heavy_results.csv", index=False)
        print(f"\nSaved: {RESULTS_DIR / 'results.json'}")
        print(f"Saved: {RESULTS_DIR / 'm14_heavy_results.csv'}")


if __name__ == "__main__":
    main()
