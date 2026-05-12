"""DLinear for log-RV volatility forecasting: HAR comparison.

Implements Zeng et al. (2023) DLinear — a single nn.Linear layer — adapted
from classification (Ensemble-DLinear-TFT) to log-RV regression.

DLinear regression:
    y_hat = Linear(seq_len * input_dim -> 1)

Optional series decomposition (moving average trend):
    trend = AvgPool1d(x, kernel_size=kernel_size)
    seasonal = x - trend
    y_hat = Linear_trend(trend) + Linear_seasonal(seasonal)

Walk-forward 5-fold x 4 seeds x 3 horizons x 7 coins.
DM test vs classic HAR baseline (Corsi 2009).

Usage:
    python dlinear_vol.py --horizons 1 5 10 --seeds 0 7 42 99 --skip-remote
    python dlinear_vol.py --horizons 1 5 10 --seeds 0 7 42 99
"""

from __future__ import annotations

import argparse
import json
import time
from pathlib import Path

import numpy as np
import pandas as pd
import torch
import torch.nn as nn

from dm_test import dm_verdict
from har_model import walk_forward_har
from intraday_loader import (
    hourly_log_returns,
    load_binance_eth,
    load_bitstamp_btc,
    load_yf_intraday,
)
from realized_variance import (
    daily_realized_variance,
    realized_variance_to_log,
)


class DLinearVol(nn.Module):
    """DLinear for univariate log-RV forecasting.

    Simplest possible deep learning baseline: a single linear projection
    from (seq_len,) to (horizon,). Optional decomposition into trend +
    seasonal (moving average detrending).
    """

    def __init__(
        self,
        seq_len: int = 22,
        horizon: int = 1,
        decompose: bool = False,
        kernel_size: int = 5,
    ) -> None:
        super().__init__()
        self.seq_len = seq_len
        self.horizon = horizon
        self.decompose = decompose
        self.kernel_size = kernel_size

        if decompose:
            self.linear_trend = nn.Linear(seq_len, horizon)
            self.linear_seasonal = nn.Linear(seq_len, horizon)
            self.avg_pool = nn.AvgPool1d(
                kernel_size=kernel_size, stride=1, padding=kernel_size // 2,
            )
        else:
            self.linear = nn.Linear(seq_len, horizon)

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        if self.decompose:
            trend = self.avg_pool(x.unsqueeze(1)).squeeze(1)
            seasonal = x - trend
            return self.linear_trend(trend) + self.linear_seasonal(seasonal)
        return self.linear(x)


def create_sequences(
    data: np.ndarray,
    seq_len: int,
    horizon: int,
) -> tuple[np.ndarray, np.ndarray]:
    x, y = [], []
    for i in range(len(data) - seq_len - horizon + 1):
        x.append(data[i:i + seq_len])
        y.append(data[i + seq_len:i + seq_len + horizon])
    return np.asarray(x), np.asarray(y)


def train_dlinear(
    x_train: np.ndarray,
    y_train: np.ndarray,
    seq_len: int,
    horizon: int,
    decompose: bool = False,
    epochs: int = 100,
    lr: float = 1e-3,
    seed: int = 0,
) -> DLinearVol:
    torch.manual_seed(seed)
    np.random.seed(seed)

    model = DLinearVol(seq_len=seq_len, horizon=horizon, decompose=decompose)
    optimizer = torch.optim.AdamW(model.parameters(), lr=lr, weight_decay=1e-4)

    x_t = torch.tensor(x_train, dtype=torch.float32)
    y_t = torch.tensor(y_train, dtype=torch.float32)

    if horizon == 1:
        y_t = y_t.squeeze(-1)

    dataset = torch.utils.data.TensorDataset(x_t, y_t)
    loader = torch.utils.data.DataLoader(
        dataset, batch_size=32, shuffle=True,
        generator=torch.Generator().manual_seed(seed),
    )

    model.train()
    for _ in range(epochs):
        for xb, yb in loader:
            pred = model(xb)
            if horizon == 1:
                pred = pred.squeeze(-1)
            loss = nn.functional.mse_loss(pred, yb)
            optimizer.zero_grad()
            loss.backward()
            nn.utils.clip_grad_norm_(model.parameters(), 1.0)
            optimizer.step()

    return model


def predict_dlinear(
    model: DLinearVol,
    x_test: np.ndarray,
    horizon: int,
) -> np.ndarray:
    model.eval()
    with torch.no_grad():
        x_t = torch.tensor(x_test, dtype=torch.float32)
        pred = model(x_t).numpy()
    if horizon == 1:
        return pred.squeeze(-1)
    return pred


def _make_split_indices(n: int, n_splits: int) -> list[tuple[int, int, int]]:
    if n_splits < 2:
        raise ValueError("n_splits must be >= 2")
    fold_size = n // (n_splits + 1)
    if fold_size < 30:
        raise ValueError(f"n={n} too small for {n_splits} splits")
    splits = []
    for k in range(1, n_splits + 1):
        train_end = fold_size * k
        test_start = train_end
        test_end = min(train_end + fold_size, n)
        splits.append((train_end, test_start, test_end))
    return splits


def walk_forward_dlinear(
    log_rv: np.ndarray,
    rv_index: pd.DatetimeIndex,
    seq_len: int = 22,
    horizon: int = 1,
    n_splits: int = 5,
    refit_every: int = 22,
    epochs: int = 100,
    lr: float = 1e-3,
    decompose: bool = False,
    seed: int = 0,
) -> dict:
    n = len(log_rv)
    if n < seq_len + horizon + 100:
        raise ValueError(f"need >= {seq_len + horizon + 100} obs, got {n}")

    splits = _make_split_indices(n, n_splits)

    mean_val = float(np.mean(log_rv[:max(100, n // (n_splits + 1))]))
    std_val = max(float(np.std(log_rv[:max(100, n // (n_splits + 1))])), 1e-6)

    preds: list[float] = []
    truths: list[float] = []
    pred_dates: list[pd.Timestamp] = []

    for fold_idx, (train_end, test_start, test_end) in enumerate(splits):
        if test_end - horizon < test_start + 1:
            continue

        train_data = log_rv[:train_end]
        train_mean = float(np.mean(train_data))
        train_std = max(float(np.std(train_data)), 1e-6)
        normed = (log_rv - train_mean) / train_std

        x_all, y_all = create_sequences(normed, seq_len, horizon)

        train_slice_end = train_end - seq_len - horizon + 1
        if train_slice_end < 10:
            continue

        x_train = x_all[:train_slice_end]
        y_train = y_all[:train_slice_end]

        model = train_dlinear(
            x_train, y_train, seq_len, horizon,
            decompose=decompose, epochs=epochs, lr=lr, seed=seed,
        )

        for i in range(test_start, test_end - horizon):
            idx_in_seq = i - seq_len - horizon + 1
            if idx_in_seq < 0:
                continue

            x_input = normed[i - seq_len:i].reshape(1, -1)
            pred_normed = predict_dlinear(model, x_input, horizon)
            if horizon == 1:
                pred_raw = float(pred_normed[0]) * train_std + train_mean
            else:
                pred_raw = float(np.mean(pred_normed[0])) * train_std + train_mean

            target_window = float(np.mean(log_rv[i:i + horizon]))

            preds.append(pred_raw)
            truths.append(target_window)
            pred_dates.append(rv_index[i])

            if (i - test_start) % refit_every == 0 and i > test_start:
                train_data = log_rv[:i]
                train_mean = float(np.mean(train_data))
                train_std = max(float(np.std(train_data)), 1e-6)
                normed = (log_rv - train_mean) / train_std
                x_all, y_all = create_sequences(normed, seq_len, horizon)
                refit_end = i - seq_len - horizon + 1
                if refit_end > 10:
                    model = train_dlinear(
                        x_all[:refit_end], y_all[:refit_end],
                        seq_len, horizon,
                        decompose=decompose, epochs=epochs, lr=lr, seed=seed,
                    )

    preds_arr = np.asarray(preds)
    truths_arr = np.asarray(truths)
    aggregate_mse = float(np.mean((preds_arr - truths_arr) ** 2)) if len(preds_arr) else float("nan")

    forecasts = pd.Series(preds_arr, index=pd.DatetimeIndex(pred_dates), name="dlinear_logrv_pred")
    targets = pd.Series(truths_arr, index=pd.DatetimeIndex(pred_dates), name="logrv_target")

    return {
        "horizon": horizon,
        "seed": seed,
        "seq_len": seq_len,
        "decompose": decompose,
        "n_splits": n_splits,
        "n_total_preds": len(preds_arr),
        "aggregate_mse_logrv": aggregate_mse,
        "forecasts": forecasts,
        "targets": targets,
    }


def _load_panel(
    skip_remote: bool,
    extra_coins: list[str] | None = None,
) -> dict[str, pd.Series]:
    out: dict[str, pd.Series] = {}
    print("[load] BTC Bitstamp 1h ...")
    btc = load_bitstamp_btc()
    out["BTC-USD"] = hourly_log_returns(btc)
    print(f"  BTC: {len(out['BTC-USD'])} obs")
    print("[load] ETH Binance 1h ...")
    eth = load_binance_eth()
    out["ETH-USD"] = hourly_log_returns(eth)
    print(f"  ETH: {len(out['ETH-USD'])} obs")
    if not skip_remote:
        for ticker in ["SOL-USD", "LTC-USD", "XRP-USD", "ADA-USD", "DOT-USD"] + (extra_coins or []):
            try:
                print(f"[load] {ticker} yfinance 1h ...")
                ds = load_yf_intraday(ticker)
                out[ticker] = hourly_log_returns(ds)
                print(f"  {ticker}: {len(out[ticker])} obs")
            except Exception as exc:
                print(f"[WARN] {ticker} skipped ({exc.__class__.__name__}: {exc})")
    return out


def aggregate_verdicts(rows: list[dict]) -> list[dict]:
    from collections import defaultdict

    grouped: dict[tuple, list[dict]] = defaultdict(list)
    for r in rows:
        if "skipped" in r or "dlinear_mse_logrv" not in r:
            continue
        key = (r["coin"], r["horizon"])
        grouped[key].append(r)

    results = []
    for (coin, h), seeds_rows in sorted(grouped.items()):
        n_seeds = len(seeds_rows)
        dl_mses = [r["dlinear_mse_logrv"] for r in seeds_rows]
        har_mses = [r["har_mse_logrv"] for r in seeds_rows]
        verdicts = [r.get("dm_verdict", "UNKNOWN") for r in seeds_rows]
        p_values = [r.get("dm_pvalue", 1.0) for r in seeds_rows]

        mean_dl = float(np.nanmean(dl_mses))
        mean_har = float(np.nanmean(har_mses))
        std_dl = float(np.nanstd(dl_mses))
        mean_reduction = (mean_har - mean_dl) / mean_har * 100 if mean_har > 0 else 0.0

        n_beats = sum(1 for v in verdicts if "BEATS" in v and "BEATEN" not in v)
        n_beaten = sum(1 for v in verdicts if "BEATEN" in v)
        n_inconclusive = sum(1 for v in verdicts if v == "INCONCLUSIVE")

        if n_beaten > 0:
            agg_verdict = "NO BEATS"
        elif n_beats == n_seeds and std_dl < abs(mean_har - mean_dl):
            agg_verdict = "BEATS"
        elif n_beats > 0:
            agg_verdict = "INCONCLUSIVE"
        else:
            agg_verdict = "INCONCLUSIVE"

        results.append({
            "coin": coin,
            "horizon": h,
            "n_seeds": n_seeds,
            "mean_dlinear_mse": mean_dl,
            "std_dlinear_mse": std_dl,
            "mean_har_mse": mean_har,
            "mean_reduction_pct": mean_reduction,
            "n_beats": n_beats,
            "n_beaten": n_beaten,
            "n_inconclusive": n_inconclusive,
            "mean_dm_pvalue": float(np.nanmean(p_values)),
            "verdict": agg_verdict,
        })

    return results


def _eval_one_coin(
    coin: str,
    hourly_rets: pd.Series,
    horizons: list[int],
    seeds: list[int],
    seq_len: int = 22,
    n_splits: int = 5,
    refit_every: int = 22,
    epochs: int = 100,
    decompose: bool = False,
) -> list[dict]:
    rv = daily_realized_variance(hourly_rets)
    if len(rv) < 300:
        print(f"  [{coin}] SKIPPED: only {len(rv)} RV days")
        return [{"coin": coin, "horizon": h, "seed": s, "skipped": "rv<300"}
                for h in horizons for s in seeds]

    log_rv = realized_variance_to_log(rv)
    log_rv_arr = log_rv.values.astype(float)
    rv_idx = rv.index

    print(f"\n[{coin}] {len(rv)} RV days, log_rv var={log_rv.var():.4f}")

    rows: list[dict] = []
    for h in horizons:
        # Classic HAR baseline (deterministic, seed 0 reference)
        try:
            har_out = walk_forward_har(rv, horizon=h, n_splits=n_splits, refit_every=refit_every)
            har_mse = har_out["aggregate_mse_logrv"]
            har_forecasts = har_out["forecasts"]
            har_targets = har_out["targets"]
            har_errors = (har_forecasts - har_targets).dropna().values
            print(f"  h={h} HAR baseline MSE={har_mse:.5f} ({har_out['n_total_preds']} preds)")
        except Exception as exc:
            print(f"  h={h} HAR baseline FAILED: {exc}")
            har_mse = float("nan")
            har_errors = None
            continue

        for seed in seeds:
            try:
                dl_out = walk_forward_dlinear(
                    log_rv_arr, rv_idx,
                    seq_len=seq_len,
                    horizon=h,
                    n_splits=n_splits,
                    refit_every=refit_every,
                    epochs=epochs,
                    decompose=decompose,
                    seed=seed,
                )
                dl_mse = dl_out["aggregate_mse_logrv"]
                dl_forecasts = dl_out["forecasts"]
                dl_targets = dl_out["targets"]
                dl_errors = (dl_forecasts - dl_targets).dropna().values
            except Exception as exc:
                print(f"  h={h} seed={seed} DLinear FAILED: {exc}")
                rows.append({
                    "coin": coin, "horizon": h, "seed": seed,
                    "dlinear_mse_logrv": float("nan"), "har_mse_logrv": float(har_mse),
                    "dm_verdict": "FAILED",
                })
                continue

            # DM test: DLinear vs HAR
            dm_info = {}
            if har_errors is not None and len(dl_errors) >= 10 and len(har_errors) >= 10:
                min_len = min(len(dl_errors), len(har_errors))
                try:
                    dm = dm_verdict(dl_errors[:min_len], har_errors[:min_len], horizon=h)
                    dm_info = {
                        "dm_stat": dm["dm_statistic"],
                        "dm_pvalue": dm["p_value"],
                        "dm_verdict": dm["verdict"],
                        "dm_mean_loss_diff": dm["mean_loss_diff"],
                    }
                    print(f"  h={h} seed={seed} DLinear MSE={dl_mse:.5f} "
                          f"DM={dm['dm_statistic']:.3f} p={dm['p_value']:.4f} "
                          f"-> {dm['verdict']}")
                except Exception as exc:
                    print(f"  h={h} seed={seed} DM FAILED: {exc}")
                    dm_info = {"dm_verdict": "DM_FAILED"}
            else:
                dm_info = {"dm_verdict": "INSUFFICIENT_DATA"}

            rows.append({
                "coin": coin,
                "horizon": h,
                "seed": seed,
                "seq_len": seq_len,
                "decompose": decompose,
                "n_rv_days": int(len(rv)),
                "n_predictions": int(dl_out["n_total_preds"]),
                "dlinear_mse_logrv": float(dl_mse),
                "har_mse_logrv": float(har_mse),
                "mse_reduction_pct": float((har_mse - dl_mse) / har_mse * 100) if har_mse > 0 else float("nan"),
                **dm_info,
            })

    return rows


def main() -> None:
    parser = argparse.ArgumentParser(description="DLinear-vol vs HAR baseline")
    parser.add_argument("--horizons", type=int, nargs="+", default=[1, 5, 10])
    parser.add_argument("--seeds", type=int, nargs="+", default=[0, 7, 42, 99])
    parser.add_argument("--seq-len", type=int, default=22)
    parser.add_argument("--n-splits", type=int, default=5)
    parser.add_argument("--refit-every", type=int, default=22)
    parser.add_argument("--epochs", type=int, default=100)
    parser.add_argument("--decompose", action="store_true",
                        help="Enable trend/seasonal decomposition")
    parser.add_argument("--skip-remote", action="store_true")
    parser.add_argument("--extra-coins", type=str, nargs="*", default=None)
    parser.add_argument("--out-json", type=str, default="results/m4_dlinear_vol.json")
    args = parser.parse_args()

    t0 = time.time()
    panel = _load_panel(args.skip_remote, extra_coins=args.extra_coins)

    all_rows: list[dict] = []
    for coin, rets in panel.items():
        rows = _eval_one_coin(
            coin=coin,
            hourly_rets=rets,
            horizons=args.horizons,
            seeds=args.seeds,
            seq_len=args.seq_len,
            n_splits=args.n_splits,
            refit_every=args.refit_every,
            epochs=args.epochs,
            decompose=args.decompose,
        )
        all_rows.extend(rows)

    agg = aggregate_verdicts(all_rows)

    print("\n=== M4 DLinear-vol vs HAR: Per-(coin, horizon) Verdicts ===")
    agg_df = pd.DataFrame(agg)
    if len(agg_df):
        print(agg_df.to_string(index=False))

    n_beats = sum(1 for r in agg if r["verdict"] == "BEATS")
    n_no = sum(1 for r in agg if r["verdict"] == "NO BEATS")
    n_inc = sum(1 for r in agg if r["verdict"] == "INCONCLUSIVE")
    print(f"\nSummary: {n_beats} BEATS / {n_no} NO BEATS / {n_inc} INCONCLUSIVE "
          f"(out of {len(agg)} configs)")

    out_path = Path(args.out_json)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps({
        "rows": all_rows,
        "aggregated": agg,
        "elapsed_s": time.time() - t0,
        "config": {
            "horizons": args.horizons,
            "seeds": args.seeds,
            "seq_len": args.seq_len,
            "n_splits": args.n_splits,
            "refit_every": args.refit_every,
            "epochs": args.epochs,
            "decompose": args.decompose,
        },
    }, indent=2))
    print(f"\n[done] {time.time() - t0:.1f}s -- wrote {out_path}")


if __name__ == "__main__":
    main()
