"""M4 DLinear-vol on ETF daily range-vol -- does the BTC log-RV edge transfer?

Extension of the M4 DLinear-vol §C entry (REGISTRY.md 2026-08-15, issue #11036:
BEATS 3/3 on BTC-USD hourly RV under --loss-fn mse) to the anti-bias ETF
basket SPY / TLT / GLD. The vol-forecasting terrain is the ONLY family with a
valid §C BEATS in this pipeline; every direction rung is NO BEATS (ETF
direction 9/9 #11427, foundation models #8610/#8620, ladder #1409). The open
question this script answers: is the M4 edge BTC-specific, or does it transfer
to equity/bond/gold ETFs?

Question
--------
Does DLinear beat the HAR baseline (Corsi 2009) for log-RV forecasting on ETF
daily data, at horizons {1, 5, 10} days, under the §C CONJUNCTION?

Terrain commun
--------------
- Universe: SPY / TLT / GLD daily OHLCV from datasets/panier (anti-bias
  basket, no FAANG/Mag7), 2005-01-03 -> 2026-08-14, 5438 obs per symbol
  (vs 2278 RV days for BTC -- 2.4x more data).
- RV estimator: Garman-Klass (1980) from daily OHLC,
  RV_GK = 0.5*ln(H/L)^2 - (2*ln(2)-1)*ln(C/O)^2,
  ~7.4x more efficient than squared daily returns. The BTC entries sum
  hourly squared returns; the estimator differs by necessity (no intraday
  ETF data on disk), but internal consistency is what §C needs: model and
  HAR baseline are fitted on the SAME GK series with the SAME walk-forward.
- Protocol: walk-forward 5-fold expanding, refit_every=110 (M15's documented
  cadence, REGISTRY 2026-08-14; M4-BTC used 22 on 2278 days -- the refit
  cadence is a legitimate, documented WF hyperparameter; 110 trades runtime
  for 2.4x more test points), seeds {0,1,7,42} (>=4 among 0/1/7/42/99,
  §C point 2).
- Baselines: HAR (Corsi 2009, reference) + persistence (random walk, last
  observed log-RV vs the same h-step mean targets).
- Gate (§C CONJUNCTION, both legs required):
    * sigma leg : mean_reduction >= 2 * edge_std_pct (cross-seed)
    * DM leg    : dm_p_median < 0.05 on a PRECISION loss (--loss-fn mse).
  loss_fn="linear" is a bias control, never the conjunction leg
  (#10956/#10961). Per-seed signed bias is reported for model AND baseline
  (§C point 7): a bias-carried edge declares itself.

Reuses the proven M4 §C machinery verbatim: walk_forward_har (har_model),
walk_forward_dlinear + aggregate_verdicts (dlinear_vol), dm_verdict (dm_test),
realized_variance_to_log (realized_variance). Only the RV source differs.

Run
---
CUDA_VISIBLE_DEVICES=2 python -u etf_vol.py --seeds 0 1 7 42 \
    --horizons 1 5 10 --loss-fn mse \
    --out-json results/m4_dlinear_vol_etf_sc_mse/results.json
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

import numpy as np
import pandas as pd
import torch

SCRIPTS_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS_DIR))
sys.path.insert(0, str(SCRIPTS_DIR.parent.parent / "shared"))

from dm_test import dm_verdict                      # noqa: E402
from dlinear_vol import (                           # noqa: E402
    aggregate_verdicts,
    walk_forward_dlinear,
)
from gpu_training import thermal_check              # noqa: E402
from har_model import walk_forward_har              # noqa: E402
from log_lines import (                              # noqa: E402
    format_dm_verdict_line,
    format_har_baseline_line,
)
from realized_variance import realized_variance_to_log  # noqa: E402

PANIER_DIR = SCRIPTS_DIR.parent / "datasets" / "panier"
GK_CONST = 2.0 * np.log(2.0) - 1.0  # 0.3862943...


def garman_klass_rv(df: pd.DataFrame) -> pd.Series:
    """Daily Garman-Klass (1980) RV from OHLC columns.

    RV_GK = 0.5*ln(H/L)^2 - (2*ln2 - 1)*ln(C/O)^2
    ~7.4x more efficient than the squared-daily-return estimator. Negative
    values (degenerate zero-range days) are floored by realized_variance_to_log.
    """
    df = df.copy()
    df["Date"] = pd.to_datetime(df["Date"])
    df = df.set_index("Date").sort_index()
    for col in ["Open", "High", "Low", "Close"]:
        if col not in df.columns:
            raise ValueError(f"missing OHLC column {col!r}")
    hl = np.log(df["High"] / df["Low"])
    co = np.log(df["Close"] / df["Open"])
    rv = 0.5 * hl.pow(2) - GK_CONST * co.pow(2)
    rv = rv.replace([np.inf, -np.inf], np.nan).dropna()
    rv.name = "rv_gk"
    return rv.astype(float)


def persistence_mse(
    log_rv: np.ndarray,
    horizons: list[int],
    n_splits: int,
) -> dict[int, float]:
    """Random-walk baseline MSE on the SAME walk-forward windows as the models.

    Prediction for day i is the last observed log-RV (log_rv[i-1]); target is
    the mean of the next h values -- identical construction to
    walk_forward_dlinear / walk_forward_har, so the MSE is directly comparable.
    """
    from dlinear_vol import _make_split_indices

    n = len(log_rv)
    out: dict[int, float] = {}
    for h in horizons:
        errs: list[float] = []
        for train_end, test_start, test_end in _make_split_indices(n, n_splits):
            for i in range(test_start, test_end - h):
                if i - 1 < 0:
                    continue
                pred = float(log_rv[i - 1])
                target = float(np.mean(log_rv[i:i + h]))
                errs.append((pred - target) ** 2)
        out[h] = float(np.mean(errs)) if errs else float("nan")
    return out


def eval_one_symbol(
    symbol: str,
    rv: pd.Series,
    horizons: list[int],
    seeds: list[int],
    seq_len: int,
    n_splits: int,
    refit_every: int,
    epochs: int,
    loss_fn: str,
    on_row=None,
    done: set[tuple] | None = None,
) -> list[dict]:
    log_rv = realized_variance_to_log(rv)
    log_rv_arr = log_rv.values.astype(float)
    rv_idx = rv.index

    print(f"\n[{symbol}] {len(rv)} RV days, log_rv var={log_rv.var():.4f}")
    pers = persistence_mse(log_rv_arr, horizons, n_splits)
    for h, m in pers.items():
        print(f"  persistence (random walk) MSE h={h}: {m:.5f}")

    rows: list[dict] = []
    for h in horizons:
        thermal_check(80, 30, verbose=True)
        try:
            har_out = walk_forward_har(rv, horizon=h, n_splits=n_splits,
                                       refit_every=refit_every)
            har_mse = har_out["aggregate_mse_logrv"]
            har_errors = (har_out["forecasts"] - har_out["targets"]).dropna().values
            har_bias_oos = float(np.mean(har_errors)) if len(har_errors) else float("nan")
            print(format_har_baseline_line(
                h, har_mse, har_bias_oos, har_out["n_total_preds"]))
        except Exception as exc:
            print(f"  h={h} HAR baseline FAILED: {exc}")
            continue

        for seed in seeds:
            if done is not None and (symbol, h, seed) in done:
                print(f"  h={h} seed={seed} already done, skipping")
                continue
            thermal_check(80, 30, verbose=True)
            try:
                dl_out = walk_forward_dlinear(
                    log_rv_arr, rv_idx,
                    seq_len=seq_len, horizon=h, n_splits=n_splits,
                    refit_every=refit_every, epochs=epochs, seed=seed,
                )
            except Exception as exc:
                print(f"  h={h} seed={seed} DLinear FAILED: {exc}")
                row = {"coin": symbol, "horizon": h, "seed": seed,
                       "dlinear_mse_logrv": float("nan"),
                       "har_mse_logrv": float(har_mse),
                       "dm_verdict": "FAILED"}
                rows.append(row)
                if on_row:
                    on_row(row)
                continue

            dl_mse = dl_out["aggregate_mse_logrv"]
            dl_errors = (dl_out["forecasts"] - dl_out["targets"]).dropna().values
            dl_bias_oos = float(np.mean(dl_errors)) if len(dl_errors) else float("nan")

            dm_info = {}
            # Le verdict DM porte sur l'echantillon ALIGNE (tronque a la
            # longueur commune des deux series d'erreurs), pas sur l'agregat
            # HAR : c'est cette valeur qu'il faut imprimer (#12681).
            min_len = min(len(dl_errors), len(har_errors))
            mse_har_aligned = (float(np.mean(har_errors[:min_len] ** 2))
                               if min_len else float("nan"))
            if len(dl_errors) >= 10 and len(har_errors) >= 10:
                try:
                    dm = dm_verdict(dl_errors[:min_len], har_errors[:min_len],
                                    horizon=h, loss_fn=loss_fn)
                    dm_info = {
                        "dm_stat": dm["dm_statistic"],
                        "dm_pvalue": dm["p_value"],
                        "dm_verdict": dm["verdict"],
                        "dm_mean_loss_diff": dm["mean_loss_diff"],
                    }
                    print(format_dm_verdict_line(
                        "DLinear", h, seed, dl_mse, mse_har_aligned,
                        dl_bias_oos, dm["dm_statistic"], dm["p_value"],
                        dm["verdict"]))
                except Exception as exc:
                    print(f"  h={h} seed={seed} DM FAILED: {exc}")
                    dm_info = {"dm_verdict": "DM_FAILED"}
            else:
                dm_info = {"dm_verdict": "INSUFFICIENT_DATA"}

            row = {
                "coin": symbol, "horizon": h, "seed": seed,
                "seq_len": seq_len, "refit_every": refit_every,
                "persistence_mse_logrv": pers[h],
                "har_bias_oos": har_bias_oos,
                "dlinear_bias_oos": dl_bias_oos,
                "n_rv_days": int(len(rv)),
                "n_predictions": int(dl_out["n_total_preds"]),
                "dlinear_mse_logrv": float(dl_mse),
                "har_mse_logrv": float(har_mse),
                "har_mse_aligned": mse_har_aligned,
                "mse_reduction_pct": (float((har_mse - dl_mse) / har_mse * 100)
                                      if har_mse > 0 else float("nan")),
                **dm_info,
            }
            rows.append(row)
            if on_row:
                on_row(row)
    return rows


def _done_combos(ckpt_path: Path) -> set[tuple]:
    """(coin, horizon, seed) already persisted with a finite result."""
    done: set[tuple] = set()
    if not ckpt_path.exists():
        return done
    with open(ckpt_path, encoding="utf-8") as fh:
        for line in fh:
            try:
                r = json.loads(line)
            except json.JSONDecodeError:
                continue
            mse = r.get("dlinear_mse_logrv", float("nan"))
            if not np.isnan(mse):
                done.add((r["coin"], r["horizon"], r["seed"]))
    return done


def main() -> None:
    parser = argparse.ArgumentParser(
        description="M4 DLinear-vol vs HAR on ETF daily range-vol (§C conjunction)")
    parser.add_argument("--symbols", nargs="+", default=["SPY", "TLT", "GLD"])
    parser.add_argument("--horizons", type=int, nargs="+", default=[1, 5, 10])
    parser.add_argument("--seeds", type=int, nargs="+", default=[0, 1, 7, 42])
    parser.add_argument("--seq-len", type=int, default=22)
    parser.add_argument("--n-splits", type=int, default=5)
    parser.add_argument("--refit-every", type=int, default=110)
    parser.add_argument("--epochs", type=int, default=100)
    parser.add_argument("--loss-fn", choices=["mse", "mae", "linear"], default="mse",
                        help="mse/mae = precision leg (§C conjunction); linear = bias control")
    parser.add_argument("--out-json", default="results/m4_dlinear_vol_etf_sc_mse/results.json")
    args = parser.parse_args()

    device = "cuda" if torch.cuda.is_available() else "cpu"
    # Honesty note: walk_forward_dlinear / train_dlinear contain no .to(device)
    # -- the M4 harness trains on CPU by construction (DLinear = 22 params).
    # This script is CPU-bound; it never touches the vLLM GPUs. The GPU-2
    # sibling of this terrain is m15_etf_vol.py (LSTM harness does use cuda).
    print(f"[env] torch={torch.__version__} cuda_available={device == 'cuda'} "
          f"(DLinear harness trains on CPU by construction)")

    out_path = Path(args.out_json)
    out_dir = out_path.parent
    out_dir.mkdir(parents=True, exist_ok=True)
    ckpt_path = out_dir / "checkpoint.jsonl"
    print(f"[out] {out_path}")

    t0 = time.time()
    all_rows: list[dict] = []

    # Resume: reload completed combos and skip them (crash/OOM-safe restart).
    done = _done_combos(ckpt_path)
    if done:
        print(f"[resume] {len(done)} completed combos will be skipped")
        with open(ckpt_path, encoding="utf-8") as fh:
            for line in fh:
                try:
                    all_rows.append(json.loads(line))
                except json.JSONDecodeError:
                    continue

    def on_row(row: dict) -> None:
        with open(ckpt_path, "a", encoding="utf-8") as fh:
            fh.write(json.dumps(row) + "\n")

    for symbol in args.symbols:
        csv = PANIER_DIR / f"{symbol}_daily.csv"
        if not csv.exists():
            print(f"[WARN] {csv} missing, symbol skipped")
            continue
        df = pd.read_csv(csv)
        rv = garman_klass_rv(df)
        if len(rv) < 300:
            print(f"[WARN] {symbol}: only {len(rv)} RV days, skipped")
            continue
        rows = eval_one_symbol(
            symbol, rv, args.horizons, args.seeds,
            args.seq_len, args.n_splits, args.refit_every, args.epochs,
            args.loss_fn, on_row=on_row, done=done,
        )
        all_rows.extend(rows)

    summary = aggregate_verdicts(all_rows)
    runtime = time.time() - t0

    payload = {
        "model": "M4 DLinear-vol (ETF extension)",
        "question": "does the BTC log-RV §C edge transfer to anti-bias ETFs?",
        "rv_estimator": "Garman-Klass (1980) daily OHLC range",
        "compute": "CPU (walk_forward_dlinear has no device movement by construction)",
        "reference": "Zeng et al. AAAI 2023 DLinear; HAR baseline Corsi 2009",
        "terrain_commun": {
            "symbols": args.symbols,
            "horizons": args.horizons,
            "seeds": args.seeds,
            "n_splits": args.n_splits,
            "refit_every": args.refit_every,
            "seq_len": args.seq_len,
            "epochs": args.epochs,
            "loss_fn": args.loss_fn,
        },
        "device": "cpu (DLinear harness, by construction)",
        "n_combos": len(all_rows),
        "runtime_s": runtime,
        "summary": summary,
        "combos": all_rows,
    }
    with open(out_path, "w", encoding="utf-8") as fh:
        json.dump(payload, fh, indent=2, default=str)

    print(f"\n{'='*72}\n§C SUMMARY ({args.loss_fn} leg) — {len(summary)} cells")
    print(f"{'sym':8} {'h':>3} {'edge%':>8} {'sig%':>6} {'dm_p_med':>10} "
          f"{'bias_DL':>9} {'bias_HAR':>9} {'persistence':>11} verdict_sc")
    bias_by_key = {}
    for r in all_rows:
        if "dlinear_mse_logrv" in r and not np.isnan(r.get("dlinear_mse_logrv", np.nan)):
            bias_by_key.setdefault((r["coin"], r["horizon"]), []).append(r)
    for s in summary:
        rows_ = bias_by_key.get((s["coin"], s["horizon"]), [])
        b_dl = np.nanmean([r["dlinear_bias_oos"] for r in rows_]) if rows_ else float("nan")
        b_har = np.nanmean([r["har_bias_oos"] for r in rows_]) if rows_ else float("nan")
        pers = rows_[0]["persistence_mse_logrv"] if rows_ else float("nan")
        print(f"{s['coin']:8} {s['horizon']:>3} {s['mean_reduction_pct']:>+8.1f} "
              f"{s['edge_std_pct']:>6.2f} {s['dm_p_median']:>10.2e} "
              f"{b_dl:>+9.4f} {b_har:>+9.4f} {pers:>11.4f} {s['verdict_sc']}")
    print(f"{'='*72}\n[done] runtime {runtime:.0f}s -> {out_path}")


if __name__ == "__main__":
    main()
