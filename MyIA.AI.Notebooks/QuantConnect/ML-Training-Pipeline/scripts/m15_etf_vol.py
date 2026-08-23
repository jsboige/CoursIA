"""M15 LSTM-vol on ETF daily range-vol -- GPU-2 sibling of etf_vol.py.

Companion of etf_vol.py (M4 DLinear-vol ETF extension): SAME terrain commun
(SPY/TLT/GLD Garman-Klass daily RV, walk-forward 5-fold, refit_every=110,
seeds {0,1,7,42}, horizons {1,5,10}, HAR baseline, persistence baseline,
§C conjunction on the mse precision leg), but the model is the M15 Log-LSTM
(h=64, 1 layer, window=22, early stopping patience 10 -- the exact §C entry
configuration of REGISTRY 2026-08-15 issue #11043: 2/3 BEATS on BTC) instead
of DLinear. The two runs together answer: does EITHER of the two §C-validated
vol models transfer from BTC hourly RV to ETF daily range-vol?

Unlike dlinear_vol (pure CPU by construction -- zero .to(device) calls), the
M15 harness trains on GPU (walk_forward_lstm moves model/tensors to cuda):
this is the GPU-2 grain of the pair. VRAM: ~18K params, batch 32 x seq 22 --
well under 1 GB.

Features: [log_RV_GK, daily log-return, sign(daily log-return)] -- the M15
feature triple (prepare_features in m15_lstm_rv builds the same on hourly
crypto data; here daily returns come directly from Close).

Note on edge sign: m15_lstm_rv.py's mse_reduction_pct is (mse_model -
mse_har)/mse_har (negative = model wins). This script reports edge_pct =
(mse_har - mse_model)/mse_har (positive = model wins) to keep the SAME table
semantics as etf_vol.py / the M4 §C registry entries.

Run
---
CUDA_VISIBLE_DEVICES=2 python -u m15_etf_vol.py --seeds 0 1 7 42 \
    --horizons 1 5 10 --loss-fn mse \
    --out-json results/m15_lstm_rv_etf_sc_mse/results.json
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

from dm_test import dm_verdict                       # noqa: E402
from etf_vol import (                                # noqa: E402
    PANIER_DIR,
    garman_klass_rv,
    persistence_mse,
)
from gpu_training import thermal_check               # noqa: E402
from har_model import walk_forward_har               # noqa: E402
from m15_lstm_rv import walk_forward_lstm            # noqa: E402
from realized_variance import realized_variance_to_log  # noqa: E402


def prepare_etf_features(df: pd.DataFrame) -> tuple[pd.DataFrame, pd.Series]:
    """[log_RV_GK, daily log-return, sign] on the GK-RV index (M15 triple)."""
    rv = garman_klass_rv(df)
    log_rv = realized_variance_to_log(rv)

    px = df.copy()
    px["Date"] = pd.to_datetime(px["Date"])
    px = px.set_index("Date").sort_index()
    daily_ret = np.log(px["Close"] / px["Close"].shift(1)).rename("returns")
    sign_ret = np.sign(daily_ret).rename("sign_returns")

    features = pd.concat([log_rv.rename("log_rv"), daily_ret, sign_ret],
                         axis=1, sort=False).dropna()
    rv = rv.reindex(features.index)
    return features, rv


def eval_one_symbol(
    symbol: str,
    features: pd.DataFrame,
    rv: pd.Series,
    horizons: list[int],
    seeds: list[int],
    n_splits: int,
    refit_every: int,
    window: int,
    hidden_size: int,
    loss_fn: str,
    on_row=None,
    done: set[tuple] | None = None,
) -> list[dict]:
    log_rv = realized_variance_to_log(rv)
    log_rv_arr = log_rv.values.astype(float)

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
            print(f"  h={h} HAR MSE(agrege)={har_mse:.5f} bias_OOS={har_bias_oos:+.5f} "
                  f"({har_out['n_total_preds']} preds)")
        except Exception as exc:
            print(f"  h={h} HAR baseline FAILED: {exc}")
            continue

        for seed in seeds:
            if done is not None and (symbol, h, seed) in done:
                print(f"  h={h} seed={seed} already done, skipping")
                continue
            thermal_check(80, 30, verbose=True)
            try:
                lstm_out = walk_forward_lstm(
                    features, rv, horizon=h, n_splits=n_splits,
                    refit_every=refit_every, window=window,
                    hidden_size=hidden_size, seed=seed,
                )
            except Exception as exc:
                print(f"  h={h} seed={seed} LSTM FAILED: {exc}")
                row = {"coin": symbol, "horizon": h, "seed": seed,
                       "lstm_mse_logrv": float("nan"),
                       "har_mse_logrv": float(har_mse),
                       "dm_verdict": "FAILED"}
                rows.append(row)
                if on_row:
                    on_row(row)
                continue

            lstm_mse = lstm_out["aggregate_mse_logrv"]
            lstm_fc = lstm_out["forecasts"]
            lstm_tgt = lstm_out["targets"]
            lstm_errors = (lstm_fc - lstm_tgt).dropna().values
            lstm_bias_oos = float(np.mean(lstm_errors)) if len(lstm_errors) else float("nan")

            # Align on the common forecast dates (LSTM and HAR walk-forwards
            # share the split scheme but may differ at the edges).
            common = lstm_fc.index.intersection(har_out["forecasts"].index)
            tgt = lstm_tgt.reindex(common).dropna()
            lstm_err = (lstm_fc.reindex(tgt.index) - tgt).values.astype(float)
            har_err = (har_out["forecasts"].reindex(tgt.index) - tgt).values.astype(float)
            # Le verdict (DM et edge_pct) porte sur l'echantillon ALIGNE, pas sur
            # l'agregat HAR : c'est cette valeur qu'il faut imprimer (#12681).
            mse_har_aligned = float(np.mean(har_err ** 2)) if len(har_err) else float("nan")

            dm_info = {}
            if len(lstm_err) >= 10 and np.all(np.isfinite(lstm_err)) and np.all(np.isfinite(har_err)):
                try:
                    dm = dm_verdict(lstm_err, har_err, horizon=h, loss_fn=loss_fn)
                    dm_info = {
                        "dm_stat": dm["dm_statistic"],
                        "dm_pvalue": dm["p_value"],
                        "dm_verdict": dm["verdict"],
                        "dm_mean_loss_diff": dm["mean_loss_diff"],
                    }
                    print(f"  h={h} seed={seed} LSTM MSE={lstm_mse:.5f} "
                          f"vs HAR aligne {mse_har_aligned:.5f} "
                          f"bias={lstm_bias_oos:+.5f} DM={dm['dm_statistic']:.3f} "
                          f"p={dm['p_value']:.4f} -> {dm['verdict']}")
                except Exception as exc:
                    print(f"  h={h} seed={seed} DM FAILED: {exc}")
                    dm_info = {"dm_verdict": "DM_FAILED"}
            else:
                dm_info = {"dm_verdict": "INSUFFICIENT_DATA"}

            row = {
                "coin": symbol, "horizon": h, "seed": seed,
                "window": window, "hidden_size": hidden_size,
                "refit_every": refit_every,
                "persistence_mse_logrv": pers[h],
                "har_bias_oos": har_bias_oos,
                "lstm_bias_oos": lstm_bias_oos,
                "n_rv_days": int(len(rv)),
                "n_predictions": int(lstm_out["n_total_preds"]),
                "lstm_mse_logrv": float(lstm_mse),
                "har_mse_logrv": float(har_mse),
                "har_mse_aligned": mse_har_aligned,
                # positive = LSTM wins (same semantics as M4 §C entries)
                "edge_pct": (float((mse_har_aligned - lstm_mse) / mse_har_aligned * 100)
                             if mse_har_aligned and mse_har_aligned > 0 else float("nan")),
                **dm_info,
            }
            rows.append(row)
            if on_row:
                on_row(row)
    return rows


def aggregate(rows: list[dict]) -> list[dict]:
    """§C conjunction per (symbol, horizon): edge >= 2 sigma AND dm_p_median < 0.05."""
    from collections import defaultdict

    grouped: dict[tuple, list[dict]] = defaultdict(list)
    for r in rows:
        if "lstm_mse_logrv" not in r or np.isnan(r.get("lstm_mse_logrv", np.nan)):
            continue
        grouped[(r["coin"], r["horizon"])].append(r)

    out = []
    for (sym, h), rs in sorted(grouped.items()):
        n = len(rs)
        edges = [r["edge_pct"] for r in rs]
        mean_edge = float(np.nanmean(edges))
        std_edge = float(np.nanstd(edges)) if n > 1 else 0.0
        p_vals = [r.get("dm_pvalue", 1.0) for r in rs]
        dm_p_median = float(np.nanmedian(p_vals))
        n_beaten = sum(1 for r in rs if "BEATEN" in str(r.get("dm_verdict", "")))
        sigma_leg = n >= 4 and mean_edge > 0 and (std_edge < 1e-10 or mean_edge >= 2 * std_edge)
        dm_leg = dm_p_median < 0.05
        if n_beaten > 0:
            verdict = "NO BEATS"
        elif sigma_leg and dm_leg:
            verdict = "BEATS"
        else:
            verdict = "INCONCLUSIVE"
        out.append({
            "coin": sym, "horizon": h, "n_seeds": n,
            "mean_edge_pct": mean_edge, "std_edge_pct": std_edge,
            "dm_p_median": dm_p_median,
            "sigma_leg": sigma_leg, "dm_leg": dm_leg,
            "n_beaten": n_beaten, "verdict_sc": verdict,
        })
    return out


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
            mse = r.get("lstm_mse_logrv", float("nan"))
            if not np.isnan(mse):
                done.add((r["coin"], r["horizon"], r["seed"]))
    return done


def main() -> None:
    parser = argparse.ArgumentParser(
        description="M15 LSTM-vol vs HAR on ETF daily range-vol (§C conjunction)")
    parser.add_argument("--symbols", nargs="+", default=["SPY", "TLT", "GLD"])
    parser.add_argument("--horizons", type=int, nargs="+", default=[1, 5, 10])
    parser.add_argument("--seeds", type=int, nargs="+", default=[0, 1, 7, 42])
    parser.add_argument("--n-splits", type=int, default=5)
    parser.add_argument("--refit-every", type=int, default=110)
    parser.add_argument("--window", type=int, default=22)
    parser.add_argument("--hidden-size", type=int, default=64)
    parser.add_argument("--loss-fn", choices=["mse", "mae", "linear"], default="mse",
                        help="mse/mae = precision leg (§C conjunction); linear = bias control")
    parser.add_argument("--out-json", default="results/m15_lstm_rv_etf_sc_mse/results.json")
    parser.add_argument("--mem-frac", type=float, default=0.0,
                        help="Cap torch allocator at this fraction of GPU VRAM "
                             "(0 = no cap). The M15 harness's varying-shape refit "
                             "loop wastes ~14 GB on allocator growth for a <1 GB "
                             "working set; a cap forces compaction so 2 workers "
                             "fit on a 24 GB card.")
    args = parser.parse_args()

    if args.mem_frac > 0 and torch.cuda.is_available():
        torch.cuda.set_per_process_memory_fraction(args.mem_frac)
        total_gb = torch.cuda.get_device_properties(0).total_memory / 2**30
        print(f"[env] VRAM capped at {args.mem_frac:.0%} of {total_gb:.0f} GB "
              f"(~{args.mem_frac * total_gb:.0f} GB)")

    device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
    uses_gpu = device.type == "cuda"
    print(f"[env] torch={torch.__version__} device={device} "
          f"(walk_forward_lstm trains on {'GPU' if uses_gpu else 'CPU -- check CUDA_VISIBLE_DEVICES'})")

    out_path = Path(args.out_json)
    out_dir = out_path.parent
    out_dir.mkdir(parents=True, exist_ok=True)
    ckpt_path = out_dir / "checkpoint.jsonl"
    print(f"[out] {out_path}")

    t0 = time.time()
    all_rows: list[dict] = []

    # Resume: reload completed combos and skip them (OOM/crash-safe restart).
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
        features, rv = prepare_etf_features(pd.read_csv(csv))
        if len(rv) < 300:
            print(f"[WARN] {symbol}: only {len(rv)} RV days, skipped")
            continue
        rows = eval_one_symbol(
            symbol, features, rv, args.horizons, args.seeds,
            args.n_splits, args.refit_every, args.window, args.hidden_size,
            args.loss_fn, on_row=on_row, done=done,
        )
        all_rows.extend(rows)
        all_rows = [r for r in all_rows if "skipped" not in r]

    summary = aggregate(all_rows)
    runtime = time.time() - t0

    payload = {
        "model": "M15 Log-LSTM vol (ETF extension, h=64 §C config)",
        "question": "does the M15 BTC log-RV §C edge transfer to anti-bias ETFs?",
        "rv_estimator": "Garman-Klass (1980) daily OHLC range",
        "reference": "Hochreiter & Schmidhuber 1997; HAR baseline Corsi 2009",
        "terrain_commun": {
            "symbols": args.symbols, "horizons": args.horizons, "seeds": args.seeds,
            "n_splits": args.n_splits, "refit_every": args.refit_every,
            "window": args.window, "hidden_size": args.hidden_size,
            "loss_fn": args.loss_fn,
        },
        "device": str(device),
        "n_combos": len(all_rows),
        "runtime_s": runtime,
        "summary": summary,
        "combos": all_rows,
    }
    with open(out_path, "w", encoding="utf-8") as fh:
        json.dump(payload, fh, indent=2, default=str)

    print(f"\n{'='*72}\n§C SUMMARY ({args.loss_fn} leg) — {len(summary)} cells")
    print(f"{'sym':8} {'h':>3} {'edge%':>8} {'sig%':>6} {'dm_p_med':>10} "
          f"{'sig_leg':>7} {'dm_leg':>7} {'bias_LSTM':>9} {'bias_HAR':>9} verdict_sc")
    for s in summary:
        rs = [r for r in all_rows if r["coin"] == s["coin"] and r["horizon"] == s["horizon"]]
        b_m = np.nanmean([r["lstm_bias_oos"] for r in rs]) if rs else float("nan")
        b_h = np.nanmean([r["har_bias_oos"] for r in rs]) if rs else float("nan")
        print(f"{s['coin']:8} {s['horizon']:>3} {s['mean_edge_pct']:>+8.1f} "
              f"{s['std_edge_pct']:>6.2f} {s['dm_p_median']:>10.2e} "
              f"{str(s['sigma_leg']):>7} {str(s['dm_leg']):>7} "
              f"{b_m:>+9.4f} {b_h:>+9.4f} {s['verdict_sc']}")
    print(f"{'='*72}\n[done] runtime {runtime:.0f}s -> {out_path}")


if __name__ == "__main__":
    main()
