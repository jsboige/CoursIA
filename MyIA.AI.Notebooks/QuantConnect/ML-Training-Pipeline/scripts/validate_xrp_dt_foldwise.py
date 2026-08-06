"""Fold-wise deployment protocol for the Decision Transformer on XRP (Epic #1454).

This is the protocol script the holdout OOS (``validate_xrp_dt_holdout.py``,
PR #9653) opened: the walk-forward BEATS@10bps did NOT survive model freezing
(internal holdout = NO-BEATS, DT net -1.865 vs BH -0.592, 0/5 seeds). The edge
comes from *re-training fold-wise* — so the operational question is no longer
"does the model beat buy-and-hold?" but "**how often must we re-train, and at
what window setting, before the freshly-retrained edge decays to zero?****

Three questions, answered by one sweep over monthly/quarterly train anchors:

  (1) **Cadence** (monthly vs quarterly): does the freshly-retrained edge hold
      for one quarter of out-of-sample, or does it decay inside the quarter?
  (2) **Sliding vs expanding window**: a fixed-width rolling train window
      (drop old data as the anchor advances) vs an expanding window (keep all
      history). Which preserves the edge better?
  (3) **Decay curve + retraining cost**: edge of a *fresh* model (re-trained at
      the anchor) vs an *aged* model (trained K months before the anchor, NOT
      re-trained) — the slope of edge-vs-age tells you the re-training cadence
      the strategy actually needs; the GPU-seconds/anchor tells you what it
      costs.

Building block. This script does NOT re-implement training: it loops the
existing ``run_one_seed_holdout`` (train <= train_end, eval on a forward
holdout, train-only normalisation, anti-leakage gap, net Sharpe post-TC, DM
HAC test, >=4 seeds). What changes fold-to-fold is *which* data window is
handed to ``run_one_seed_holdout`` (the ``raw`` frame) and the ``train_end`` /
``holdout_start`` pair — never the training internals.

Toy-scale on a laptop 3070 (8 GB). A single model (1 seed, 30 epochs) is
~70 s on this GPU; the full sweep is sized so a worker can run it inside a
session:

    - anchors : quarterly (8 anchors, 2024-Q3 .. 2026-Q2)
    - seeds   : 0/1/7/42/99 (shared with ai-01 for GPU-2 replication)
    - windows : sliding (fixed 3-year rolling) + expanding (all history)
    - modes   : fresh (re-train at each anchor) + aged-1q (train one quarter
                before the anchor, do NOT re-train, eval at the anchor)

Output: ``results/xrp_dt_validation/foldwise_<timestamp>.json`` plus a printed
human-readable summary table (fresh vs aged, sliding vs expanding, decay
slope, retraining cost).

Usage
-----
    # toy-scale full sweep (GPU 0, ~45-60 min on a 3070)
    CUDA_VISIBLE_DEVICES=0 python scripts/validate_xrp_dt_foldwise.py

    # smoke (CPU synthetic, 2 anchors x 2 seeds x 2 epochs)
    python scripts/validate_xrp_dt_foldwise.py --smoke

Guardrails: train-only normalisation (anti-leakage), >=4 seeds, edge >= 2
sigma cross-seed else INCONCLUSIVE, DM HAC Newey-West. No "promising".
"""

from __future__ import annotations

import argparse
import json
import time
from datetime import datetime, timedelta
from pathlib import Path

import numpy as np
import pandas as pd
import torch

from validate_xrp_dt import COIN, CRYPTO_DIR, RESULTS_DIR, COMMISSION_BPS
from validate_xrp_dt_holdout import run_one_seed_holdout
from data_utils import compute_data_hash, load_data


# Quarterly anchors covering the post-walk-forward data. The walk-forward run
# of 2026-07-21 used folds up to ~2026-04, so anchors here run 2024-Q3 ->
# 2026-Q2: each anchor's forward holdout (next quarter) is data the frozen
# internal holdout already touched, but the *decay* signal (fresh vs aged) is
# what we are measuring, not a contamination-free BEATS claim.
QUARTERLY_ANCHORS = [
    "2024-06-30", "2024-09-30", "2024-12-31",
    "2025-03-31", "2025-06-30", "2025-09-30",
    "2025-12-31", "2026-03-31",
]
# Forward holdout window per anchor = the quarter AFTER the anchor (3 months),
# so the eval window moves with the anchor. ~63 trading days per quarter.
HOLDOUT_DAYS = 90
GAP_DAYS = 10              # anti-leakage gap (matches holdout script default)
SLIDING_WINDOW_YEARS = 3   # fixed-width rolling train window


def _quarter_after(anchor: str) -> str:
    """holdout_start = anchor + GAP_DAYS (anti-leakage), holdout_end = +quarter."""
    start = pd.Timestamp(anchor) + timedelta(days=GAP_DAYS)
    end = start + timedelta(days=HOLDOUT_DAYS)
    return str(start.date()), str(end.date())


def _frame_for_window(raw: pd.DataFrame, anchor: str, window: str) -> pd.DataFrame:
    """Slice ``raw`` to the train window requested, ending at the anchor.

    ``expanding`` keeps the full history (truncated at the anchor + its forward
    holdout, so the FeatureEngineer backward-only indicators still compute).
    ``sliding`` keeps only the trailing ``SLIDING_WINDOW_YEARS`` years before
    the anchor, plus the forward holdout needed to eval the anchor's quarter.
    """
    anchor_ts = pd.Timestamp(anchor)
    holdout_start, holdout_end = _quarter_after(anchor)
    end_ts = pd.Timestamp(holdout_end)
    if window == "expanding":
        return raw.loc[:end_ts]
    # sliding: drop data older than (anchor - N years) but keep the holdout tail.
    keep_from = anchor_ts - pd.DateOffset(years=SLIDING_WINDOW_YEARS)
    # Keep a little lead so backward indicators at `keep_from` are warm.
    keep_from -= timedelta(days=HOLDOUT_DAYS)
    return raw.loc[(raw.index >= keep_from) & (raw.index <= end_ts)]


def _run_mode(raw: pd.DataFrame, anchors, seeds, mode: str, window: str,
              epochs: int, window_len: int, context_length: int, batch_size: int,
              lr: float, d_model: int, nhead: int, num_layers: int, device: str,
              commission_bps: int) -> dict:
    """Run one (mode, window) combination across all anchors x seeds.

    ``mode``:
      - ``fresh``  : re-train at every anchor (train_end = anchor).
      - ``aged-1q``: train one quarter BEFORE the anchor, do NOT re-train,
                     eval on the anchor's forward quarter. This is the
                     "deployed then left alone" scenario: the decay curve's
                     first data point.
    """
    results = []
    for anchor in anchors:
        holdout_start, holdout_end = _quarter_after(anchor)
        frame = _frame_for_window(raw, anchor, window)
        if mode == "aged-1q":
            # Train one quarter earlier; eval still on the anchor's forward q.
            train_end = str((pd.Timestamp(anchor)
                             - pd.DateOffset(months=3)).date())
        else:  # fresh
            train_end = anchor
        # Guard: the frame must cover train_end and the full forward holdout.
        # An anchor whose 90d holdout runs past the end of the data would make
        # run_one_seed_holdout raise "holdout trop court"; skip it cleanly.
        if frame.index.max() < pd.Timestamp(holdout_end):
            print(f"  [{mode}/{window}] skip {anchor}: holdout_end {holdout_end} "
                  f"past frame end ({frame.index.max().date()})")
            continue
        if frame.index.min() > pd.Timestamp(train_end):
            print(f"  [{mode}/{window}] skip {anchor}: train_end {train_end} "
                  f"before frame start ({frame.index.min().date()})")
            continue

        anchor_seed_sharpes = []
        for seed in seeds:
            t0 = time.time()
            r = run_one_seed_holdout(
                seed, frame, train_end, holdout_start, holdout_end,
                epochs=epochs, window=window_len, context_length=context_length,
                batch_size=batch_size, lr=lr, d_model=d_model, nhead=nhead,
                num_layers=num_layers, device=device, commission_bps=commission_bps,
            )
            r["train_end"] = train_end
            r["window"] = window
            r["mode"] = mode
            r["elapsed_s"] = round(time.time() - t0, 1)
            results.append(r)
            anchor_seed_sharpes.append(r["dt_net_sharpe"])
        if anchor_seed_sharpes:
            arr = np.array(anchor_seed_sharpes)
            print(f"  [{mode}/{window}] {anchor}: DT net {arr.mean():+.3f} "
                  f"(+/- {arr.std(ddof=1):.3f}) n={len(arr)} | "
                  f"retrain~{np.mean([x['elapsed_s'] for x in results[-len(arr):]]):.0f}s/seed",
                  flush=True)
    return {"mode": mode, "window": window, "per_seed": results}


def _summary_row(per_seed: list, label: str) -> dict:
    """Aggregate cross-seed metrics for one (mode, window) bucket."""
    if not per_seed:
        return {"label": label, "n": 0}
    nets = np.array([r["dt_net_sharpe"] for r in per_seed])
    bhs = np.array([r["bh_sharpe"] for r in per_seed])
    edge = nets - bhs
    # DM p-values where present
    dm_ps = [r["dm_dt_vs_bh"]["p_value"] for r in per_seed
             if r.get("dm_dt_vs_bh") and "p_value" in r["dm_dt_vs_bh"]]
    return {
        "label": label,
        "n_models": len(per_seed),
        "dt_net_sharpe_mean": round(float(nets.mean()), 4),
        "dt_net_sharpe_std": round(float(nets.std(ddof=1)), 4) if len(nets) > 1 else None,
        "bh_sharpe_mean": round(float(bhs.mean()), 4),
        "edge_mean_pp": round(float(edge.mean()) * 100, 2),
        "edge_sigma": round(float(edge.mean() / (edge.std(ddof=1) + 1e-12)), 2)
                      if len(edge) > 1 else None,
        "dm_p_median": float(np.median(dm_ps)) if dm_ps else None,
        "mean_retrain_s": round(float(np.mean([r["elapsed_s"] for r in per_seed])), 1),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--smoke", action="store_true",
                        help="CPU synthetic sanity (2 anchors x 2 seeds x 2 epochs)")
    parser.add_argument("--anchors", nargs="+", default=None,
                        help="train_end anchors (default: quarterly set)")
    parser.add_argument("--seeds", nargs="+", type=int, default=[0, 1, 7, 42, 99])
    parser.add_argument("--epochs", type=int, default=30)
    parser.add_argument("--d-model", type=int, default=128)
    parser.add_argument("--nhead", type=int, default=4)
    parser.add_argument("--num-layers", type=int, default=3)
    parser.add_argument("--context-length", type=int, default=20)
    parser.add_argument("--window", type=int, default=20)
    parser.add_argument("--batch-size", type=int, default=32)
    parser.add_argument("--lr", type=float, default=1e-4)
    parser.add_argument("--device", default=None)
    parser.add_argument("--commission-bps", type=int, default=COMMISSION_BPS)
    parser.add_argument("--modes", nargs="+",
                        default=["fresh", "aged-1q"],
                        choices=["fresh", "aged-1q"],
                        help="Which deployment scenarios to sweep")
    parser.add_argument("--windows", nargs="+",
                        default=["sliding", "expanding"],
                        choices=["sliding", "expanding"],
                        help="Train window strategy")
    args = parser.parse_args()

    if args.smoke:
        args.seeds = args.seeds[:2]
        args.epochs = 2
        device = "cpu"
    else:
        args.anchors = args.anchors or QUARTERLY_ANCHORS
        device = args.device or ("cuda" if torch.cuda.is_available() else "cpu")

    if args.smoke:
        from data_utils import generate_synthetic_data
        raw = generate_synthetic_data(1500)
        if not isinstance(raw.index, pd.DatetimeIndex):
            raw.index = pd.date_range("2018-01-01", periods=len(raw), freq="D")
        data_hash = "synthetic-smoke"
        # Derive smoke anchors from the synthetic frame so frame slicing stays
        # in-range (the default quarterly anchors point at real 2024-2026 dates,
        # which are outside synthetic data).
        last = raw.index.max()
        args.anchors = [
            str((last - pd.DateOffset(months=6)).date()),
            str((last - pd.DateOffset(months=3)).date()),
        ]
    else:
        raw = load_data(CRYPTO_DIR, COIN)
        data_hash = compute_data_hash(raw)

    out_dir = RESULTS_DIR
    out_dir.mkdir(parents=True, exist_ok=True)
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")

    print(f"=== XRP DT fold-wise deployment protocol (#1454) ===")
    print(f"Date: {datetime.now().isoformat()} | device: {device} | smoke: {args.smoke}")
    print(f"Data: {len(raw)} rows [{raw.index.min().date()} .. {raw.index.max().date()}] "
          f"hash={data_hash[:12]}")
    print(f"Anchors ({len(args.anchors)}): {args.anchors}")
    print(f"Modes: {args.modes} | Windows: {args.windows}")
    print(f"TC: {args.commission_bps} bps | seeds: {args.seeds} | epochs: {args.epochs}")
    print(f"Forward holdout/anchor: {HOLDOUT_DAYS}d (+{GAP_DAYS}d gap) | "
          f"sliding window: {SLIDING_WINDOW_YEARS}y")
    print()

    sweep = {}
    t_sweep_start = time.time()
    for window in args.windows:
        for mode in args.modes:
            key = f"{mode}/{window}"
            print(f"--- {key} ---", flush=True)
            sweep[key] = _run_mode(
                raw, args.anchors, args.seeds, mode, window,
                epochs=args.epochs, window_len=args.window,
                context_length=args.context_length, batch_size=args.batch_size,
                lr=args.lr, d_model=args.d_model, nhead=args.nhead,
                num_layers=args.num_layers, device=device,
                commission_bps=args.commission_bps,
            )
    sweep_elapsed = time.time() - t_sweep_start

    # Aggregate per (mode, window) bucket.
    summary_rows = []
    for key, bucket in sweep.items():
        summary_rows.append(_summary_row(bucket["per_seed"], key))

    # Decay signal: fresh vs aged-1q, for each window (the cadence answer).
    decay = {}
    for window in args.windows:
        if "fresh" in args.modes and "aged-1q" in args.modes:
            f = _summary_row(sweep[f"fresh/{window}"]["per_seed"], f"fresh/{window}")
            a = _summary_row(sweep[f"aged-1q/{window}"]["per_seed"], f"aged-1q/{window}")
            if f.get("n_models") and a.get("n_models"):
                decay[window] = {
                    "fresh_edge_pp": f["edge_mean_pp"],
                    "aged1q_edge_pp": a["edge_mean_pp"],
                    "decay_pp_per_quarter": round(f["edge_mean_pp"] - a["edge_mean_pp"], 2),
                }

    summary = {
        "timestamp": ts, "coin": COIN, "device": device, "smoke": args.smoke,
        "data_hash": data_hash,
        "config": {
            "anchors": args.anchors, "seeds": args.seeds, "epochs": args.epochs,
            "modes": args.modes, "windows": args.windows,
            "holdout_days": HOLDOUT_DAYS, "gap_days": GAP_DAYS,
            "sliding_window_years": SLIDING_WINDOW_YEARS,
            "commission_bps": args.commission_bps,
            "d_model": args.d_model, "window": args.window,
            "context_length": args.context_length,
        },
        "sweep_elapsed_s": round(sweep_elapsed, 1),
        "summary_by_bucket": summary_rows,
        "decay_fresh_vs_aged1q": decay,
        "sweep": sweep,
    }
    out_path = out_dir / f"foldwise_{ts}.json"
    out_path.write_text(json.dumps(summary, indent=2), encoding="utf-8")

    print()
    print("=" * 78)
    print("FOLD-WISE DEPLOYMENT PROTOCOL — summary")
    print("=" * 78)
    print(f"{'mode/window':<22}{'n':>4}{'DTnet':>9}{'BH':>8}{'edge_pp':>9}"
          f"{'edge_sig':>9}{'DMp':>7}{'retrain_s':>10}")
    print("-" * 78)
    for r in summary_rows:
        if not r.get("n_models"):
            print(f"{r['label']:<22}{'-':>4}  (no models)")
            continue
        print(f"{r['label']:<22}{r['n_models']:>4}{r['dt_net_sharpe_mean']:>9.3f}"
              f"{r['bh_sharpe_mean']:>8.3f}{r['edge_mean_pp']:>9.2f}"
              f"{str(r['edge_sigma']):>9}{str(r['dm_p_median']):>7}"
              f"{r['mean_retrain_s']:>10.0f}")
    if decay:
        print("-" * 78)
        print("DECAY (fresh retrain vs aged-1q frozen): edge lost per quarter frozen")
        for w, d in decay.items():
            print(f"  {w:<12} fresh {d['fresh_edge_pp']:+.2f}pp -> aged-1q "
                  f"{d['aged1q_edge_pp']:+.2f}pp  |  "
                  f"decay = {d['decay_pp_per_quarter']:+.2f} pp/quarter")
    print("-" * 78)
    print(f"sweep elapsed: {sweep_elapsed/60:.1f} min | -> {out_path}")
    print()
    print("Interpretation key:")
    print("  * edge_mean_pp > 0 with edge_sigma >= 2 and DMp < 0.05 => the mode")
    print("    holds out-of-sample; the cadence is defensible.")
    print("  * decay_pp_per_quarter is the COST of NOT re-training: if it is large")
    print("    and positive, quarterly (or finer) re-training is required; if it is")
    print("    ~0, a frozen model is fine and re-training cost is wasted.")
    print("  * This sweep does NOT claim BEATS/NO-BEATS on unseen data (the frozen")
    print("    internal holdout already answered that = NO-BEATS). It quantifies")
    print("    the decay + cost of the fold-wise re-training the edge depends on.")


if __name__ == "__main__":
    main()
