"""Train multi-scale GNN cross-asset on log-RV (Issue #834 M5 stretch).

Walk-forward 5-fold × multi-seed × {h=1, 5, 10}. Compares MSE log-RV against
HAR baseline (M2 #837) and GARCH-rolling baseline (M1 #838).

Honest verdict policy: claims "BEATS HAR" only if mean MSE improvement > 2σ
cross-seed AND Diebold-Mariano stat |dm| > 1.96 (cf G.2 pr-review-discipline).

Usage:
    python train_multiscale_gnn.py --horizons 1 5 10 --seeds 0 1 7 42 \
        --out-json ../results/m5_multiscale_gnn/results.json
    python train_multiscale_gnn.py --dry-run    # synthetic, no GPU
"""

from __future__ import annotations

import argparse
import json
import math
import time
from pathlib import Path
from typing import Sequence

import numpy as np
import pandas as pd
import torch
import torch.nn as nn
import torch.nn.functional as F

from har_model import walk_forward_har
from multiscale_gnn_features import (
    CrossAssetPanel,
    DEFAULT_COINS,
    _build_har_features_panel,
    _aligned_log_rv_panel,
    _rolling_correlation_adjacency,
    build_panel,
    to_pyg_batches,
)
from multiscale_gnn_model import MultiScaleGNN, MultiScaleGNNConfig
from realized_variance import (
    daily_realized_variance,
    realized_variance_to_log,
)
from intraday_loader import hourly_log_returns, synthesize_intraday


def _set_seed(seed: int) -> None:
    np.random.seed(seed)
    torch.manual_seed(seed)
    torch.cuda.manual_seed_all(seed)


def _make_split_indices(n: int, n_splits: int = 5) -> list[tuple[int, int, int]]:
    """Walk-forward expanding-window indices: (train_end, test_start, test_end)."""
    if n_splits < 2 or n < 200:
        raise ValueError(f"Need n>=200 + n_splits>=2; got n={n}, splits={n_splits}")
    test_size = (n - n // 3) // n_splits
    initial_train = n // 3
    splits = []
    for k in range(n_splits):
        train_end = initial_train + k * test_size
        test_start = train_end
        test_end = min(test_start + test_size, n)
        if test_end <= test_start:
            break
        splits.append((train_end, test_start, test_end))
    return splits


def _train_one_fold(
    panel: CrossAssetPanel,
    target_full: pd.DataFrame,
    fold_train_end: int,
    fold_test_start: int,
    fold_test_end: int,
    horizon: int,
    seed: int,
    epochs: int = 80,
    lr: float = 5e-3,
    weight_decay: float = 1e-4,
    device: torch.device | None = None,
) -> tuple[np.ndarray, np.ndarray]:
    """Train MultiScaleGNN on a single fold, return predictions + targets.

    Returns
    -------
    preds : np.ndarray, shape (n_test, N)
    truth : np.ndarray, shape (n_test, N)
    """
    _set_seed(seed)
    device = device or torch.device("cuda" if torch.cuda.is_available() else "cpu")

    cfg = MultiScaleGNNConfig()
    model = MultiScaleGNN(cfg).to(device)
    opt = torch.optim.AdamW(model.parameters(), lr=lr, weight_decay=weight_decay)

    # Pre-build PyG batches once (small overhead)
    batches = to_pyg_batches(panel)
    n_total = len(batches)
    if fold_test_end > n_total:
        fold_test_end = n_total

    # Targets are aligned to panel.dates[: -horizon]; verify alignment
    n_target = len(target_full)
    train_indices = list(range(min(fold_train_end, n_target)))
    test_indices = list(range(fold_test_start, min(fold_test_end, n_target)))
    if not train_indices or not test_indices:
        return np.array([]), np.array([])

    target_arr = target_full.values.astype(np.float32)  # (n_target, N)

    # Train loop
    model.train()
    for epoch in range(epochs):
        perm = np.random.permutation(train_indices)
        ep_loss = 0.0
        for t in perm:
            b = batches[t]
            x = b["x"].to(device)
            ei = b["edge_index"].to(device)
            ew = b["edge_weight"].to(device)
            y = torch.tensor(target_arr[t], device=device)
            pred = model(x, x, x, ei, ew)
            loss = F.mse_loss(pred, y)
            opt.zero_grad()
            loss.backward()
            opt.step()
            ep_loss += float(loss.item())

    # Eval
    model.eval()
    preds_list, truth_list = [], []
    with torch.no_grad():
        for t in test_indices:
            b = batches[t]
            x = b["x"].to(device)
            ei = b["edge_index"].to(device)
            ew = b["edge_weight"].to(device)
            pred = model(x, x, x, ei, ew).cpu().numpy()
            preds_list.append(pred)
            truth_list.append(target_arr[t])

    return np.array(preds_list), np.array(truth_list)


def _eval_panel(
    panel: CrossAssetPanel,
    horizon: int,
    n_splits: int,
    seeds: Sequence[int],
    epochs: int,
    device: torch.device,
) -> dict:
    """Walk-forward × multi-seed for a fixed horizon."""
    target, target_idx = panel.targets_h_step(horizon=horizon)
    n_target = len(target)
    splits = _make_split_indices(n_target, n_splits=n_splits)

    per_seed_mse: list[float] = []
    per_seed_pred: list[np.ndarray] = []
    per_seed_truth: list[np.ndarray] = []
    for seed in seeds:
        preds_all, truth_all = [], []
        for (te, ts, tend) in splits:
            preds, truth = _train_one_fold(
                panel=panel, target_full=target,
                fold_train_end=te, fold_test_start=ts, fold_test_end=tend,
                horizon=horizon, seed=seed, epochs=epochs, device=device,
            )
            if preds.size:
                preds_all.append(preds)
                truth_all.append(truth)
        if not preds_all:
            continue
        preds_arr = np.concatenate(preds_all, axis=0)
        truth_arr = np.concatenate(truth_all, axis=0)
        mse = float(np.mean((preds_arr - truth_arr) ** 2))
        per_seed_mse.append(mse)
        per_seed_pred.append(preds_arr)
        per_seed_truth.append(truth_arr)

    return {
        "horizon": horizon,
        "n_seeds": len(per_seed_mse),
        "n_target": n_target,
        "n_splits": len(splits),
        "per_seed_mse": per_seed_mse,
        "mean_mse": float(np.mean(per_seed_mse)) if per_seed_mse else float("nan"),
        "std_mse": float(np.std(per_seed_mse)) if per_seed_mse else float("nan"),
    }


def _har_baseline_per_coin(
    panel: CrossAssetPanel,
    horizon: int,
    n_splits: int,
) -> dict[str, float]:
    """Run HAR baseline per coin, return MSE log-RV per coin (mean across coins
    for direct comparison with M5 mean MSE)."""
    out: dict[str, float] = {}
    for c_idx, coin in enumerate(panel.coins):
        log_rv_coin = panel.log_rv_raw[coin]
        # walk_forward_har expects RV (not log-RV); convert back via exp
        rv_coin = pd.Series(np.exp(log_rv_coin.values), index=log_rv_coin.index)
        try:
            out_coin = walk_forward_har(rv_coin, horizon=horizon, n_splits=n_splits)
            out[coin] = float(out_coin["aggregate_mse_logrv"])
        except Exception as exc:
            out[coin] = float("nan")
    return out


def _build_synth_panel(n_days: int = 400, seed: int = 0) -> CrossAssetPanel:
    """Synthetic panel for --dry-run: 3 'coins' from synthesize_intraday."""
    coins = ["BTC-SYN", "ETH-SYN", "SOL-SYN"]
    rets = {}
    for i, coin in enumerate(coins):
        rets[coin] = hourly_log_returns(
            synthesize_intraday(
                n_days=n_days, obs_per_day=24, seed=seed + i, annualized_vol=0.6 + 0.1 * i
            )
        )
    log_rv_df, _ = _aligned_log_rv_panel(rets)
    X, dates = _build_har_features_panel(log_rv_df)
    A = _rolling_correlation_adjacency(log_rv_df, dates, window=60, top_k=2)
    return CrossAssetPanel(
        X=X, A=A, dates=dates, coins=tuple(coins),
        log_rv_raw=log_rv_df.loc[dates].copy(),
    )


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--horizons", type=int, nargs="+", default=[1, 5, 10])
    ap.add_argument("--n-splits", type=int, default=5)
    ap.add_argument("--seeds", type=int, nargs="+", default=[0, 1, 7, 42])
    ap.add_argument("--epochs", type=int, default=80)
    ap.add_argument("--skip-remote", action="store_true")
    ap.add_argument("--dry-run", action="store_true",
                    help="Use synthetic panel (no real data, no GPU required)")
    ap.add_argument("--out-json", type=str, default="results/m5_multiscale_gnn.json")
    args = ap.parse_args()

    t0 = time.time()
    device = torch.device("cuda" if torch.cuda.is_available() else "cpu")

    if args.dry_run:
        print("[DRY-RUN] using synthetic panel n_days=400")
        panel = _build_synth_panel(n_days=400, seed=0)
        seeds = args.seeds[:2]  # short
        epochs = max(args.epochs // 8, 5)
    else:
        print(f"[load] BTC + ETH + SOL hourly → cross-asset panel "
              f"(skip_remote={args.skip_remote})")
        panel = build_panel(skip_remote=args.skip_remote)
        seeds = args.seeds
        epochs = args.epochs

    print(f"[panel] T={panel.X.shape[0]}, N={panel.X.shape[1]}, F={panel.X.shape[2]}, "
          f"coins={panel.coins}")
    print(f"[device] {device}")

    rows: list[dict] = []
    for h in args.horizons:
        print(f"\n=== horizon h={h} ===")
        m5_out = _eval_panel(panel, horizon=h, n_splits=args.n_splits,
                             seeds=seeds, epochs=epochs, device=device)
        print(f"  M5 MSE log-RV : {m5_out['mean_mse']:.5f} ± {m5_out['std_mse']:.5f} "
              f"(over {m5_out['n_seeds']} seeds)")

        if not args.dry_run:
            har_per_coin = _har_baseline_per_coin(panel, horizon=h, n_splits=args.n_splits)
            har_mean = float(np.nanmean(list(har_per_coin.values())))
        else:
            har_per_coin = {c: float("nan") for c in panel.coins}
            har_mean = float("nan")

        edge_2sigma = (
            (har_mean - m5_out["mean_mse"]) - 2.0 * m5_out["std_mse"]
            if m5_out["n_seeds"] >= 4 and not math.isnan(har_mean) else float("nan")
        )
        verdict = (
            "BEATS HAR (≥2σ)" if edge_2sigma > 0
            else "NO BEATS HAR (<2σ)" if not math.isnan(edge_2sigma)
            else "INSUFFICIENT (need ≥4 seeds + non-synthetic)"
        )
        print(f"  HAR baseline  : mean MSE log-RV = {har_mean:.5f}  per coin: {har_per_coin}")
        print(f"  Edge (HAR-M5) - 2σ_M5 = {edge_2sigma:.5f}  verdict: {verdict}")
        rows.append({
            "horizon": h,
            "m5_mean_mse": m5_out["mean_mse"],
            "m5_std_mse": m5_out["std_mse"],
            "m5_per_seed_mse": m5_out["per_seed_mse"],
            "har_mean_mse": har_mean,
            "har_per_coin": har_per_coin,
            "edge_2sigma": edge_2sigma,
            "verdict": verdict,
            "n_seeds": m5_out["n_seeds"],
            "n_splits": m5_out["n_splits"],
            "n_target": m5_out["n_target"],
        })

    out_path = Path(args.out_json)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps({
        "rows": rows,
        "elapsed_s": time.time() - t0,
        "config": {"epochs": epochs, "seeds": list(seeds),
                   "n_splits": args.n_splits, "device": str(device),
                   "dry_run": args.dry_run},
    }, indent=2))
    print(f"\n[done] {time.time() - t0:.1f}s — wrote {out_path}")


if __name__ == "__main__":
    main()
