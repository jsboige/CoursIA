"""Holdout out-of-sample XRP du Decision Transformer (Epic #1454).

Etape decisionnelle post-validation walk-forward (validate_xrp_dt.py, run
21/07) : le verdict etait BEATS@10bps (net Sharpe 0.651 vs BH 0.390, edge
3.84 sigma, DM p=0.024, 5/5 seeds) mais INCONCLUSIVE@50bps. La decision
requiert de confirmer l'edge 10 bps sur une periode JAMAIS touchee par le
walk-forward avant tout claim BEATS gradue.

Deux modes de holdout (a lancer separement, --label distinct) :

  (a) **internal** : train sur [debut .. --train-end], holdout =
      [--train-end + gap .. fin du CSV]. Statistiquement plus puissant
      (plusieurs centaines d'obs) mais la periode a ETE vue par les folds
      du run 21/07 — contamination de selection possible (on a decide de
      poursuivre en ayant vu ces resultats).
  (b) **fresh** : train sur tout le CSV historique (<= 2026-04-21),
      holdout = data POSTERIEURE au CSV du run 21/07 (2026-05 ->
      aujourd'hui, CSV additionnel telecharge). Zero contamination, mais
      puissance faible (~60-70 obs) : le DM test y est indicatif.

Contrairement au walk-forward (5 modeles/seed), on entraine UN modele par
seed sur la fenetre train, puis on evalue DT / momentum_naked / buy_and_hold
sur le holdout. Memes garde-fous que validate_xrp_dt : normalisation
train-only, gap anti-leakage, net Sharpe post-TC, DM HAC Newey-West,
>=4 seeds, edge >= 2 sigma cross-seed sinon INCONCLUSIVE. Pas de "promising".

Usage
-----
Smoke CPU :
    python scripts/validate_xrp_dt_holdout.py --smoke

Holdout interne (GPU 2) :
    CUDA_VISIBLE_DEVICES=2 python scripts/validate_xrp_dt_holdout.py \
        --label internal --train-end 2025-06-30

Holdout frais (GPU 2, apres download du CSV 2026-05 -> present) :
    CUDA_VISIBLE_DEVICES=2 python scripts/validate_xrp_dt_holdout.py \
        --label fresh --train-end 2026-04-21 --holdout-start 2026-05-01

Sortie : ``results/xrp_dt_validation/holdout_<label>_<timestamp>.json``.
Checkpoints .pt transients (PAS stages).
"""

from __future__ import annotations

import argparse
import json
from datetime import datetime, timedelta
from pathlib import Path

import numpy as np
import pandas as pd
import torch

from validate_xrp_dt import (
    COIN, CRYPTO_DIR, RESULTS_DIR, COMMISSION_BPS,
    momentum_naked_positions, dt_positions_on_test,
    sharpe, net_returns, gross_returns,
)
from data_utils import compute_data_hash, load_data
from features import FeatureEngineer
from train_rl_dt import build_trajectories, train_dt
import dm_test as DM


def run_one_seed_holdout(seed: int, raw: pd.DataFrame, train_end: str,
                         holdout_start: str, holdout_end: str | None,
                         epochs: int, window: int, context_length: int,
                         batch_size: int, lr: float, d_model: int, nhead: int,
                         num_layers: int, device: str, commission_bps: int) -> dict:
    """Un modele par seed : train <= train_end, eval sur [holdout_start .. holdout_end]."""
    np.random.seed(seed)
    torch.manual_seed(seed)

    indicators = ["returns", "volatility", "volume_ratio", "ma_ratios",
                  "rsi", "macd", "bollinger", "true_range_atr", "obv"]
    engineer = FeatureEngineer(lookback=window, indicators=indicators)
    # Features sur la frame ENTIERE (indicateurs backward-only : les lignes du
    # holdout consomment l'historique d'avant holdout_start, pas le futur).
    features_df = engineer.transform(raw, add_target=False)
    prices_all = raw.loc[features_df.index, "Close"].values.astype(np.float32)
    features_arr = features_df.values.astype(np.float32)
    idx = features_df.index

    train_mask = idx <= pd.Timestamp(train_end)
    hold_mask = idx >= pd.Timestamp(holdout_start)
    if holdout_end:
        hold_mask &= idx <= pd.Timestamp(holdout_end)

    train_prices = prices_all[train_mask]
    train_features = features_arr[train_mask]
    test_prices = prices_all[hold_mask]
    test_features = features_arr[hold_mask]
    commission = commission_bps / 10000.0

    # Normalisation train-only (anti-leakage), comme dans le fold WF.
    mean = train_features.mean(axis=0)
    std = np.where(train_features.std(axis=0) < 1e-8, 1.0, train_features.std(axis=0))
    train_trajs = build_trajectories(train_prices, (train_features - mean) / std,
                                     window=window, context_length=context_length,
                                     commission=commission)
    test_trajs = build_trajectories(test_prices, (test_features - mean) / std,
                                    window=window, context_length=context_length,
                                    commission=commission)
    if len(train_trajs["states"]) <= context_length:
        raise RuntimeError(f"train window trop courte ({len(train_trajs['states'])} states)")
    if len(test_trajs["states"]) <= context_length:
        raise RuntimeError(f"holdout trop court ({len(test_trajs['states'])} states)")

    state_dim = train_trajs["states"].shape[1]
    result = train_dt(train_trajs, state_dim=state_dim, d_model=d_model,
                      nhead=nhead, num_layers=num_layers,
                      context_length=context_length, epochs=epochs,
                      batch_size=batch_size, lr=lr, device=device)
    model = result["model"]

    dt_pos = dt_positions_on_test(model, test_trajs, len(test_prices),
                                  context_length, batch_size, device)
    test_returns_full = np.diff(test_prices[:len(dt_pos) + 1]) / \
        (test_prices[:len(dt_pos) + 1][:-1] + 1e-8)
    mom_pos = momentum_naked_positions(test_prices[:len(dt_pos) + 1], window=window)[:len(dt_pos)]
    bh_pos = np.ones(len(dt_pos), dtype=np.float32)

    dt_n = net_returns(dt_pos, test_returns_full, commission)
    dt_g = gross_returns(dt_pos, test_returns_full)
    mom_n = net_returns(mom_pos, test_returns_full, commission)
    bh_g = gross_returns(bh_pos, test_returns_full)

    dm = None
    dm_mom = None
    if len(dt_n) > 30:
        # loss_fn="linear" (#10228): mse/mae are symmetric ((-r)**2 == r**2)
        # and made the test sign-blind -- a winning and a losing return series
        # got bit-identical dm_stat. Linear loss L(e) = e preserves the sign,
        # so d = (-bh_g) - (-dt_n) = dt_n - bh_g and E[d] < 0 <=> DT beats BH.
        try:
            r = DM.diebold_mariano_test(-dt_n, -bh_g, loss_fn="linear", hln_correction=True)
            dm = {"dm_stat": round(r.dm_statistic, 4), "p_value": round(r.p_value, 4),
                  "n_obs": int(r.n_observations)}
        except Exception as e:
            dm = {"error": str(e)}
        # Momentum is the real adversary: BH is degenerate when the asset falls
        # (fresh-window BH sharpe was -1.80). A DM vs naked momentum is what
        # makes the third conjunct of pr-review-discipline section C informative.
        try:
            r_mom = DM.diebold_mariano_test(-dt_n, -mom_n, loss_fn="linear", hln_correction=True)
            dm_mom = {"dm_stat": round(r_mom.dm_statistic, 4), "p_value": round(r_mom.p_value, 4),
                      "n_obs": int(r_mom.n_observations)}
        except Exception as e:
            dm_mom = {"error": str(e)}

    del model, result
    if torch.cuda.is_available():
        torch.cuda.empty_cache()

    # Persist the per-seed return series so the DM p-values stay recalculable
    # post hoc: today only aggregated Sharpes are saved, which froze the p-value
    # at the buggy mse value and prevented correcting it without a rerun.
    # ~300 obs x 3 series x 5 seeds stays small.
    return {
        "seed": seed,
        "n_holdout_obs": int(len(dt_n)),
        "dt_net_sharpe": round(sharpe(dt_n), 4),
        "dt_gross_sharpe": round(sharpe(dt_g), 4),
        "momentum_naked_net_sharpe": round(sharpe(mom_n), 4),
        "bh_sharpe": round(sharpe(bh_g), 4),
        "dm_dt_vs_bh": dm,
        "dm_dt_vs_momentum": dm_mom,
        "dt_net": [round(float(x), 6) for x in dt_n],
        "bh_gross": [round(float(x), 6) for x in bh_g],
        "momentum_net": [round(float(x), 6) for x in mom_n],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--smoke", action="store_true",
                        help="Sanity CPU sur data synthetique (2 seeds, 2 epochs)")
    parser.add_argument("--label", default="internal",
                        help="Nom du run (internal | fresh | ...)")
    parser.add_argument("--train-end", default="2025-06-30")
    parser.add_argument("--holdout-start", default=None,
                        help="Defaut : train_end + gap jours")
    parser.add_argument("--holdout-end", default=None,
                        help="Defaut : fin des donnees disponibles")
    parser.add_argument("--gap", type=int, default=10)
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
    args = parser.parse_args()

    if args.smoke:
        args.seeds = args.seeds[:2]
        args.epochs = 2
        device = "cpu"
    else:
        device = args.device or ("cuda" if torch.cuda.is_available() else "cpu")

    if args.smoke:
        from data_utils import generate_synthetic_data
        raw = generate_synthetic_data(900)
        if not isinstance(raw.index, pd.DatetimeIndex):
            raw.index = pd.date_range("2018-01-01", periods=len(raw), freq="D")
        data_hash = "synthetic-smoke"
        # Split positionnel 70/25 avec gap.
        args.train_end = str(raw.index[int(len(raw) * 0.70)].date())
    else:
        raw = load_data(CRYPTO_DIR, COIN)
        data_hash = compute_data_hash(raw)

    holdout_start = args.holdout_start or str(
        (pd.Timestamp(args.train_end) + timedelta(days=args.gap)).date())
    gap_days = (pd.Timestamp(holdout_start) - pd.Timestamp(args.train_end)).days
    if gap_days < args.gap:
        raise SystemExit(f"holdout_start doit etre >= train_end + {args.gap} j "
                         f"(gap anti-leakage) ; ecart actuel = {gap_days} j")

    out_dir = RESULTS_DIR
    out_dir.mkdir(parents=True, exist_ok=True)
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")

    print(f"=== XRP DT holdout OOS (#1454) — label={args.label} ===")
    print(f"Date: {datetime.now().isoformat()} | device: {device} | smoke: {args.smoke}")
    print(f"Data: {len(raw)} rows [{raw.index.min().date()} .. {raw.index.max().date()}] "
          f"hash={data_hash[:12]}")
    print(f"Train <= {args.train_end} | holdout [{holdout_start} .. "
          f"{args.holdout_end or 'fin'}] | gap={gap_days} j")
    print(f"TC: {args.commission_bps} bps | seeds: {args.seeds} | epochs: {args.epochs}")
    print()

    seed_results = []
    for seed in args.seeds:
        print(f"[seed {seed}] train + eval holdout ...", flush=True)
        r = run_one_seed_holdout(
            seed, raw, args.train_end, holdout_start, args.holdout_end,
            epochs=args.epochs, window=args.window,
            context_length=args.context_length, batch_size=args.batch_size,
            lr=args.lr, d_model=args.d_model, nhead=args.nhead,
            num_layers=args.num_layers, device=device,
            commission_bps=args.commission_bps)
        seed_results.append(r)
        print(f"  net={r['dt_net_sharpe']}  gross={r['dt_gross_sharpe']}  "
              f"mom_net={r['momentum_naked_net_sharpe']}  bh={r['bh_sharpe']}  "
              f"dm_p={r['dm_dt_vs_bh'].get('p_value') if r.get('dm_dt_vs_bh') else None}",
              flush=True)

    # Agregation cross-seed. BH est deterministe (meme serie pour toutes les seeds).
    dt_nets = np.array([r["dt_net_sharpe"] for r in seed_results])
    bh = seed_results[0]["bh_sharpe"]
    mom_net = seed_results[0]["momentum_naked_net_sharpe"]
    seeds_beat = int(np.sum(dt_nets > bh))
    edge_sigma = float((dt_nets.mean() - bh) / (dt_nets.std(ddof=1) + 1e-12)) \
        if len(dt_nets) > 1 else 0.0
    dm_ps = [r["dm_dt_vs_bh"]["p_value"] for r in seed_results
             if r.get("dm_dt_vs_bh") and "p_value" in r["dm_dt_vs_bh"]]
    dm_p_median = float(np.median(dm_ps)) if dm_ps else None

    if dt_nets.mean() <= bh:
        verdict = "NO-BEATS"
    elif seeds_beat >= min(4, len(dt_nets)) and edge_sigma >= 2.0 \
            and dm_p_median is not None and dm_p_median < 0.05:
        verdict = "BEATS"
    else:
        verdict = "INCONCLUSIVE"

    summary = {
        "timestamp": ts, "label": args.label, "coin": COIN, "device": device,
        "smoke": args.smoke, "data_hash": data_hash,
        "config": {"train_end": args.train_end, "holdout_start": holdout_start,
                   "holdout_end": args.holdout_end, "gap_days": gap_days,
                   "seeds": args.seeds, "epochs": args.epochs,
                   "commission_bps": args.commission_bps,
                   "d_model": args.d_model, "window": args.window,
                   "context_length": args.context_length},
        "seed_results": seed_results,
        "aggregate": {
            "dt_net_sharpe_mean": round(float(dt_nets.mean()), 4),
            "dt_net_sharpe_std": round(float(dt_nets.std(ddof=1)), 4)
            if len(dt_nets) > 1 else None,
            "bh_sharpe": bh,
            "momentum_naked_net_sharpe": mom_net,
            "seeds_beat_bh": f"{seeds_beat}/{len(dt_nets)}",
            "edge_sigma": round(edge_sigma, 2),
            "dm_p_median": dm_p_median,
        },
        "verdict": verdict,
    }
    out_path = out_dir / f"holdout_{args.label}_{ts}.json"
    out_path.write_text(json.dumps(summary, indent=2), encoding="utf-8")

    print()
    print(f"=== VERDICT holdout[{args.label}] @ {args.commission_bps} bps : {verdict} ===")
    print(f"  DT net {dt_nets.mean():.3f} (+/- {dt_nets.std(ddof=1):.3f}) vs BH {bh:.3f} "
          f"| mom_naked net {mom_net:.3f}")
    print(f"  seeds>{'BH'}: {seeds_beat}/{len(dt_nets)} | edge {edge_sigma:.2f} sigma "
          f"| DM p mediane {dm_p_median}")
    print(f"  -> {out_path}")


if __name__ == "__main__":
    main()
