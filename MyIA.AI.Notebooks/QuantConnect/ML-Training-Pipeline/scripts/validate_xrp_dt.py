"""Validation dediee XRP du Decision Transformer (Epic #1454).

Repond au greenlight coordinateur : l'edge XRP (+0.65 gross_sharpe > BH +0.39,
5/5 seeds positifs, cf results/dt_multiseed/dt_multiseed_20260623_180656.json)
SURVIT-IL a :

  (a) **couts de transaction** -> NET Sharpe (actuellement None dans le JSON
      existant, calcule ici avec 10 bps crypto sur les changements de position) ;
  (b) **walk-forward OOS >=5-fold** sur une periode DISTINCTE du build_trajectories
      (WalkForwardSplitter, gap=10 anti-leakage inter-fold) ;
  (c) **Diebold-Mariano** vs benchmark buy-and-hold, hors-echantillon.

**Garde-fou honnetete (directive coordinateur)** : le teacher de
``build_trajectories`` est un momentum DETERMINISTE (buy si past_return > 0.01,
sell si < -0.01, hold sinon). La vraie question = XRP a-t-il un edge momentum
**REEL** OOS, ou est-ce de la chance de periode ? On isole en comparant trois
strategies OOS sur les memes folds walk-forward :

  1. **DT** : politique APPRISE (DecisionTransformer imitant le momentum) ;
  2. **momentum_naked** : le teacher PUR applique au test (isole l'edge momentum
     sous-jacent, sans le bruit d'apprentissage du DT) ;
  3. **buy_and_hold** : benchmark passif.

Si le DT bat BH mais pas le momentum naked, le DT n'ajoute rien (edge = momentum,
pas de valeur ajoutée par l'apprentissage). Si le momentum naked lui-même ne bat
pas BH en OOS, alors l'edge XRP etait de la chance de periode (NO BEATS reel).

Verdict : BEATS / NO-BEATS / INCONCLUSIVE sur le NET Sharpe post-TC, avec
p-value DM (HAC Newey-West), edge >= 2 sigma cross-seed sinon flag "noise".
>=4 seeds (0/1/7/42/99). Pas de "promising".

Usage
-----
Smoke CPU :
    python scripts/validate_xrp_dt.py --smoke

Run complet GPU 2 :
    CUDA_VISIBLE_DEVICES=2 python scripts/validate_xrp_dt.py

Sortie : ``results/xrp_dt_validation/<timestamp>.json`` (series OOS par
fold/seed, net/gross sharpe, momentum naked, DM) + resume verdict sur stdout.
Checkpoints .pt transients (PAS stages).

References
----------
- train_rl_dt.build_trajectories (teacher momentum deterministe)
- walk_forward.WalkForwardSplitter (walk-forward 5-fold, gap anti-leakage)
- dm_test.diebold_mariano_test (HAC Newey-West, correction HLN)
- ML-Training-Pipeline gate : WF 5-fold + >=4 seeds + edge>=2sigma + DM + tx costs
"""

from __future__ import annotations

import argparse
import json
import math
import sys
import time
from datetime import datetime
from pathlib import Path
from typing import List, Tuple

import numpy as np
import torch
import torch.nn.functional as F

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

from data_utils import compute_data_hash, load_data
from features import FeatureEngineer
from walk_forward import WalkForwardSplitter
import dm_test as DM
from train_rl_dt import build_trajectories, train_dt, create_sequence_batches

SCRIPTS_PARENT = SCRIPT_DIR.parent
CRYPTO_DIR = SCRIPTS_PARENT.parent / "datasets" / "yfinance" / "crypto_panier"
RESULTS_DIR = SCRIPTS_PARENT / "results" / "xrp_dt_validation"
COMMISSION_BPS = 10  # crypto transaction cost (cf train_dt_multiseed)
COIN = "XRP-USD"


def momentum_naked_positions(prices: np.ndarray, window: int = 20,
                             buy_thr: float = 0.01, sell_thr: float = -0.01
                             ) -> np.ndarray:
    """Positions du teacher momentum PUR (le teacher de build_trajectories).

    Reprend EXACTEMENT la regle deterministe de train_rl_dt.build_trajectories
    (l.339-350) : buy (1.0) si past_return > buy_thr, sell (-1.0) si <
    sell_thr, hold (0.0) sinon. Appliquee au test set = isole l'edge momentum
    sous-jacent, sans le bruit d'apprentissage du DT.
    """
    n = len(prices)
    positions = np.zeros(n, dtype=np.float32)
    pos = 0.0
    for i in range(1, n):
        if i >= window:
            past_return = (prices[i - 1] - prices[i - window]) / (prices[i - window] + 1e-8)
        else:
            past_return = 0.0
        if past_return > buy_thr:
            pos = 1.0
        elif past_return < sell_thr:
            pos = -1.0
        else:
            pos = 0.0
        positions[i] = pos
    return positions


@torch.no_grad()
def dt_positions_on_test(model, test_trajs: dict, n_test: int,
                         context_length: int, batch_size: int, device: str
                         ) -> np.ndarray:
    """Positions predites par le DT sur le test set (0=hold, 1=buy, 2=sell -> -1/0/1)."""
    model.eval()
    batches = create_sequence_batches(test_trajs, context_length=context_length,
                                      batch_size=batch_size, shuffle=False)
    all_preds = []
    for batch in batches:
        states = batch["states"].to(device)
        actions = batch["actions"].to(device)
        rtg = batch["rtg"].to(device)
        mask = batch["attention_mask"].to(device)
        logits = model(states, actions, rtg, attention_mask=mask)
        preds = logits.argmax(dim=-1)
        mask_flat = mask.reshape(-1).bool()
        valid = preds.reshape(-1)[mask_flat].cpu().numpy()
        all_preds.append(valid)
    preds_array = np.concatenate(all_preds) if all_preds else np.array([], dtype=int)
    positions = np.zeros(len(preds_array), dtype=np.float32)
    positions[preds_array == 1] = 1.0
    positions[preds_array == 2] = -1.0
    return positions


def sharpe(returns: np.ndarray, periods: int = 252) -> float:
    if len(returns) < 2:
        return 0.0
    mu = float(np.mean(returns))
    sd = float(np.std(returns, ddof=1)) + 1e-12
    return mu / sd * math.sqrt(periods)


def net_returns(positions: np.ndarray, test_returns: np.ndarray,
                commission: float) -> np.ndarray:
    """Rendements strategies nets : position*return - TC sur changements de position."""
    min_len = min(len(positions), len(test_returns))
    strat = test_returns[:min_len] * positions[:min_len]
    pos_changes = np.abs(np.diff(positions[:min_len], prepend=0.0))
    tc = pos_changes * commission
    return strat - tc


def gross_returns(positions: np.ndarray, test_returns: np.ndarray) -> np.ndarray:
    min_len = min(len(positions), len(test_returns))
    return test_returns[:min_len] * positions[:min_len]


def run_one_seed(seed: int, epochs: int, n_splits: int, window: int,
                 context_length: int, batch_size: int, lr: float,
                 d_model: int, nhead: int, num_layers: int, device: str,
                 commission_bps: int, dry_run: bool) -> dict:
    """Walk-forward 5-fold XRP pour une seed. Retourne series OOS + sharpe (gross/net/mom/BH)."""
    np.random.seed(seed)
    torch.manual_seed(seed)

    if dry_run:
        from data_utils import generate_synthetic_data
        raw = generate_synthetic_data(1500)
        data_hash = "synthetic-dryrun"
    else:
        raw = load_data(CRYPTO_DIR, COIN)
        data_hash = compute_data_hash(raw)

    indicators = ["returns", "volatility", "volume_ratio", "ma_ratios",
                  "rsi", "macd", "bollinger", "true_range_atr", "obv"]
    engineer = FeatureEngineer(lookback=window, indicators=indicators)
    features_df = engineer.transform(raw, add_target=False)
    features_arr = features_df.values.astype(np.float32)
    prices = raw.loc[features_df.index, "Close"].values.astype(np.float32)
    commission = commission_bps / 10000.0  # bps -> fraction (cf --commission-bps)

    splitter = WalkForwardSplitter(
        n_splits=n_splits,
        train_size=max(252, len(prices) // (n_splits + 1)),
        test_size=max(63, len(prices) // (n_splits * 3)),
        gap=10,
    )

    fold_records = []
    # Series OOS concatenees sur les folds (alignees, pour DM test).
    dt_gross_all, dt_net_all, mom_all, bh_all = [], [], [], []

    for fold_idx, (train_idx, test_idx) in enumerate(splitter.split(np.arange(len(prices)))):
        if len(test_idx) < context_length + window + 10:
            continue
        train_prices = prices[train_idx]
        train_features = features_arr[train_idx]
        test_prices = prices[test_idx]
        test_features = features_arr[test_idx]

        # Normalisation train-only (anti-leakage).
        mean = train_features.mean(axis=0)
        std = np.where(train_features.std(axis=0) < 1e-8, 1.0, train_features.std(axis=0))
        train_features_norm = (train_features - mean) / std
        test_features_norm = (test_features - mean) / std

        train_trajs = build_trajectories(train_prices, train_features_norm,
                                         window=window, context_length=context_length,
                                         commission=commission)
        test_trajs = build_trajectories(test_prices, test_features_norm,
                                        window=window, context_length=context_length,
                                        commission=commission)
        if len(train_trajs["states"]) <= context_length:
            continue
        if len(test_trajs["states"]) <= context_length:
            continue

        state_dim = train_trajs["states"].shape[1]
        result = train_dt(train_trajs, state_dim=state_dim, d_model=d_model,
                          nhead=nhead, num_layers=num_layers,
                          context_length=context_length, epochs=epochs,
                          batch_size=batch_size, lr=lr, device=device)
        model = result["model"]

        # Positions DT sur le test set.
        dt_pos = dt_positions_on_test(model, test_trajs, len(test_prices),
                                      context_length, batch_size, device)
        # Rendements du test (alignes sur la trajectoire).
        test_returns_full = np.diff(test_prices[:len(dt_pos) + 1]) / \
            (test_prices[:len(dt_pos) + 1][:-1] + 1e-8)
        # Momentum naked (teacher pur) sur le MEME test set.
        mom_pos = momentum_naked_positions(test_prices[:len(dt_pos) + 1], window=window)
        mom_pos = mom_pos[:len(dt_pos)]
        # BH sur le meme horizon.
        bh_pos = np.ones(len(dt_pos), dtype=np.float32)

        dt_g = gross_returns(dt_pos, test_returns_full)
        dt_n = net_returns(dt_pos, test_returns_full, commission)
        mom_g = gross_returns(mom_pos, test_returns_full)
        bh_g = gross_returns(bh_pos, test_returns_full)

        fold_records.append({
            "fold": fold_idx,
            "n_test": int(len(dt_pos)),
            "dt_gross_sharpe": round(sharpe(dt_g), 4),
            "dt_net_sharpe": round(sharpe(dt_n), 4),
            "momentum_naked_sharpe": round(sharpe(mom_g), 4),
            "bh_sharpe": round(sharpe(bh_g), 4),
        })
        dt_gross_all.append(dt_g)
        dt_net_all.append(dt_n)
        mom_all.append(mom_g)
        bh_all.append(bh_g)

        del model, result
        if torch.cuda.is_available():
            torch.cuda.empty_cache()

    # Concatener les series OOS par fold (DM test sur la serie temporelle complete).
    dt_net_series = np.concatenate(dt_net_all) if dt_net_all else np.array([])
    dt_gross_series = np.concatenate(dt_gross_all) if dt_gross_all else np.array([])
    mom_series = np.concatenate(mom_all) if mom_all else np.array([])
    bh_series = np.concatenate(bh_all) if bh_all else np.array([])

    # DM test : DT-net vs BH. Loss differentielle = -(ret_DT - ret_BH) (on veut DT > BH).
    # diebold_mariano_test prend des forecast ERRORS (plus petit = mieux).
    # errors_a = -dt_net (on veut maximiser le rendement), errors_b = -bh.
    dm = None
    if len(dt_net_series) > 30 and len(bh_series) > 30:
        err_dt = -dt_net_series
        err_bh = -bh_series
        try:
            r = DM.diebold_mariano_test(err_dt, err_bh, loss_fn="mse", hln_correction=True)
            dm = {"dm_stat": round(r.dm_statistic, 4), "p_value": round(r.p_value, 4),
                  "mean_loss_diff": round(r.mean_loss_diff, 6), "n_obs": int(r.n_observations)}
        except Exception as e:
            dm = {"error": str(e)}

    return {
        "seed": seed, "coin": COIN, "data_hash": data_hash, "n_folds": len(fold_records),
        "fold_records": fold_records,
        "dt_net_sharpe_oos": round(sharpe(dt_net_series), 4),
        "dt_gross_sharpe_oos": round(sharpe(dt_gross_series), 4),
        "momentum_naked_sharpe_oos": round(sharpe(mom_series), 4),
        "bh_sharpe_oos": round(sharpe(bh_series), 4),
        "dm_dt_vs_bh": dm,
        # Series brutes pour audit (non commitees si trop volumineuses ; on garde les sharpe).
        "n_oos_points": int(len(dt_net_series)),
    }


def aggregate_seeds(seed_results: List[dict]) -> dict:
    """Verdict cluster honnete sur le NET Sharpe post-TC + DM + edge 2sigma."""
    valid = [r for r in seed_results if "error" not in r and r["n_folds"] > 0]
    if len(valid) < 2:
        return {"verdict": "INCONCLUSIVE", "reason": f"Only {len(valid)} valid seeds"}

    net_sharpes = np.array([r["dt_net_sharpe_oos"] for r in valid])
    mom_sharpes = np.array([r["momentum_naked_sharpe_oos"] for r in valid])
    bh_sharpes = np.array([r["bh_sharpe_oos"] for r in valid])
    dt_vs_bh = net_sharpes - bh_sharpes

    mean_edge = float(np.mean(dt_vs_bh))
    std_edge = float(np.std(dt_vs_bh, ddof=1)) if len(dt_vs_bh) > 1 else 0.0
    sigma_edge = mean_edge / std_edge if std_edge > 1e-9 else 0.0
    n_pos_net = int(np.sum(net_sharpes > 0))
    n_beats_bh = int(np.sum(net_sharpes > bh_sharpes))

    # DM aggregation : p-value mediane cross-seed (chaque seed a sa serie OOS).
    pvals = [r["dm_dt_vs_bh"]["p_value"] for r in valid
             if r.get("dm_dt_vs_bh") and "p_value" in r["dm_dt_vs_bh"]]
    dm_median_p = float(np.median(pvals)) if pvals else None

    # Momentum naked bat-il BH en moyenne ? (question cle : edge momentum reel ?)
    mom_vs_bh = float(np.mean(mom_sharpes - bh_sharpes))
    n_mom_beats_bh = int(np.sum(mom_sharpes > bh_sharpes))

    # Verdict : BEATS si mean_edge > 0 ET sigma_edge >= 2 ET dm_median_p < 0.05 ET n_beats_bh >= 3/4.
    threshold_sigma = 2.0
    if mean_edge > 0 and sigma_edge >= threshold_sigma and dm_median_p is not None \
            and dm_median_p < 0.05 and n_beats_bh >= max(3, len(valid) - 1):
        verdict = "BEATS"
    elif mean_edge <= 0 and n_beats_bh == 0:
        verdict = "NO-BEATS"
    else:
        verdict = "INCONCLUSIVE"
    if mean_edge > 0 and sigma_edge < threshold_sigma:
        verdict += " [noise: edge < 2sigma]"

    return {
        "n_seeds": len(valid),
        "net_sharpe_mean": round(float(np.mean(net_sharpes)), 4),
        "net_sharpe_std": round(float(np.std(net_sharpes, ddof=1)), 4),
        "bh_sharpe_mean": round(float(np.mean(bh_sharpes)), 4),
        "momentum_naked_sharpe_mean": round(float(np.mean(mom_sharpes)), 4),
        "mean_edge_net_vs_bh": round(mean_edge, 4),
        "std_edge": round(std_edge, 4),
        "sigma_edge": round(sigma_edge, 4),
        "n_seeds_net_positive": n_pos_net,
        "n_seeds_dt_beats_bh": n_beats_bh,
        "dm_dt_vs_bh_median_p": round(dm_median_p, 4) if dm_median_p is not None else None,
        "momentum_naked_vs_bh_mean": round(mom_vs_bh, 4),
        "n_seeds_momentum_beats_bh": n_mom_beats_bh,
        "verdict": verdict,
    }


def main():
    parser = argparse.ArgumentParser(
        description="Validation XRP dediee du Decision Transformer (Epic #1454).")
    parser.add_argument("--smoke", action="store_true",
                        help="CPU smoke : 1 seed, 10 epochs, rapide.")
    parser.add_argument("--seeds", nargs="+", type=int, default=[0, 1, 7, 42, 99])
    parser.add_argument("--epochs", type=int, default=30)
    parser.add_argument("--n-splits", type=int, default=5)
    parser.add_argument("--d-model", type=int, default=128)
    parser.add_argument("--nhead", type=int, default=4)
    parser.add_argument("--num-layers", type=int, default=3)
    parser.add_argument("--context-length", type=int, default=20)
    parser.add_argument("--window", type=int, default=20)
    parser.add_argument("--batch-size", type=int, default=32)
    parser.add_argument("--lr", type=float, default=1e-4)
    parser.add_argument("--device", default=None)
    parser.add_argument("--commission-bps", type=int, default=COMMISSION_BPS,
                        help=f"Crypto transaction cost in bps (default {COMMISSION_BPS}, "
                             "stress test = 50). Enables a TC sweep.")
    args = parser.parse_args()

    if args.smoke:
        args.seeds = [0]
        args.epochs = 10
        if args.device is None:
            args.device = "cpu"

    device = args.device or ("cuda" if torch.cuda.is_available() else "cpu")
    out_dir = RESULTS_DIR
    out_dir.mkdir(parents=True, exist_ok=True)
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")

    print("=" * 78)
    print(f"VALIDATION XRP DECISION TRANSFORMER — Epic #1454")
    print("=" * 78)
    print(f"Date: {datetime.now().isoformat()}")
    print(f"Coin: {COIN} | device: {device} | smoke: {args.smoke}")
    print(f"WF: {args.n_splits} folds (gap=10) | seeds: {args.seeds} | epochs: {args.epochs}")
    print(f"TC: {args.commission_bps} bps crypto | Question: edge XRP survit TC + OOS WF + DM ?")
    print(f"Output: {out_dir}")
    print()

    seed_results = []
    for i, seed in enumerate(args.seeds):
        print(f"\n[{i+1}/{len(args.seeds)}] seed {seed}")
        t0 = time.time()
        try:
            r = run_one_seed(seed=seed, epochs=args.epochs, n_splits=args.n_splits,
                             window=args.window, context_length=args.context_length,
                             batch_size=args.batch_size, lr=args.lr,
                             d_model=args.d_model, nhead=args.nhead,
                             num_layers=args.num_layers, device=device,
                             commission_bps=args.commission_bps, dry_run=args.smoke)
            print(f"  net_sharpe={r['dt_net_sharpe_oos']}  gross={r['dt_gross_sharpe_oos']}  "
                  f"mom_naked={r['momentum_naked_sharpe_oos']}  bh={r['bh_sharpe_oos']}  "
                  f"dm_p={r['dm_dt_vs_bh'].get('p_value') if r.get('dm_dt_vs_bh') else None}  "
                  f"({time.time()-t0:.0f}s)")
            seed_results.append(r)
        except Exception as e:
            import traceback
            print(f"  EXCEPTION seed {seed}: {e}")
            traceback.print_exc()
            seed_results.append({"seed": seed, "error": str(e)})

    agg = aggregate_seeds(seed_results)
    print("\n" + "=" * 78)
    print("VERDICT VALIDATION XRP (NET Sharpe post-TC, WF 5-fold, DM vs BH)")
    print("=" * 78)
    print(json.dumps(agg, indent=2))

    # Diagnostic momentum : la vraie question (edge momentum reel vs chance de periode).
    # (Uniquement si l'agregation a complete, i.e. >=2 seeds valides.)
    if "momentum_naked_vs_bh_mean" in agg:
        print("\nDiagnostic momentum (question cle du coordinateur) :")
        print(f"  momentum_naked bat BH sur {agg['n_seeds_momentum_beats_bh']}/{agg['n_seeds']} seeds "
              f"(mean edge mom-BH = {agg['momentum_naked_vs_bh_mean']:+.4f})")
        print(f"  => si momentum naked ne bat PAS BH en OOS, l'edge XRP etait chance de periode.")
        print(f"  => si DT bat BH mais pas momentum naked, le DT n'ajoute rien (edge = momentum pur).")
    else:
        print(f"\nDiagnostic momentum : saute ({agg.get('reason', 'agregation incomplete')}).")

    summary = {
        "timestamp": ts, "coin": COIN, "device": device, "smoke": args.smoke,
        "config": {"epochs": args.epochs, "n_splits": args.n_splits,
                   "seeds": args.seeds, "commission_bps": args.commission_bps,
                   "d_model": args.d_model, "window": args.window,
                   "context_length": args.context_length},
        "seed_results": seed_results,
        "aggregate": agg,
    }
    out_path = out_dir / f"{ts}.json"
    with open(out_path, "w", encoding="utf-8") as fh:
        json.dump(summary, fh, indent=2)
    print(f"\nResultats -> {out_path}")


if __name__ == "__main__":
    main()
