"""L3 -- Directional long-horizon GPU trainer on the anti-bias multi-asset panier.

EPIC Curriculum Trading V3 (#1409), sous-issue L3 (#1417). Track ai-01 GPU 2.

Mandate (user 2026-05-22)
-------------------------
Do NOT reinvent architecture. Reapply a PROVEN arch (the s8 long-horizon
directional sweep + a small GPU LSTM, as in train_lstm.py) on the RIGHT data:
- Data = anti-bias multi-asset panier from L1/L2 (#1412/#1413): 26 symbols
  (equities ex-Mag7/FAANG, bonds, commodities, FX, indices). NOT crypto-only
  (s8), NOT SPY/TLT/VIX alone (m15).
- Target = DIRECTIONAL long-horizon: sign(return_{t+h}) for h in {60,120,252}
  trading days. No short-term RV "crystal ball".

Walk-forward 5-fold expanding-but-bounded, >=4 seeds (0/1/7/42). Edge >= 2 sigma
cross-seed else flagged noise. Baseline = buy&hold + majority. Tx >= 5 bps equity.
Verdict: BEATS / NO BEATS / INCONCLUSIVE.

Memory safety -- lessons NOT to reproduce (post-mortem m15_cross_asset_lstm)
---------------------------------------------------------------------------
m15 was killed after 47 min stuck on the 1st combo (24 GB VRAM, 39 GB RAM, zero
output). Structural causes avoided here:
1. NO unbounded expanding refit. Train window is a bounded rolling window
   (TRAIN_WINDOW) -- memory growth is capped.
2. NO O(N^2) normalization. StandardScaler is fit ONCE per fold on the bounded
   train window (O(N)), never recomputed per time step.
3. NO whole train set permanently on GPU. A batched DataLoader streams to GPU;
   model/loaders are freed (del + torch.cuda.empty_cache()) between folds.
4. Sweep is scheduled LONGEST horizon first (h=252 -> 120 -> 60). Short h has
   the most test steps and is slowest, so the chain is validated quickly.

Data dependency (BLOCKING)
--------------------------
L3 training depends on L1/L2 delivering the panier. Until the panier file exists
(see PANIER_PATH / load_panier), only --smoke runs (synthetic data, no real
result claimed). load_panier() raises a clear "blocked on #1412/#1413" message.

Usage
-----
    # End-to-end chain validation on synthetic data (no L1/L2 needed):
    python L3_trend_long_horizon_gpu.py --smoke

    # Real sweep once the panier is delivered by L1/L2:
    python L3_trend_long_horizon_gpu.py --panier <path-to-panier.parquet>

Env: conda coursia-ml-training (Python 3.11, PyTorch 2.x + CUDA), GPU 2.
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
from torch.utils.data import DataLoader, TensorDataset

SCRIPT_DIR = Path(__file__).resolve().parent
RESULTS_DIR = SCRIPT_DIR / "results" / "l3_trend_long_horizon"
CHECKPOINT_PATH = RESULTS_DIR / "checkpoint.jsonl"

# Anti-bias panier data from L1/L2 (#1412/#1413). CSV with DatetimeIndex, cols=tickers.
PANIER_CSV = SCRIPT_DIR.parent.parent / "datasets" / "panier" / "panier_close_all.csv"
PANIER_PATH = RESULTS_DIR.parent / "l1_panier" / "panier_daily_close.parquet"

# Sweep config -- longest horizon first (anti-m15 lesson #4)
HORIZONS = [252, 120, 60]
SEEDS = [0, 1, 7, 42]
N_SPLITS = 5
TRAIN_WINDOW = 1500          # bounded rolling train window in days (anti-m15 #1)
SEQ_LEN = 60                 # LSTM lookback window
BATCH_SIZE = 256
EPOCHS = 30
HIDDEN = 64
LR = 1e-3
FEE_BPS = 5                  # equity tx cost
EDGE_SIGMA = 2.0             # cross-seed edge threshold


# -- Feature engineering (reused from s8, lookahead-safe, O(N) rolling) ---------


def build_trend_features(close: pd.Series) -> pd.DataFrame:
    """Long-horizon trend features from daily close. All lagged by 1 (no lookahead).

    Uses pandas rolling (O(N)) -- never the per-step np.nanmean(x[:i]) that made
    m15 O(N^2) (anti-m15 lesson #2).
    """
    df = pd.DataFrame(index=close.index)
    ret = close.pct_change()
    log_ret = np.log(close / close.shift(1))

    for fast, slow in [(5, 20), (20, 50), (50, 200)]:
        ma_f = close.rolling(fast, min_periods=fast).mean()
        ma_s = close.rolling(slow, min_periods=slow).mean()
        df[f"ma_ratio_{fast}_{slow}"] = (ma_f / ma_s - 1.0).shift(1)

    for w in [5, 20, 60]:
        df[f"vol_{w}"] = ret.rolling(w, min_periods=w).std().shift(1)

    delta = close.diff()
    gain = delta.clip(lower=0)
    loss = -delta.clip(upper=0)
    avg_gain = gain.rolling(14, min_periods=14).mean()
    avg_loss = loss.rolling(14, min_periods=14).mean()
    rs = avg_gain / avg_loss.replace(0, np.nan)
    df["rsi_14"] = (100 - 100 / (1 + rs)).shift(1)

    rv = (log_ret ** 2).rolling(22, min_periods=22).sum().shift(1)
    df["log_rv_22"] = np.log(rv.clip(lower=1e-12))

    for w in [5, 22]:
        df[f"ret_agg_{w}"] = log_ret.rolling(w, min_periods=w).sum().shift(1)

    df["log_volume_22"] = np.log(
        ret.abs().rolling(22, min_periods=22).mean().shift(1).clip(lower=1e-12)
    )
    for h in HORIZONS:
        df[f"mom_{h}"] = log_ret.rolling(h, min_periods=h).sum().shift(1)

    return df.dropna()


def make_sequences(feat: np.ndarray, target: np.ndarray, seq_len: int):
    """Sliding windows: (N-seq_len, seq_len, n_feat) sequences -> aligned targets."""
    n = len(feat) - seq_len
    if n <= 0:
        return np.empty((0, seq_len, feat.shape[1])), np.empty((0,))
    seqs = np.lib.stride_tricks.sliding_window_view(feat, seq_len, axis=0)
    # sliding_window_view -> (N-seq_len+1, n_feat, seq_len); reorder + drop last
    seqs = np.transpose(seqs, (0, 2, 1))[:n]
    tgt = target[seq_len:]
    return np.ascontiguousarray(seqs), tgt


# -- Model (small LSTM classifier, reused arch a la train_lstm.py) --------------


class TrendLSTM(nn.Module):
    def __init__(self, input_sz: int, hidden_sz: int = HIDDEN):
        super().__init__()
        self.lstm = nn.LSTM(input_sz, hidden_sz, num_layers=1, batch_first=True)
        self.head = nn.Sequential(nn.Linear(hidden_sz, 1))

    def forward(self, x):
        out, _ = self.lstm(x)
        return self.head(out[:, -1, :]).squeeze(-1)


def _sharpe_ann(returns: np.ndarray) -> float:
    if len(returns) < 10:
        return float("nan")
    mu = float(np.mean(returns))
    sigma = float(np.std(returns, ddof=1))
    return (mu / sigma) * np.sqrt(252) if sigma > 1e-12 else float("nan")


# -- Walk-forward training for one (symbol, horizon, seed) ----------------------


def walk_forward_lstm(close: pd.Series, horizon: int, seed: int, device: str) -> dict | None:
    torch.manual_seed(seed)
    np.random.seed(seed)

    feats = build_trend_features(close)
    fwd = close.pct_change().shift(-horizon)
    target = (fwd.reindex(feats.index) > 0).astype(float)
    aligned = feats.assign(_t=target).dropna()
    if len(aligned) < SEQ_LEN + 300:
        return None

    cols = [c for c in aligned.columns if c != "_t"]
    X_all = aligned[cols].values.astype(np.float32)
    y_all = aligned["_t"].values.astype(np.float32)
    n = len(aligned)

    fold = n // (N_SPLITS + 1)
    if fold < SEQ_LEN + 30:
        return None

    all_probs: list[float] = []
    all_truth: list[int] = []
    all_idx: list[int] = []

    for k in range(1, N_SPLITS + 1):
        tr_end = fold * k
        te_end = min(tr_end + fold, n)
        if te_end - tr_end < 30:
            continue
        tr_start = max(0, tr_end - TRAIN_WINDOW)        # bounded window (anti-m15 #1)

        # Normalize ONCE per fold on the bounded train slice (anti-m15 #2)
        mu = X_all[tr_start:tr_end].mean(axis=0)
        sd = X_all[tr_start:tr_end].std(axis=0) + 1e-8
        Xn = (X_all - mu) / sd

        Xtr, ytr = make_sequences(Xn[tr_start:tr_end], y_all[tr_start:tr_end], SEQ_LEN)
        # test sequences need SEQ_LEN of preceding context
        te_ctx = max(0, tr_end - SEQ_LEN)
        Xte, yte = make_sequences(Xn[te_ctx:te_end], y_all[te_ctx:te_end], SEQ_LEN)
        if len(Xtr) < 50 or len(Xte) < 10:
            continue

        train_ds = TensorDataset(torch.from_numpy(Xtr), torch.from_numpy(ytr))
        train_loader = DataLoader(train_ds, batch_size=BATCH_SIZE, shuffle=True)  # batched (anti-m15 #3)

        model = TrendLSTM(Xtr.shape[2]).to(device)
        opt = torch.optim.Adam(model.parameters(), lr=LR)
        loss_fn = nn.BCEWithLogitsLoss()

        model.train()
        for _ in range(EPOCHS):
            for xb, yb in train_loader:
                xb, yb = xb.to(device), yb.to(device)
                opt.zero_grad()
                loss = loss_fn(model(xb), yb)
                loss.backward()
                opt.step()

        model.eval()
        with torch.no_grad():
            xt = torch.from_numpy(Xte).to(device)
            probs = torch.sigmoid(model(xt)).cpu().numpy()

        all_probs.extend(probs.tolist())
        all_truth.extend(yte.astype(int).tolist())
        all_idx.extend(range(te_ctx + SEQ_LEN, te_end))

        del model, opt, train_loader, train_ds, xt    # free GPU between folds (anti-m15 #3)
        if device == "cuda":
            torch.cuda.empty_cache()

    if len(all_probs) < 50:
        return None

    probs = np.array(all_probs)
    truth = np.array(all_truth)
    preds = (probs > 0.5).astype(int)
    dir_acc = float(np.mean(preds == truth))

    try:
        from sklearn.metrics import roc_auc_score
        auc = float(roc_auc_score(truth, probs)) if len(set(truth)) > 1 else float("nan")
    except Exception:
        auc = float("nan")

    # Strategy returns: long if prob>0.5 else short, fee on flips
    fwd_ret = close.pct_change().shift(-1).reindex(aligned.index).values
    sig_ret = np.array([
        (fwd_ret[i] if probs[j] > 0.5 else -fwd_ret[i])
        for j, i in enumerate(all_idx) if i < len(fwd_ret) and not np.isnan(fwd_ret[i])
    ])
    pos = (probs > 0.5).astype(int)
    flips = np.abs(np.diff(pos, prepend=pos[0]))[: len(sig_ret)]
    net = sig_ret - flips * (FEE_BPS / 10000)
    sharpe = _sharpe_ann(net)

    bh = fwd_ret[~np.isnan(fwd_ret)]
    sharpe_bh = _sharpe_ann(bh) if len(bh) >= 30 else float("nan")
    majority = float(max(truth.mean(), 1 - truth.mean()))

    return {
        "auc": auc, "dir_acc": dir_acc, "majority": majority,
        "sharpe": sharpe, "sharpe_bh": sharpe_bh,
        "delta_sharpe": sharpe - sharpe_bh if not np.isnan(sharpe_bh) else float("nan"),
        "n_obs": len(all_probs),
    }


# -- Data loading --------------------------------------------------------------


def load_panier(path: Path) -> pd.DataFrame:
    """Load the L1/L2 anti-bias panier: wide daily close, index=date, cols=symbols.

    Tries --panier arg first, then PANIER_CSV (datasets/panier/), then PANIER_PATH.
    Excludes VIX (volatility index, no price return).
    """
    candidates = [path, PANIER_CSV, PANIER_PATH]
    for p in candidates:
        if p.exists():
            if p.suffix == ".parquet":
                df = pd.read_parquet(p)
            else:
                df = pd.read_csv(p, index_col=0, parse_dates=True)
            df.index = pd.DatetimeIndex(df.index)
            df = df.sort_index()
            # Exclude VIX (volatility index, no price return for momentum)
            if "VIX" in df.columns:
                df = df.drop(columns=["VIX"])
            return df
    raise FileNotFoundError(
        f"Panier not found. Tried: {[str(p) for p in candidates]}\n"
        f"L3 (#1417) needs the anti-bias panier (25 symbols, daily close).\n"
        f"Run with --smoke to validate the training chain on synthetic data."
    )


def make_synthetic_panier(n_days: int = 2000, n_sym: int = 6, seed: int = 0) -> pd.DataFrame:
    """Synthetic multi-asset daily closes (trend + noise) for chain validation only."""
    rng = np.random.default_rng(seed)
    idx = pd.bdate_range("2010-01-01", periods=n_days)
    out = {}
    for s in range(n_sym):
        drift = rng.normal(0.0003, 0.0002)
        trend = np.cumsum(rng.normal(drift, 0.012, n_days))
        cycle = 0.15 * np.sin(np.linspace(0, rng.uniform(6, 18) * np.pi, n_days))
        out[f"SYN{s}"] = 100 * np.exp(trend + cycle)
    return pd.DataFrame(out, index=idx)


# -- Checkpoint (incremental jsonl + resume) -----------------------------------


def load_done_combos(path: Path) -> set:
    done = set()
    if path.exists():
        for line in path.read_text(encoding="utf-8").splitlines():
            if not line.strip():
                continue
            try:
                r = json.loads(line)
                done.add((r["symbol"], r["horizon"], r["seed"]))
            except (json.JSONDecodeError, KeyError):
                continue
    return done


def append_checkpoint(path: Path, row: dict) -> None:
    with open(path, "a", encoding="utf-8") as f:
        f.write(json.dumps(row, default=str) + "\n")


# -- Aggregation & verdict -----------------------------------------------------


def aggregate_and_verdict(rows: list[dict]) -> dict:
    """Cross-seed edge >= EDGE_SIGMA sigma else noise; honest BEATS/NO BEATS/INCONCLUSIVE."""
    by_sh: dict = {}
    for r in rows:
        by_sh.setdefault((r["symbol"], r["horizon"]), []).append(r)

    edges = []
    for (sym, h), group in by_sh.items():
        deltas = [g["delta_sharpe"] for g in group if not np.isnan(g.get("delta_sharpe", float("nan")))]
        if len(deltas) >= 2:
            mu, sd = float(np.mean(deltas)), float(np.std(deltas, ddof=1))
            sigma_edge = mu / sd if sd > 1e-9 else float("nan")
            edges.append({"symbol": sym, "horizon": h, "mean_delta": mu,
                          "std_delta": sd, "sigma_edge": sigma_edge,
                          "is_signal": (not np.isnan(sigma_edge)) and sigma_edge >= EDGE_SIGMA})

    n_signal = sum(1 for e in edges if e["is_signal"])
    median_auc = float(np.median([r["auc"] for r in rows if not np.isnan(r.get("auc", float("nan")))])) if rows else float("nan")
    if n_signal == 0:
        verdict = "NO BEATS"
    elif n_signal >= max(1, len(edges) // 3):
        verdict = "BEATS"
    else:
        verdict = "INCONCLUSIVE"
    return {"verdict": verdict, "n_signal": n_signal, "n_cells": len(edges),
            "median_auc": median_auc, "edges": edges}


# -- Main sweep ----------------------------------------------------------------


def run_sweep(panier: pd.DataFrame, device: str, smoke: bool) -> None:
    RESULTS_DIR.mkdir(parents=True, exist_ok=True)
    done = load_done_combos(CHECKPOINT_PATH)
    symbols = list(panier.columns)
    horizons = [60] if smoke else HORIZONS
    seeds = [0, 1] if smoke else SEEDS
    total = len(symbols) * len(horizons) * len(seeds)
    t0 = time.time()
    n = 0
    rows: list[dict] = []

    if device == "cuda":
        torch.cuda.reset_peak_memory_stats()

    for h in horizons:                              # longest first (anti-m15 #4)
        for sym in symbols:
            close = panier[sym].dropna()
            for seed in seeds:
                n += 1
                key = (sym, h, seed)
                if key in done:
                    print(f"[{n}/{total}] {sym} h={h} seed={seed} SKIP (checkpoint)", flush=True)
                    continue
                res = walk_forward_lstm(close, h, seed, device)
                if res is None:
                    print(f"[{n}/{total}] {sym} h={h} seed={seed} SKIP (insufficient)", flush=True)
                    continue
                row = {"symbol": sym, "horizon": h, "seed": seed, **res}
                append_checkpoint(CHECKPOINT_PATH, row)
                rows.append(row)
                print(f"[{n}/{total}] {sym} h={h} seed={seed} "
                      f"auc={res['auc']:.3f} dir={res['dir_acc']:.3f} "
                      f"dSharpe={res['delta_sharpe']:+.3f}", flush=True)

    # Reload all rows from checkpoint for full aggregation (resume-safe)
    all_rows = [json.loads(l) for l in CHECKPOINT_PATH.read_text(encoding="utf-8").splitlines() if l.strip()]
    summary = aggregate_and_verdict(all_rows)
    peak_vram = (torch.cuda.max_memory_allocated() / 1e9) if device == "cuda" else 0.0
    summary.update({"n_combos": len(all_rows), "elapsed_s": time.time() - t0,
                    "peak_vram_gb": round(peak_vram, 3), "device": device, "smoke": smoke})
    (RESULTS_DIR / "results.json").write_text(json.dumps(summary, indent=2, default=str), encoding="utf-8")

    print(f"\n{'='*60}")
    print(f"L3 sweep: {len(all_rows)} combos in {summary['elapsed_s']:.0f}s | "
          f"peak VRAM {summary['peak_vram_gb']:.2f} GB")
    print(f"VERDICT: {summary['verdict']} "
          f"(signal cells {summary['n_signal']}/{summary['n_cells']}, "
          f"median AUC {summary['median_auc']:.3f})")
    print(f"Saved: {RESULTS_DIR / 'results.json'}")


def main() -> None:
    ap = argparse.ArgumentParser(description="L3 directional long-horizon GPU trainer")
    ap.add_argument("--smoke", action="store_true",
                    help="Validate the chain on synthetic data (no L1/L2 dependency)")
    ap.add_argument("--panier", type=str, default=str(PANIER_PATH),
                    help="Path to L1/L2 anti-bias panier (parquet/csv)")
    args = ap.parse_args()

    device = "cuda" if torch.cuda.is_available() else "cpu"
    print(f"Device: {device} | torch {torch.__version__}")

    if args.smoke:
        print("[SMOKE] synthetic panier -- chain validation only, no result claim.")
        panier = make_synthetic_panier()
    else:
        panier = load_panier(Path(args.panier))
        print(f"Loaded panier: {panier.shape[1]} symbols, "
              f"{panier.shape[0]} days [{panier.index.min().date()}..{panier.index.max().date()}]")

    run_sweep(panier, device, smoke=args.smoke)


if __name__ == "__main__":
    main()
