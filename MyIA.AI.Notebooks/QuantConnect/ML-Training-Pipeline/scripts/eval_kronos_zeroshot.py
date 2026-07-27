"""
Stage 5: Kronos zero-shot evaluation for financial time-series forecasting.

Evaluates the Kronos foundation model (shiyu-coder/Kronos, AAAI 2026, MIT) in
zero-shot mode on the anti-bias basket. Kronos is pre-trained on 12B K-lines
(OHLCV) across multiple asset classes, enabling direct forecasting without
task-specific fine-tuning. This is the **second foundation-model rung** of the
#8607 spin-out (the first being Chronos-Bolt, c.893, See #8610).

Unlike Chronos-Bolt (deterministic decoder, std_edge=0 across seeds per C893-L),
Kronos forecasts are produced by **autoregressive sampling** (temperature T,
top-p, sample_count). The forward pass is therefore **stochastic**, so the
multi-seed gate is *meaningful* here: cross-seed variance measures forecast
dispersion rather than collapsing to zero. This is the structural difference
that makes Kronos a genuinely distinct rung from Chronos.

Open-source sizes (HuggingFace, ``NeoQuasar/Kronos-*``): mini (~4.1M), small
(~24.7M), base (~102.3M). Kronos-large (~499M) is NOT open-source and is
excluded. We default to ``base`` (largest open checkpoint) for a fair comparison
with Chronos-Bolt-base (~200M, the closest available size).

NOTE on the API: Kronos is distributed as a source repo (no PyPI wheel). The
harness clones ``github.com/shiyu-coder/Kronos`` to a local cache (or reuses
``--kronos-repo``) and imports ``from model import Kronos, KronosTokenizer,
KronosPredictor``. Inference takes an OHLCV pandas DataFrame plus
``x_timestamp`` / ``y_timestamp`` and ``pred_len``, returning a forecast
DataFrame (we extract the ``close`` column for direction/Sharpe metrics).

Anti-pattern safeguards (cf. feedback_ml_trading_pitfalls.md):
- Walk-forward evaluation (no shuffle, temporal split honored)
- Majority-class baseline computed and reported (must beat to claim edge)
- Transaction costs deducted from the strategy returns
- Edge-over-majority reported explicitly

Usage:
    # Dry-run (CPU, synthetic data, NaiveKronosWrapper)
    python eval_kronos_zeroshot.py --dry-run

    # Multi-seed on SPY at h~22
    python eval_kronos_zeroshot.py --symbol SPY --pred-len 24 \\
        --seeds 0,1,7,42,99 --device cuda

    # Full panier sweep (SPY/TLT/GLD x h=22/66/132 x 5 seeds)
    python eval_kronos_zeroshot.py --mode sweep \\
        --symbols SPY,TLT,GLD --pred-lens 24,66,132 \\
        --seeds 0,1,7,42,99 --device cuda \\
        --output-dir results/kronos_zeroshot

Output:
    results.json with per-config (symbol x horizon) edge, std_edge, beats_valid,
    majority baseline and transaction costs, plus a top-level ``sweep`` list
    mirroring the Chronos results.json layout for direct comparison.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from datetime import datetime
from pathlib import Path

import numpy as np
import pandas as pd

sys.path.append(str(Path(__file__).resolve().parent.parent.parent / "shared"))

from baselines import sharpe_from_returns
from data_utils import load_data


KRONOS_REPO_URL = "https://github.com/shiyu-coder/Kronos.git"
KRONOS_REPO_DEFAULT = Path(
    os.environ.get("KRONOS_REPO", "C:/dev/_kronos_src")
)

# Real HuggingFace checkpoints (NeoQuasar mirrors). Kronos-large is not
# open-source and is intentionally absent.
KRONOS_MODEL_IDS = {
    "mini": "NeoQuasar/Kronos-mini",
    "small": "NeoQuasar/Kronos-small",
    "base": "NeoQuasar/Kronos-base",
}
KRONOS_TOKENIZER_ID = "NeoQuasar/Kronos-Tokenizer-base"


def compute_direction_accuracy(y_true: np.ndarray, y_pred: np.ndarray) -> float:
    """Fraction of correctly predicted directional moves."""
    if len(y_true) == 0:
        return 0.0
    return float(np.mean(np.sign(y_true) == np.sign(y_pred)))


def compute_majority_baseline(returns: np.ndarray) -> dict:
    """Compute majority-class baseline for direction prediction."""
    up_frac = float(np.mean(returns > 0))
    down_frac = float(np.mean(returns < 0))
    majority_acc = max(up_frac, down_frac)
    return {
        "majority_class_accuracy": majority_acc,
        "pct_up": up_frac,
        "pct_down": down_frac,
        "majority_class": "up" if up_frac >= down_frac else "down",
    }


def compute_transaction_cost(
    predictions: np.ndarray, cost_bps: float = 10.0
) -> float:
    """Estimate transaction costs from position changes."""
    if len(predictions) < 2:
        return 0.0
    trades = np.sum(np.diff(np.sign(predictions)) != 0)
    return trades * cost_bps / 10000.0


def ensure_kronos_repo(repo_path: Path) -> Path:
    """Clone the Kronos source repo if not already present.

    Kronos has no PyPI wheel; its ``model`` package must be on sys.path. We
    shallow-clone the official repo to a local cache (idempotent). Override
    the location with --kronos-repo or the KRONOS_REPO env var.
    """
    repo_path = Path(repo_path)
    if (repo_path / "model" / "__init__.py").exists():
        return repo_path
    repo_path.parent.mkdir(parents=True, exist_ok=True)
    print(f"[ensure_kronos_repo] cloning {KRONOS_REPO_URL} -> {repo_path}")
    subprocess.run(
        ["git", "clone", "--depth", "1", KRONOS_REPO_URL, str(repo_path)],
        check=True,
    )
    return repo_path


def load_kronos_model(
    model_size: str = "base",
    device: str = "auto",
    kronos_repo: Path | None = None,
):
    """Load the real Kronos predictor from the source repo.

    Returns a ``KronosWrapper`` when the repo + deps are available. Falls back
    to ``NaiveKronosWrapper`` only when the package/deps are missing (dry-run /
    CI). The ``is_mock`` flag makes a mock result unambiguous, so a committed
    real result MUST carry ``is_mock=False`` (sota-not-workaround Prong A: the
    naive fallback is never a substitute for a committed SOTA result).
    """
    model_id = KRONOS_MODEL_IDS.get(model_size, KRONOS_MODEL_IDS["base"])
    try:
        repo = ensure_kronos_repo(kronos_repo or KRONOS_REPO_DEFAULT)
        repo_str = str(repo.resolve())
        if repo_str not in sys.path:
            sys.path.insert(0, repo_str)
        from model import Kronos, KronosPredictor, KronosTokenizer

        tokenizer = KronosTokenizer.from_pretrained(KRONOS_TOKENIZER_ID)
        model = Kronos.from_pretrained(model_id)
        if device and device != "auto":
            try:
                model = model.to(device)
            except Exception:
                pass  # device placement is best-effort; predictor handles it
        predictor = KronosPredictor(model, tokenizer, max_context=512)
        return KronosWrapper(predictor, model_id=model_id)
    except Exception as exc:
        print(
            f"[WARN] real Kronos unavailable ({type(exc).__name__}: {exc}); "
            "falling back to NaiveKronosWrapper (mock). Install the Kronos "
            "source repo + torch/einops/safetensors for real evaluation."
        )
        return NaiveKronosWrapper(model_id=model_id)


class KronosWrapper:
    """Wrapper around the real KronosPredictor (OHLCV DataFrame I/O)."""

    def __init__(self, predictor, model_id: str = ""):
        self.predictor = predictor
        self.model_id = model_id

    def predict(
        self,
        context_ohlcv: pd.DataFrame,
        x_timestamp,
        y_timestamp,
        pred_len: int = 24,
        seed: int | None = None,
    ) -> np.ndarray:
        """Generate a zero-shot close-price forecast.

        Parameters
        ----------
        context_ohlcv : DataFrame with lowercase open/high/low/close[/volume]
            columns, length == lookback (<=512).
        x_timestamp, y_timestamp : DatetimeIndex / Series aligned to the
            context and the forecast horizon (required by KronosPredictor).
        pred_len : forecast horizon length.
        seed : if set, seeds torch + numpy before the sampling forward pass
            (Kronos samples autoregressively, so the seed materially changes
            the forecast -- unlike deterministic Chronos-Bolt).

        Returns
        -------
        np.ndarray, shape (pred_len,) -- forecast close prices.
        """
        import torch

        if seed is not None:
            torch.manual_seed(seed)
            np.random.seed(seed)

        pred_df = self.predictor.predict(
            df=context_ohlcv,
            x_timestamp=x_timestamp,
            y_timestamp=y_timestamp,
            pred_len=pred_len,
            T=1.0,
            top_p=0.9,
            sample_count=1,
            verbose=False,
        )
        # pred_df is a DataFrame with a 'close' column (forecast OHLCV)
        close = np.asarray(pred_df["close"].values, dtype=float)
        return close[:pred_len]

    @property
    def is_mock(self) -> bool:
        return False


class NaiveKronosWrapper:
    """Last-value persistence baseline. Dry-run / CI only (mock)."""

    def __init__(self, model_id: str = ""):
        self.model_id = model_id

    def predict(
        self,
        context_ohlcv: pd.DataFrame,
        x_timestamp=None,
        y_timestamp=None,
        pred_len: int = 24,
        seed: int | None = None,
    ) -> np.ndarray:
        last_close = float(context_ohlcv["close"].iloc[-1])
        return np.full(pred_len, last_close, dtype=float)

    @property
    def is_mock(self) -> bool:
        return True


def build_evaluation_windows(
    ohlcv_df: pd.DataFrame,
    seq_len: int = 96,
    pred_len: int = 24,
    n_windows: int = 5,
) -> list[dict]:
    """Build walk-forward evaluation windows from the OHLCV frame.

    Each window carries the Kronos inputs (OHLCV context + x_timestamp +
    y_timestamp) and the ground truth (actual close prices / returns) used to
    score direction accuracy and Sharpe.
    """
    close = ohlcv_df["close"]
    returns = close.pct_change().dropna()

    total_len = seq_len + pred_len
    if len(returns) < total_len + n_windows:
        n_windows = max(1, (len(returns) - total_len) // pred_len)

    windows = []
    start_idx = len(close) - total_len
    for i in range(n_windows):
        ctx_start = start_idx - i * pred_len
        if ctx_start < 0:
            break
        ctx_end = ctx_start + seq_len
        actual_end = ctx_end + pred_len

        ctx_ohlcv = ohlcv_df.iloc[ctx_start:ctx_end]
        actual_close = close.iloc[ctx_end:actual_end].values
        actual_rets = returns.iloc[
            ctx_end - 1 : actual_end - 1
        ].values  # align returns with forecast returns

        # Kronos calc_time_stamps expects a Series (uses .dt accessor), not a
        # DatetimeIndex, so wrap the index slices.
        x_ts = pd.Series(ohlcv_df.index[ctx_start:ctx_end])
        y_ts = pd.Series(ohlcv_df.index[ctx_end:actual_end])

        windows.append(
            {
                "context_ohlcv": ctx_ohlcv,
                "x_timestamp": x_ts,
                "y_timestamp": y_ts,
                "actual_close": actual_close,
                "actual_returns": actual_rets,
                "start_date": str(ohlcv_df.index[ctx_start]),
                "end_date": str(ohlcv_df.index[min(actual_end - 1, len(close) - 1)]),
            }
        )

    return list(reversed(windows))


def evaluate_window(
    model,
    window: dict,
    pred_len: int = 24,
    cost_bps: float = 10.0,
    seed: int | None = None,
) -> dict:
    """Evaluate model on a single window (direction + Sharpe after costs)."""
    context_ohlcv = window["context_ohlcv"]
    actual_close = window["actual_close"]
    actual_returns = window["actual_returns"]

    forecast = model.predict(
        context_ohlcv,
        x_timestamp=window["x_timestamp"],
        y_timestamp=window["y_timestamp"],
        pred_len=pred_len,
        seed=seed,
    )

    forecast_returns = np.diff(forecast) / forecast[:-1]
    min_len = min(len(forecast_returns), len(actual_returns))
    forecast_returns = forecast_returns[:min_len]
    actual_pred_returns = actual_returns[:min_len]

    dir_acc = compute_direction_accuracy(actual_pred_returns, forecast_returns)
    mse = float(np.mean((actual_close[: len(forecast)] - forecast) ** 2))

    strategy_returns = np.sign(forecast_returns) * actual_pred_returns
    tcost = compute_transaction_cost(forecast_returns, cost_bps=cost_bps)
    net_returns = strategy_returns - tcost / max(len(strategy_returns), 1)
    sharpe = sharpe_from_returns(net_returns)

    return {
        "direction_accuracy": dir_acc,
        "mse": mse,
        "sharpe": sharpe,
        "net_sharpe": sharpe_from_returns(net_returns),
        "n_trades": int(np.sum(np.diff(np.sign(forecast_returns)) != 0)),
        "transaction_cost_bps": tcost * 10000,
        "forecast_mean": float(np.mean(forecast)),
        "actual_mean": float(np.mean(actual_close)),
    }


def load_ohlcv(data_dir: Path, symbol: str) -> pd.DataFrame:
    """Load OHLCV and lowercase columns for Kronos (open/high/low/close/volume)."""
    df = load_data(data_dir, symbol=symbol)
    rename = {c: c.lower() for c in df.columns}
    df = df.rename(columns=rename)
    # Kronos requires open/high/low/close; volume optional (zero-filled inside)
    needed = ["open", "high", "low", "close"]
    missing = [c for c in needed if c not in df.columns]
    if missing:
        raise ValueError(f"{symbol}: missing OHLCV columns {missing}")
    if "volume" not in df.columns:
        df["volume"] = 0.0
    return df[["open", "high", "low", "close", "volume"]]


def run_multi_seed(args: argparse.Namespace, ohlcv_df=None, symbol=None) -> dict:
    """Multi-seed walk-forward validation (>=4 seeds).

    Kronos forward passes are stochastic (autoregressive sampling), so the
    cross-seed std is a genuine dispersion measure here -- NOT degenerate like
    Chronos-Bolt (C893-L). The BEATS gate (edge>0, mean_edge>=2*std, >=4 seeds)
    is therefore a real test rather than a collapsed artefact.
    """
    seeds = [int(s) for s in args.seeds.split(",")]
    symbol = symbol or args.symbol
    if ohlcv_df is None:
        ohlcv_df = load_ohlcv(Path(args.data_dir), symbol=symbol)

    close = ohlcv_df["close"]
    baseline = compute_majority_baseline(close.pct_change().dropna().values)

    windows = build_evaluation_windows(
        ohlcv_df, seq_len=args.seq_len, pred_len=args.pred_len, n_windows=args.n_windows
    )

    seed_results = []
    for seed in seeds:
        window_metrics = []
        for window in windows:
            m = evaluate_window(
                args._model, window, pred_len=args.pred_len,
                cost_bps=args.cost_bps, seed=seed,
            )
            window_metrics.append(m)
        avg_dir_acc = float(np.mean([m["direction_accuracy"] for m in window_metrics]))
        edge = avg_dir_acc - baseline["majority_class_accuracy"]
        seed_results.append({
            "seed": seed,
            "avg_direction_accuracy": avg_dir_acc,
            "majority_baseline": baseline["majority_class_accuracy"],
            "edge_vs_majority": float(edge),
            "avg_sharpe": float(np.mean([m["sharpe"] for m in window_metrics])),
        })
        verdict = "BEATS" if edge > 0 else "FAILS"
        print(
            f"  [{symbol} h={args.pred_len}] seed {seed}: "
            f"DirAcc={avg_dir_acc:.4f} Edge={edge:+.4f} [{verdict}]"
        )

    edges = np.array([r["edge_vs_majority"] for r in seed_results])
    mean_edge = float(np.mean(edges))
    std_edge = float(np.std(edges))
    n_beats = int(np.sum(edges > 0))
    beats_valid = len(seeds) >= 4 and mean_edge > 0 and (
        std_edge < 1e-10 or mean_edge >= 2 * std_edge
    )

    return {
        "model": args._model.model_id,
        "is_mock": args._model.is_mock,
        "symbol": symbol,
        "pred_len": args.pred_len,
        "evaluation_type": "multi_seed",
        "seeds": seeds,
        "n_beats": n_beats,
        "n_seeds": len(seeds),
        "mean_edge": mean_edge,
        "std_edge": std_edge,
        "beats_valid": beats_valid,
        "majority_baseline": baseline,
        "seed_results": seed_results,
        "timestamp": datetime.now().isoformat(),
    }


def run_sweep(args: argparse.Namespace) -> dict:
    """Sweep symbols x horizons x seeds, consolidating into one results.json.

    Layout mirrors eval_chronos_bolt results.json (top-level metadata + a
    ``sweep`` list of per-config dicts) so the two foundation-model rungs can
    be compared directly in the verdict doc.
    """
    symbols = [s.strip() for s in args.symbols.split(",")]
    pred_lens = [int(p) for p in args.pred_lens.split(",")]

    sweep = []
    for symbol in symbols:
        try:
            ohlcv_df = load_ohlcv(Path(args.data_dir), symbol=symbol)
        except Exception as exc:
            print(f"[WARN] {symbol}: data load failed ({exc}), skipping")
            continue
        print(f"\n=== {symbol} ({len(ohlcv_df)} bars) ===")
        for pred_len in pred_lens:
            args.pred_len = pred_len
            res = run_multi_seed(args, ohlcv_df=ohlcv_df, symbol=symbol)
            sweep.append(res)
            print(
                f"  -> {symbol} h={pred_len}: mean_edge={res['mean_edge']:+.4f} "
                f"std={res['std_edge']:.4f} beats_valid={res['beats_valid']}"
            )

    summary = {
        "model": args._model.model_id,
        "is_mock": args._model.is_mock,
        "mode": "sweep",
        "seeds": [int(s) for s in args.seeds.split(",")],
        "n_seeds": len([int(s) for s in args.seeds.split(",")]),
        "cost_bps": args.cost_bps,
        "walk_forward_windows": args.n_windows,
        "seq_len": args.seq_len,
        "device": args.device,
        "sweep": sweep,
        "timestamp": datetime.now().isoformat(),
    }
    return summary


def main():
    parser = argparse.ArgumentParser(
        description="Kronos zero-shot evaluation on financial time series"
    )
    parser.add_argument("--mode", default="multiseed",
                        choices=["dry-run", "multiseed", "sweep"])
    parser.add_argument("--data-dir", default="../datasets/yfinance", type=str)
    parser.add_argument("--symbol", default="SPY", type=str)
    parser.add_argument("--symbols", default="SPY,TLT,GLD", type=str,
                        help="Comma-separated symbols for --mode sweep")
    parser.add_argument("--model-size", default="base", type=str,
                        choices=list(KRONOS_MODEL_IDS.keys()))
    parser.add_argument("--kronos-repo", default=str(KRONOS_REPO_DEFAULT), type=str)
    parser.add_argument("--seq-len", default=96, type=int)
    parser.add_argument("--pred-len", default=24, type=int)
    parser.add_argument("--pred-lens", default="24,66,132", type=str,
                        help="Comma-separated horizons for --mode sweep")
    parser.add_argument("--n-windows", default=5, type=int)
    parser.add_argument("--seeds", default="0,1,7,42,99", type=str)
    parser.add_argument("--cost-bps", default=10.0, type=float)
    parser.add_argument("--device", default="auto", type=str)
    parser.add_argument("--output-dir", default=None, type=str)
    args = parser.parse_args()

    if args.mode == "dry-run":
        args._model = NaiveKronosWrapper(model_id="naive:last-value")
        # synthetic close series for the dry-run smoke
        n_points = args.seq_len + args.pred_len + args.n_windows * args.pred_len + 10
        dates = pd.date_range("2020-01-01", periods=n_points, freq="B")
        rng = np.random.default_rng(42)
        ohlcv_df = pd.DataFrame(
            {
                "open": np.cumsum(rng.standard_normal(n_points) * 0.1 + 100),
                "high": 0.0, "low": 0.0,
                "close": np.cumsum(rng.standard_normal(n_points) * 0.1 + 100),
                "volume": 0.0,
            }, index=dates,
        )
        ohlcv_df["high"] = ohlcv_df[["open", "close"]].max(axis=1) + 0.5
        ohlcv_df["low"] = ohlcv_df[["open", "close"]].min(axis=1) - 0.5
        args.symbol = "SYNTHETIC"
        res = run_multi_seed(args, ohlcv_df=ohlcv_df, symbol="SYNTHETIC")
    else:
        print(f"Loading Kronos ({args.model_size}) from {args.kronos_repo}...")
        args._model = load_kronos_model(
            args.model_size, device=args.device,
            kronos_repo=Path(args.kronos_repo),
        )
        print(f"  Model: {args._model.model_id} (mock={args._model.is_mock})")
        res = run_sweep(args) if args.mode == "sweep" else run_multi_seed(args)

    if args.output_dir:
        out_path = Path(args.output_dir)
        out_path.mkdir(parents=True, exist_ok=True)
        tag = "sweep" if args.mode == "sweep" else f"{args.symbol}_{args.pred_len}"
        out_file = out_path / f"kronos_zeroshot_{tag}_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"
        with open(out_file, "w", encoding="utf-8") as f:
            json.dump(res, f, indent=2)
        print(f"  Saved to: {out_file}")

    print("\n=== Done ===")


if __name__ == "__main__":
    main()
