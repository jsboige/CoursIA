"""Port local GPU du re-entrainement Chronos du livre (06/18/02, HandsOnAITradingBook e025f21).

Le livre entraine `amazon/chronos-t5-tiny` DANS l'algorithme LEAN (a chaque
rebalancement trimestriel, `_train_chronos` puis `ChronosPipeline.predict`).
Ce harnais sort le re-entrainement de l'algorithme pour l'executer sur un GPU
local, et compare modele de base et modele re-entraine hors echantillon :

  1. `--stage finetune` : re-entraine le modele par graine (recette du livre :
     context 126 j, prediction 63 j, lr 1e-5, adamw_torch_fused, batch 32,
     accumulation 2, tf32 Ampere). Ecarts documentes : `max_steps` configurable
     (le livre utilise 3, budget de runtime cloud) et `torch_compile=False`
     (portabilite Windows).
  2. `--stage eval` : erreur de prevision hors echantillon (2022-2026) par
     origine trimestrielle — MAE, MASE (naif m=1 sur la fenetre reelle) et
     WQL (quantiles 0.1/0.25/0.5/0.75/0.9, forme publiee normalisee par
     somme|a|), modele de base vs re-entraine, meme graine de tirage pour
     les deux bras (appariement par origine).
  3. Test de Diebold-Mariano apparie par origine (origines trimestrielles
     NON chevauchantes) sur la perte MAE.
  4. Simulation locale de la strategie du livre (poids SLSQP maximisant le
     Sharpe des courbes prevues, long-only, rebalancement trimestriel, couts
     5 bps sur le turnover) sur la fenetre OOS, pour les deux bras.

Donnees : cloture ajustee quotidienne (yfinance) de 5 mega-caps US, cache
local. Univers fixe (AAPL, MSFT, NVDA, AMZN, GOOGL) — ecart documente vs la
selection dynamique top-5 dollar-volume du livre (indisponible hors QC).

Usage :
    set CUDA_VISIBLE_DEVICES=1   # enumeration torch par defaut : 1 = 3080 Ti (libre)
    python run_finetune_chronos.py --stage all --seeds 1 2 3 42 --run-dir D:\\Dev\\CoursIA-18962-run
"""

from __future__ import annotations

import argparse
import json
import logging
import math
import os
import sys
import time
from ast import literal_eval
from functools import partial
from pathlib import Path

import numpy as np
import pandas as pd
import torch

FINETUNE_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(FINETUNE_DIR))

from chronos_training import (  # noqa: E402  (vendored v2.3.2, voir en-tete du fichier)
    ChronosDataset,
    has_enough_observations,
    load_model,
)

from chronos import ChronosConfig, ChronosPipeline  # noqa: E402
from gluonts.dataset.pandas import PandasDataset  # noqa: E402
from gluonts.itertools import Filter  # noqa: E402
from scipy.optimize import minimize  # noqa: E402
from transformers import Trainer, TrainingArguments, set_seed  # noqa: E402

UNIVERSE = ["AAPL", "MSFT", "NVDA", "AMZN", "GOOGL"]
DATA_START = "2016-01-01"
TRAIN_END = "2021-12-31"
OOS_START = "2022-01-01"
CONTEXT_LENGTH = 126
PREDICTION_LENGTH = 63
NUM_SAMPLES = 20
BASE_MODEL = "amazon/chronos-t5-tiny"
QUANTILES = [0.1, 0.25, 0.5, 0.75, 0.9]
COST_BPS = 5.0


def log(msg: str) -> None:
    print(f"[{time.strftime('%H:%M:%S')}] {msg}", flush=True)


def device_banner() -> str:
    """Imprime le GPU reellement selectionne (l'index torch ne suit pas nvidia-smi)."""
    if not torch.cuda.is_available():
        raise SystemExit("CUDA indisponible — verifier l'env (bonsai) et le pilote.")
    name = torch.cuda.get_device_name(0)
    props = torch.cuda.get_device_properties(0)
    log(f"GPU: {name} ({props.total_memory / 2**30:.1f} GiB) — "
        f"CUDA_VISIBLE_DEVICES={os.environ.get('CUDA_VISIBLE_DEVICES', '(non pose)')}")
    return name


def load_prices(run_dir: Path) -> pd.DataFrame:
    cache = run_dir / "data" / "closes.csv"
    if cache.exists():
        df = pd.read_csv(cache, index_col=0, parse_dates=True)
        log(f"donnees: cache {cache} ({df.shape[0]} j x {df.shape[1]} series)")
        return df
    import yfinance as yf

    log("donnees: telechargement yfinance...")
    raw = yf.download(UNIVERSE, start=DATA_START, interval="1d", auto_adjust=True, progress=False)
    df = raw["Close"][UNIVERSE].dropna(how="all")
    cache.parent.mkdir(parents=True, exist_ok=True)
    df.to_csv(cache)
    log(f"donnees: {df.shape[0]} j x {df.shape[1]} series -> {cache}")
    return df


def build_training_frames(prices: pd.DataFrame) -> list[pd.DataFrame]:
    """Frames d'entrainement au format du livre : index quotidien calendaire (asfreq)."""
    train = prices.loc[:TRAIN_END]
    frames = []
    for symbol in UNIVERSE:
        s = train[symbol].dropna()
        frame = s.reset_index()
        frame.columns = ["time", "target"]
        frame["time"] = pd.to_datetime(frame["time"])
        frames.append(frame.set_index("time").resample("D").asfreq())
    return frames


def train_chronos(training_data, output_dir: Path, seed: int, max_steps: int,
                  context_length: int = CONTEXT_LENGTH, prediction_length: int = PREDICTION_LENGTH,
                  min_past: int = 64, per_device_train_batch_size: int = 32,
                  learning_rate: float = 1e-5, optim: str = "adamw_torch_fused",
                  gradient_accumulation_steps: int = 2, model_id: str = BASE_MODEL,
                  model_type: str = "seq2seq", tf32: bool = True,
                  torch_compile: bool = False) -> Path:
    """Corps de `_train_chronos` du livre (06/18/02), hors algorithme, seed parametrable."""
    import chronos_training as chronos_train_module

    chronos_train_module.logger = logging.getLogger()
    chronos_train_module.logger.setLevel(logging.INFO)
    output_dir = Path(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)

    probabilities = [1.0 / len(training_data)] * len(training_data)
    tokenizer_kwargs = literal_eval("{'low_limit': -15.0, 'high_limit': 15.0}")
    set_seed(seed, True)

    train_datasets = [
        Filter(
            partial(has_enough_observations, min_length=min_past + prediction_length, max_missing_prop=0.9),
            PandasDataset(data_frame, freq="D"),
        )
        for data_frame in training_data
    ]
    model = load_model(model_id=model_id, model_type=model_type, vocab_size=4096,
                       random_init=False, tie_embeddings=False, pad_token_id=0, eos_token_id=1)
    chronos_config = ChronosConfig(
        tokenizer_class="MeanScaleUniformBins", tokenizer_kwargs=tokenizer_kwargs,
        n_tokens=4096, n_special_tokens=2, pad_token_id=0, eos_token_id=1,
        use_eos_token=True, model_type=model_type, context_length=context_length,
        prediction_length=prediction_length, num_samples=NUM_SAMPLES,
        temperature=1.0, top_k=50, top_p=1.0,
    )
    model.config.chronos_config = chronos_config.__dict__
    shuffled = ChronosDataset(
        datasets=train_datasets, probabilities=probabilities,
        tokenizer=chronos_config.create_tokenizer(), context_length=context_length,
        prediction_length=prediction_length, min_past=min_past, mode="training",
    ).shuffle(100)

    args = TrainingArguments(
        output_dir=str(output_dir), per_device_train_batch_size=per_device_train_batch_size,
        learning_rate=learning_rate, lr_scheduler_type="linear", warmup_ratio=0.0,
        optim=optim, logging_dir=str(output_dir / "train-logs"), logging_strategy="steps",
        logging_steps=25, save_strategy="no", report_to=[], max_steps=max_steps,
        gradient_accumulation_steps=gradient_accumulation_steps, dataloader_num_workers=1,
        tf32=tf32, torch_compile=torch_compile, ddp_find_unused_parameters=False,
        remove_unused_columns=False, seed=seed,
    )
    Trainer(model=model, args=args, train_dataset=shuffled).train()
    model.save_pretrained(output_dir)
    return output_dir


def quarter_origins(index: pd.DatetimeIndex, warmup: int) -> list[pd.Timestamp]:
    """Premier jour de bourse de chaque trimestre de la fenetre OOS, apres warmup."""
    seen, origins = set(), []
    for i, ts in enumerate(index):
        if ts < pd.Timestamp(OOS_START) or i < warmup:
            continue
        key = (ts.year, (ts.month - 1) // 3)
        if key not in seen:
            seen.add(key)
            origins.append(ts)
    while origins and index.get_loc(origins[-1]) + PREDICTION_LENGTH >= len(index):
        origins.pop()
    return origins


def forecast_quantiles(pipeline: ChronosPipeline, context: np.ndarray, seed: int) -> dict:
    torch.manual_seed(seed)
    samples = pipeline.predict([torch.tensor(context, dtype=torch.float32)],
                               PREDICTION_LENGTH, num_samples=NUM_SAMPLES)
    arr = samples[0].float().cpu().numpy()
    return {q: np.quantile(arr, q, axis=0) for q in QUANTILES}


def metrics_for_origin(med: np.ndarray, quants: dict, actual: np.ndarray) -> dict:
    mae = float(np.mean(np.abs(med - actual)))
    naive_den = float(np.mean(np.abs(np.diff(actual)))) if len(actual) > 1 else float("nan")
    mase = mae / naive_den if naive_den else float("nan")
    denom = float(np.sum(np.abs(actual))) or 1.0
    wql = float(np.mean([
        2.0 * np.sum(np.maximum(q * (actual - quants[q]), (1 - q) * (quants[q] - actual))) / denom
        for q in QUANTILES
    ]))
    return {"mae": mae, "mase": mase, "wql": wql}


def dm_test(loss_a: np.ndarray, loss_b: np.ndarray) -> dict:
    """Diebold-Mariano apparie (origines non chevauchantes) sur loss_a - loss_b."""
    d = np.asarray(loss_a) - np.asarray(loss_b)
    n = len(d)
    mean_d = float(np.mean(d))
    sd = float(np.std(d, ddof=1)) if n > 1 else float("nan")
    if not sd or math.isnan(sd):
        return {"mean_diff": mean_d, "dm_stat": float("nan"), "dm_p": float("nan"), "n": n}
    stat = mean_d / (sd / math.sqrt(n))
    p = math.erfc(abs(stat) / math.sqrt(2))
    return {"mean_diff": mean_d, "dm_stat": float(stat), "dm_p": float(p), "n": n}


def optimize_weights(forecast_df: pd.DataFrame) -> np.ndarray:
    """Poids SLSQP du livre : maximise le Sharpe des courbes prevues, long-only, somme=1."""
    returns = forecast_df.pct_change().dropna()
    n = returns.shape[1]

    def neg_sharpe(weights):
        mean_returns = returns.mean() * 252
        cov = returns.cov() * 252
        port_ret = float(np.sum(mean_returns * weights))
        port_std = float(np.sqrt(np.dot(weights.T, np.dot(cov, weights))))
        return -(port_ret / port_std) if port_std > 0 else 0.0

    res = minimize(neg_sharpe, n * [1.0 / n], method="SLSQP",
                   bounds=tuple((0, 1) for _ in range(n)),
                   constraints=({"type": "eq", "fun": lambda w: np.sum(w) - 1}))
    return res.x


def simulate_strategy(pairs: list[tuple[np.ndarray, np.ndarray]]) -> dict:
    """Chaine les rebalancements (poids, rendements realises) avec couts sur le turnover."""
    equity, prev_w, rets = 1.0, np.zeros(len(UNIVERSE)), []
    for w, realized in pairs:
        turnover = float(np.sum(np.abs(w - prev_w)))
        r = float(np.dot(w, realized)) - turnover * COST_BPS / 1e4
        equity *= 1.0 + r
        rets.append(r)
        prev_w = w
    stats = curve_stats(rets)
    stats["n_rebalances"] = len(rets)
    return stats


def curve_stats(returns: list) -> dict:
    r = np.asarray(returns)
    if len(r) < 2:
        return {"sharpe": float("nan"), "cagr": float("nan"), "max_dd": float("nan"), "final_equity": float("nan")}
    equity = np.cumprod(1 + r)
    years = len(r) / 4.0
    cagr = float(equity[-1] ** (1 / years) - 1) if years > 0 else float("nan")
    sd = float(np.std(r, ddof=1))
    sharpe = float(np.mean(r) / sd * math.sqrt(4)) if sd > 0 else float("nan")
    peak = np.maximum.accumulate(equity)
    return {"sharpe": sharpe, "cagr": cagr, "max_dd": float(np.min(equity / peak - 1)),
            "final_equity": float(equity[-1])}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--stage", choices=["finetune", "eval", "all"], default="all")
    ap.add_argument("--seeds", type=int, nargs="+", default=[1, 2, 3, 42])
    ap.add_argument("--max-steps", type=int, default=300)
    ap.add_argument("--run-dir", type=str, required=True)
    ap.add_argument("--smoke", action="store_true")
    args = ap.parse_args()

    run_dir = Path(args.run_dir)
    (run_dir / "models").mkdir(parents=True, exist_ok=True)
    (run_dir / "results").mkdir(parents=True, exist_ok=True)

    device_banner()
    prices = load_prices(run_dir)
    index = prices.index
    origins = quarter_origins(index, warmup=CONTEXT_LENGTH + 1)
    if args.smoke:
        origins = origins[:1]
        args.seeds = args.seeds[:1]
        args.max_steps = min(args.max_steps, 20)
    log(f"origines OOS: {len(origins)} ({origins[0].date()} -> {origins[-1].date()})")

    summary = {"config": {
        "universe": UNIVERSE, "train_end": TRAIN_END, "oos_start": OOS_START,
        "context": CONTEXT_LENGTH, "prediction": PREDICTION_LENGTH,
        "max_steps": args.max_steps, "seeds": args.seeds, "cost_bps": COST_BPS,
        "base_model": BASE_MODEL, "rows": int(len(prices)),
    }, "seeds": {}}

    for seed in args.seeds:
        seed_dir = run_dir / "models" / f"seed-{seed}"
        if args.stage in ("finetune", "all") and not (seed_dir / "config.json").exists():
            t0 = time.time()
            log(f"graine {seed}: re-entrainement ({args.max_steps} pas)...")
            train_chronos(build_training_frames(prices), seed_dir, seed=seed, max_steps=args.max_steps)
            log(f"graine {seed}: entraine en {time.time() - t0:.0f} s")

        if args.stage not in ("eval", "all"):
            continue

        log(f"graine {seed}: evaluation base vs re-entraine sur {len(origins)} origines")
        base_pipe = ChronosPipeline.from_pretrained(BASE_MODEL, device_map="cuda", torch_dtype=torch.bfloat16)
        ft_pipe = ChronosPipeline.from_pretrained(str(seed_dir), device_map="cuda", torch_dtype=torch.bfloat16)
        per_origin, strat_pairs = [], {"base": [], "finetuned": []}
        for k, origin in enumerate(origins):
            i = index.get_loc(origin)
            ctx = prices.iloc[i - CONTEXT_LENGTH:i][UNIVERSE].values
            act = prices.iloc[i:i + PREDICTION_LENGTH][UNIVERSE].values
            realized = prices.iloc[i + PREDICTION_LENGTH][UNIVERSE].values / prices.iloc[i][UNIVERSE].values - 1.0
            row = {"origin": str(origin.date())}
            for arm, pipe in (("base", base_pipe), ("finetuned", ft_pipe)):
                med = np.empty((PREDICTION_LENGTH, len(UNIVERSE)))
                per_asset = []
                for j in range(len(UNIVERSE)):
                    qs = forecast_quantiles(pipe, ctx[:, j], seed=seed * 1000 + k)
                    med[:, j] = qs[0.5]
                    per_asset.append(metrics_for_origin(med[:, j], qs, act[:, j]))
                row[arm] = {kk: float(np.mean([m[kk] for m in per_asset])) for kk in ("mae", "mase", "wql")}
                strat_pairs[arm].append((optimize_weights(pd.DataFrame(med, columns=UNIVERSE)), realized))
            per_origin.append(row)
            log(f"  {origin.date()}: MAE base {row['base']['mae']:.4f} / ft {row['finetuned']['mae']:.4f}")

        dm = dm_test([r["base"]["mae"] for r in per_origin], [r["finetuned"]["mae"] for r in per_origin])
        strat = {arm: simulate_strategy(pairs) for arm, pairs in strat_pairs.items()}
        entry = {"per_origin": per_origin, "dm": dm, "strategy": strat}
        summary["seeds"][str(seed)] = entry
        with open(run_dir / "results" / f"seed-{seed}.json", "w", encoding="utf-8") as fh:
            json.dump(entry, fh, indent=1)
        log(f"graine {seed}: DM stat {dm['dm_stat']:.3f} p {dm['dm_p']:.4f} "
            f"(MAE base-ft {dm['mean_diff']:+.5f}) | strat Sharpe base {strat['base']['sharpe']:.3f} "
            f"ft {strat['finetuned']['sharpe']:.3f}")

    with open(run_dir / "results" / "summary.json", "w", encoding="utf-8") as fh:
        json.dump(summary, fh, indent=1)
    log(f"resultats ecrits dans {run_dir / 'results'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
