"""M8 — SOTA sequence transformers vs HAR baseline (overnight sweep).

Generalisation des resultats M5/M6/M7 (multiscale GNN NO BEATS HAR sur BTC/ETH
volatilite log-RV) a 4 architectures SOTA pour repondre :

  Question : est-ce que TFT, Mamba, iTransformer, ou PatchTST battent HAR
  sur le meme task ou est-ce qu'aucune architecture sequence-to-one ne suffit ?

Setup (apples-to-apples avec M7) :
  - Coins   : BTC-USD, ETH-USD (panier crypto 2018-2026)
  - Horizons : 1, 5, 10 (M7 a teste 1..30, 1 et 5 sont les plus pertinents)
  - Seeds   : 0, 1, 7, 42 (4 seeds, baseline statistique honnete)
  - WF      : 5 splits, gap=24h (24 heures), seq-len=60
  - Epochs  : 250 (M7 verdict invariant entre 1000 et 2000 epochs, donc 250 suffit)
  - GPU     : CUDA_VISIBLE_DEVICES=2 (RTX 4090 #2)

Total : 4 modeles x 2 coins x 3 horizons = 24 combos.
Estim. : 24 * ~14 min = ~5.6h overnight.

Sortie : results/m8_sota_overnight/<model>_<coin>_h<H>.json + _overall.log + _verdict.md

Verdict criterion (per combo) : edge cross-seed >= 2 * std vs HAR_mse_combo.
- BEATS HAR : edge >= +2 sigma
- NO BEATS  : edge <= -2 sigma
- INCONCLUSIVE : |edge| < 2 sigma
"""
from __future__ import annotations
import json, os, subprocess, sys, time
from datetime import datetime
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parent
PIPELINE = SCRIPTS.parent
RESULTS = PIPELINE / "results" / "m8_sota_overnight"
RESULTS.mkdir(parents=True, exist_ok=True)
OVERALL = RESULTS / "_overall.log"
PYTHON = r"C:\Users\MYIA\miniconda3\envs\coursia-ml-training\python.exe"
DATA_DIR = (PIPELINE.parent / "datasets" / "yfinance" / "crypto_panier").as_posix()

MODELS = [
    ("tft", "train_tft.py"),
    ("mamba", "train_mamba.py"),
    ("itransformer", "train_itransformer.py"),
    ("patchtst", "train_patchtst.py"),
]
COINS = ["BTC-USD", "ETH-USD"]
HORIZONS = [1, 5, 10]
SEEDS = "0,1,7,42"
N_SPLITS = 5
SEQ_LEN = 60
EPOCHS = 250


def log(msg: str) -> None:
    line = f"[{datetime.now().isoformat(timespec='seconds')}] {msg}"
    print(line, flush=True)
    with OVERALL.open("a", encoding="utf-8") as f:
        f.write(line + "\n")


def run_one(model_name: str, script: str, coin: str, horizon: int) -> dict:
    """Run a single (model, coin, horizon) combo with all seeds + WF."""
    out_dir = RESULTS / f"{model_name}_{coin.replace('-','_')}_h{horizon}"
    out_dir.mkdir(parents=True, exist_ok=True)
    log_file = out_dir / "training.log"
    cmd = [
        PYTHON, str(SCRIPTS / script),
        "--data-dir", DATA_DIR,
        "--symbols", coin,
        "--start", "2020-01-01",
        "--end", "2026-05-01",
        "--seq-len", str(SEQ_LEN),
        "--pred-len", str(horizon),
        "--epochs", str(EPOCHS),
        "--batch-size", "64",
        "--walk-forward",
        "--n-splits", str(N_SPLITS),
        "--seeds", SEEDS,
        "--output-dir", str(out_dir),
    ]
    env = os.environ.copy()
    env["CUDA_VISIBLE_DEVICES"] = "2"
    env["PYTHONUNBUFFERED"] = "1"
    t0 = time.time()
    try:
        with log_file.open("w", encoding="utf-8") as fh:
            proc = subprocess.run(cmd, stdout=fh, stderr=subprocess.STDOUT, env=env, timeout=3600)
        elapsed = time.time() - t0
        return {"exit": proc.returncode, "elapsed_s": elapsed, "log": str(log_file)}
    except subprocess.TimeoutExpired:
        elapsed = time.time() - t0
        return {"exit": -1, "elapsed_s": elapsed, "log": str(log_file), "error": "TIMEOUT"}
    except Exception as e:
        elapsed = time.time() - t0
        return {"exit": -2, "elapsed_s": elapsed, "log": str(log_file), "error": str(e)}


def main() -> int:
    log(f"=== M8 SOTA sweep START ({len(MODELS)} models x {len(COINS)} coins x {len(HORIZONS)} horizons) ===")
    log(f"Configuration: epochs={EPOCHS} seeds={SEEDS} n_splits={N_SPLITS} seq_len={SEQ_LEN}")
    log(f"Output dir: {RESULTS}")

    summary_file = RESULTS / "_summary.json"
    summary: list = []
    completed: set = set()
    if summary_file.exists():
        try:
            summary = json.loads(summary_file.read_text(encoding="utf-8"))
            completed = {(r["model"], r["coin"], r["horizon"]) for r in summary if r.get("exit") == 0}
            if completed:
                log(f"Resume: {len(completed)} combos already OK in _summary.json, will skip")
        except Exception as e:
            log(f"Resume: failed to load _summary.json ({e}), starting fresh")
            summary = []
            completed = set()

    total = len(MODELS) * len(COINS) * len(HORIZONS)
    idx = 0
    for model_name, script in MODELS:
        for coin in COINS:
            for h in HORIZONS:
                idx += 1
                tag = f"{model_name}/{coin}/h{h}"
                if (model_name, coin, h) in completed:
                    log(f"[{idx}/{total}] SKIP  {tag} (already OK)")
                    continue
                log(f"[{idx}/{total}] START {tag}")
                result = run_one(model_name, script, coin, h)
                result.update({"model": model_name, "coin": coin, "horizon": h})
                summary.append(result)
                status = "OK" if result["exit"] == 0 else f"FAIL exit={result['exit']}"
                log(f"[{idx}/{total}] END   {tag} {status} ({result['elapsed_s']:.0f}s)")
                # incremental flush
                with summary_file.open("w", encoding="utf-8") as f:
                    json.dump(summary, f, indent=2)

    log(f"=== M8 SOTA sweep DONE: {sum(1 for r in summary if r['exit']==0)}/{total} OK ===")
    return 0


if __name__ == "__main__":
    sys.exit(main())
