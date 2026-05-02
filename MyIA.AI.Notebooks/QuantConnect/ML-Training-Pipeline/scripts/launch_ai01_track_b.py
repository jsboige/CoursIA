"""
ai-01 Track B — Hyperparameter sweep on RTX 4090 24GB (GPU 2)

Sequential training of 4 models with larger architectures than po-2023 baselines:
- Transformer SPY 2015-2025 (d=256, heads=8, layers=6, 100 epochs)
- LSTM SPY (hidden=512, layers=4, 100 epochs)
- DQN GPU (hidden=512, 500 episodes)
- XGBoost classification (1000 trees, depth 12)

Logs to outputs/ai01_track_b_<timestamp>/. Saves all checkpoints in checkpoints/<model>/<timestamp>/.
"""

from __future__ import annotations

import os
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

os.environ["CUDA_VISIBLE_DEVICES"] = "2"

ROOT = Path(__file__).resolve().parent.parent
SCRIPTS = ROOT / "scripts"
DATA_DIR = ROOT.parent / "datasets" / "yfinance"
PYTHON = r"C:\Users\MYIA\miniconda3\envs\coursia-ml-training\python.exe"

ts = datetime.now(timezone.utc).strftime("%Y%m%d_%H%M%S")
OUT_DIR = ROOT / "outputs" / f"ai01_track_b_{ts}"
OUT_DIR.mkdir(parents=True, exist_ok=True)

JOBS = [
    (
        "transformer-spy",
        [
            PYTHON, str(SCRIPTS / "train_transformer.py"),
            "--data-dir", str(DATA_DIR),
            "--symbol", "SPY",
            "--start", "2015-01-01",
            "--end", "2024-12-31",
            "--d-model", "256",
            "--nhead", "8",
            "--num-layers", "6",
            "--dim-ff", "1024",
            "--epochs", "100",
            "--batch-size", "64",
            "--seq-len", "30",
        ],
    ),
    (
        "lstm-spy",
        [
            PYTHON, str(SCRIPTS / "train_lstm.py"),
            "--data-dir", str(DATA_DIR),
            "--symbol", "SPY",
            "--start", "2015-01-01",
            "--end", "2024-12-31",
            "--hidden-size", "512",
            "--num-layers", "4",
            "--epochs", "100",
            "--batch-size", "64",
            "--seq-len", "30",
        ],
    ),
    (
        "dqn-spy",
        [
            PYTHON, str(SCRIPTS / "train_dqn_rl.py"),
            "--data-dir", str(DATA_DIR),
            "--symbol", "SPY",
            "--start", "2015-01-01",
            "--end", "2024-12-31",
            "--hidden-size", "512",
            "--num-episodes", "500",
            "--replay-size", "200000",
            "--batch-size", "128",
        ],
    ),
    (
        "xgb-spy",
        [
            PYTHON, str(SCRIPTS / "train_classification.py"),
            "--data-dir", str(DATA_DIR),
            "--symbol", "SPY",
            "--start", "2015-01-01",
            "--end", "2024-12-31",
            "--model", "xgboost",
            "--n-estimators", "1000",
            "--max-depth", "12",
        ],
    ),
]


def main():
    summary_path = OUT_DIR / "summary.txt"
    print(f"[ai-01 Track B] Starting {len(JOBS)} jobs")
    print(f"[ai-01 Track B] Output dir: {OUT_DIR}")
    print(f"[ai-01 Track B] CUDA_VISIBLE_DEVICES=2 (RTX 4090)")
    print()

    results = []
    for name, cmd in JOBS:
        log_path = OUT_DIR / f"{name}.log"
        start = time.time()
        print(f"[ai-01 Track B] Running {name}...")
        with open(log_path, "w", encoding="utf-8") as f:
            f.write(f"# {name} START {datetime.now(timezone.utc).isoformat()}\n")
            f.write(f"# CMD: {' '.join(cmd)}\n\n")
            f.flush()
            proc = subprocess.run(cmd, stdout=f, stderr=subprocess.STDOUT, env={**os.environ, "CUDA_VISIBLE_DEVICES": "2"})
            elapsed = time.time() - start
            f.write(f"\n# {name} END returncode={proc.returncode} elapsed={elapsed:.1f}s\n")
        results.append((name, proc.returncode, elapsed))
        print(f"  -> rc={proc.returncode} elapsed={elapsed:.1f}s log={log_path.name}")

    with open(summary_path, "w", encoding="utf-8") as f:
        f.write(f"ai-01 Track B summary {datetime.now(timezone.utc).isoformat()}\n\n")
        for name, rc, elapsed in results:
            f.write(f"  {name}: rc={rc} elapsed={elapsed:.1f}s\n")

    print()
    print(f"[ai-01 Track B] DONE. Summary: {summary_path}")
    return 0 if all(rc == 0 for _, rc, _ in results) else 1


if __name__ == "__main__":
    sys.exit(main())
