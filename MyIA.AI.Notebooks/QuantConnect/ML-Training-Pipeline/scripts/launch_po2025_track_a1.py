"""
po-2025 Track A1 — GPU Training on RTX 3080 Ti (17.2GB VRAM)

Thermal-safe training using shared/gpu_training.py utilities.
Downloads yfinance data if missing, then runs:
- Transformer SPY 2015-2024 (d=192, heads=8, layers=4, 200 epochs)
- DQN SPY (hidden=384, 300 episodes, replay=150K)
- LSTM SPY (hidden=384, layers=3, 150 epochs)

Conservative settings per postmortem (7 GPU crashes total):
- MAX_TEMP=80C (crash threshold ~96C, 16C margin)
- batch_size=32 (not 64, reduces instantaneous GPU load)
- AMP enabled (mixed precision, halves VRAM/heat)
- Intra-epoch thermal checks every 5 batches via nvidia-smi
"""

from __future__ import annotations

import os
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SCRIPTS = ROOT / "scripts"
DATA_DIR = ROOT.parent / "datasets" / "yfinance"


def download_yfinance_data(data_dir: Path, symbols: list[str], start: str, end: str) -> None:
    """Download OHLCV data via yfinance if not present."""
    import yfinance as yf

    data_dir.mkdir(parents=True, exist_ok=True)

    for symbol in symbols:
        existing = list(data_dir.glob(f"{symbol}_*.csv"))
        if existing:
            print(f"  {symbol}: already downloaded ({len(existing)} files)")
            continue

        print(f"  Downloading {symbol} {start} to {end}...")
        ticker = yf.Ticker(symbol)
        df = ticker.history(start=start, end=end, auto_adjust=True)
        if df.empty:
            print(f"  WARNING: No data for {symbol}")
            continue

        ts = datetime.now(timezone.utc).strftime("%Y%m%d")
        path = data_dir / f"{symbol}_{ts}.csv"
        df.to_csv(path)
        print(f"  {symbol}: {len(df)} rows -> {path.name}")


def main():
    ts = datetime.now(timezone.utc).strftime("%Y%m%d_%H%M%S")
    out_dir = ROOT / "outputs" / f"po2025_track_a1_{ts}"
    out_dir.mkdir(parents=True, exist_ok=True)

    print(f"[po-2025 Track A1] GPU Training Launcher (thermal-safe)")
    print(f"[po-2025 Track A1] Output dir: {out_dir}")

    # Step 1: Download data
    print("\n[Step 1] Downloading yfinance data...")
    symbols = ["SPY", "QQQ", "AAPL", "MSFT", "GOOG", "AMZN", "BTC-USD", "ETH-USD"]
    download_yfinance_data(DATA_DIR, symbols, "2015-01-01", "2024-12-31")

    # Step 2: Verify GPU
    import torch
    print(f"\n[Step 2] GPU check:")
    print(f"  Device: {torch.cuda.get_device_name(0)}")
    print(f"  VRAM: {torch.cuda.get_device_properties(0).total_memory / 1e9:.1f} GB")
    print(f"  CUDA: {torch.cuda.is_available()}")
    print(f"  torch: {torch.__version__}")

    # Verify thermal watchdog available
    sys.path.insert(0, str(ROOT.parent / "shared"))
    from gpu_training import get_gpu_temp
    temp = get_gpu_temp()
    print(f"  Current temp: {temp}C (MAX_TEMP=80C)")

    conda_python = sys.executable

    # Step 3: Launch training jobs — batch_size=32, thermal checks in each script
    jobs = [
        (
            "transformer-spy-192",
            [
                conda_python, str(SCRIPTS / "train_transformer.py"),
                "--data-dir", str(DATA_DIR),
                "--symbol", "SPY",
                "--start", "2015-01-01",
                "--end", "2024-12-31",
                "--d-model", "192",
                "--nhead", "8",
                "--num-layers", "4",
                "--dim-ff", "768",
                "--epochs", "200",
                "--batch-size", "32",
                "--seq-len", "30",
            ],
        ),
        (
            "dqn-spy-384",
            [
                conda_python, str(SCRIPTS / "train_dqn_rl.py"),
                "--data-dir", str(DATA_DIR),
                "--symbol", "SPY",
                "--start", "2015-01-01",
                "--end", "2024-12-31",
                "--hidden-size", "384",
                "--num-episodes", "300",
                "--replay-size", "150000",
                "--batch-size", "32",
            ],
        ),
        (
            "lstm-spy-384",
            [
                conda_python, str(SCRIPTS / "train_lstm.py"),
                "--data-dir", str(DATA_DIR),
                "--symbol", "SPY",
                "--start", "2015-01-01",
                "--end", "2024-12-31",
                "--hidden-size", "384",
                "--num-layers", "3",
                "--epochs", "150",
                "--batch-size", "32",
                "--seq-len", "30",
            ],
        ),
    ]

    print(f"\n[Step 3] Running {len(jobs)} training jobs (batch_size=32, thermal-safe)...")
    results = []

    for name, cmd in jobs:
        log_path = out_dir / f"{name}.log"
        start = time.time()
        print(f"\n[po-2025 Track A1] Running {name}...")

        with open(log_path, "w", encoding="utf-8") as f:
            f.write(f"# {name} START {datetime.now(timezone.utc).isoformat()}\n")
            f.write(f"# CMD: {' '.join(str(c) for c in cmd)}\n")
            f.write(f"# MAX_TEMP=80C, batch_size=32, AMP enabled\n\n")
            f.flush()
            proc = subprocess.run(cmd, stdout=f, stderr=subprocess.STDOUT, env={**os.environ})
            elapsed = time.time() - start
            f.write(f"\n# {name} END returncode={proc.returncode} elapsed={elapsed:.1f}s\n")

        rc = proc.returncode
        results.append((name, rc, elapsed))
        status = "OK" if rc == 0 else f"FAILED (rc={rc})"
        print(f"  -> {status} in {elapsed:.1f}s")

    # Step 4: Summary
    summary_path = out_dir / "summary.txt"
    with open(summary_path, "w", encoding="utf-8") as f:
        f.write(f"po-2025 Track A1 summary {datetime.now(timezone.utc).isoformat()}\n")
        f.write(f"GPU: {torch.cuda.get_device_name(0)} ({torch.cuda.get_device_properties(0).total_memory / 1e9:.1f} GB)\n")
        f.write(f"PyTorch: {torch.__version__}\n")
        f.write(f"MAX_TEMP: 80C, batch_size: 32\n\n")
        for name, rc, elapsed in results:
            f.write(f"  {name}: {'OK' if rc == 0 else 'FAILED'} rc={rc} elapsed={elapsed:.1f}s\n")

    print(f"\n[po-2025 Track A1] DONE. Summary: {summary_path}")

    all_ok = all(rc == 0 for _, rc, _ in results)
    return 0 if all_ok else 1


if __name__ == "__main__":
    sys.exit(main())
