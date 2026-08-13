# ML Training Launchers

Detached GPU training jobs on ai-01 (RTX 4090, GPU 2). Available as PowerShell (`.ps1`, Windows-native) and bash (`.sh`, Mac/Linux-native) companions.

Each launcher handles environment setup, pre-checks, metadata logging, and starts the training process in the background with output redirection.

## Available Launchers

| Script (`.ps1`) | Script (`.sh`) | Model | Key Config | ETA |
|-----------------|----------------|-------|------------|-----|
| `launch_ai01_lstm_run5.ps1` | `launch_ai01_lstm_run5.sh` | LSTM | h=384, layers=4, epochs=100, batch=64 | ~30-50 min |
| `launch_ai01_lstm_run7_h512.ps1` | `launch_ai01_lstm_run7_h512.sh` | LSTM | h=512, layers=4, epochs=150, batch=64 | ~5-10 min |
| `launch_ai01_transformer_run6.ps1` | `launch_ai01_transformer_run6.sh` | Transformer | d=384, heads=8, layers=8, epochs=200, batch=32 | ~60-90 min |

All use `--advanced` features (19 indicators) and SPY 2015-2024 data.

The `run_m7_overnight_sweep.{ps1,sh}` (sibling of `launchers/`) runs 4 multi-scale GNN robustness sweeps sequentially overnight.

## Usage — Windows (PowerShell)

```powershell
# Full training (detached, logs to file)
.\launch_ai01_lstm_run5.ps1

# Quick validation (synthetic data, 2 epochs)
.\launch_ai01_lstm_run5.ps1 -DryRun

# Transformer training
.\launch_ai01_transformer_run6.ps1
.\launch_ai01_transformer_run6.ps1 -DryRun
```

## Usage — macOS / Linux (bash)

```bash
# Full training (detached, logs to file)
./launch_ai01_lstm_run5.sh

# Quick validation (synthetic data, 2 epochs)
./launch_ai01_lstm_run5.sh --dry-run
```

Prerequisites on Mac/Linux:
- `conda` (Miniconda or Anaconda) on `PATH`, **or** `CONDA_PREFIX` set if a conda env is already activated.
- The `coursia-ml-training` conda env with torch + pandas + numpy installed.
- `nvidia-smi` and an NVIDIA driver (only required for actual training, not `--dry-run`).
- `bash >= 4`.

The bash launcher resolves the Python interpreter via `CONDA_PREFIX` if set, otherwise via `conda env list`. This matches the PowerShell script's `$CondaEnv = "coursia-ml-training"` + explicit Python path.

## Monitoring

### Windows

```powershell
# Follow training log
Get-Content outputs\ai01_lstm_run5_<timestamp>\train.log -Wait

# GPU utilization (refresh every 5s)
nvidia-smi -i 2 -l 5

# Check if process is still running
Get-Process -Id (Get-Content outputs\ai01_lstm_run5_<timestamp>\PID.txt)

# Stop training
Stop-Process -Id (Get-Content outputs\ai01_lstm_run5_<timestamp>\PID.txt)
```

### macOS / Linux

```bash
# Follow training log
tail -f outputs/ai01_lstm_run5_<timestamp>/train.log

# GPU utilization (refresh every 5s)
nvidia-smi -i 2 -l 5

# Check if process is still running
ps -p "$(cat outputs/ai01_lstm_run5_<timestamp>/PID.txt)"

# Stop training
kill "$(cat outputs/ai01_lstm_run5_<timestamp>/PID.txt)"
```

## Output Structure

Identical for `.ps1` and `.sh` (date/time format and metadata schema are byte-compatible):

```
outputs/ai01_<model>_run<N>_<timestamp>/
  train.log           # stdout (training progress)
  train.err           # stderr
  PID.txt             # process ID for monitoring
  run_metadata.json   # hyperparams, git info, timestamps
```

Checkpoints are saved to `checkpoints/<model>/<timestamp>/model.pt` with a `metadata.json` containing metrics and training history.

## Pre-checks

Each launcher (both PowerShell and bash) validates before starting:

1. Python executable exists in conda env `coursia-ml-training`.
2. `FeatureEngineer` imports from `ML-Training-Pipeline/scripts/features.py`.
3. PyTorch + CUDA available.
4. SPY CSV data files exist in `datasets/yfinance/`.
5. GPU 2 visible via `nvidia-smi` (warning only — the job proceeds even if `nvidia-smi` is missing on CPU-only hosts).

## Configuration

| Parameter | Default | Notes |
|-----------|---------|-------|
| `CUDA_VISIBLE_DEVICES` | `2` | GPU 2 on ai-01 (RTX 4090) |
| `PYTHONUNBUFFERED` | `1` | Real-time log output |
| Conda env | `coursia-ml-training` | Must have torch, pandas, numpy |

## CI — Dry-run validation

A `bash -n` syntax check runs in CI on `ubuntu-latest` (advisory, non-blocking):

```yaml
- name: Shell syntax check (bash companions)
  shell: bash
  run: |
    set -e
    for f in MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/scripts/launchers/*.sh \
             MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/scripts/run_m7_overnight_sweep.sh; do
      bash -n "$f"
    done
```

## Why `.sh` companions, not PowerShell Core 7+?

`#10643` (EPIC) documents the decision: students on Mac/Linux shouldn't need `pwsh` installed. Native bash is the convention chosen for the dépôt, with `$IsWindows`-style OS detection only inside the PowerShell scripts for Windows-specific paths.
