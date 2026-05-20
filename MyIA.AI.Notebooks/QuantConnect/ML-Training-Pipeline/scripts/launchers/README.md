# ML Training Launchers

PowerShell scripts to launch detached GPU training jobs on ai-01 (RTX 4090, GPU 2).

Each launcher handles environment setup, pre-checks, metadata logging, and starts the training process in the background with output redirection.

## Available Launchers

| Script | Model | Key Config | ETA |
|--------|-------|------------|-----|
| `launch_ai01_lstm_run5.ps1` | LSTM | h=384, layers=4, epochs=100, batch=64 | ~30-50 min |
| `launch_ai01_transformer_run6.ps1` | Transformer | d=384, heads=8, layers=8, epochs=200, batch=32 | ~60-90 min |

Both use `--advanced` features (19 indicators) and SPY 2015-2024 data.

## Usage

```powershell
# Full training (detached, logs to file)
.\launch_ai01_lstm_run5.ps1

# Quick validation (synthetic data, 2 epochs)
.\launch_ai01_lstm_run5.ps1 -DryRun

# Transformer training
.\launch_ai01_transformer_run6.ps1
.\launch_ai01_transformer_run6.ps1 -DryRun
```

## Monitoring

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

## Output Structure

Each run creates:

```
outputs/ai01_<model>_run<N>_<timestamp>/
  train.log           # stdout (training progress)
  train.err           # stderr
  PID.txt             # process ID for monitoring
  run_metadata.json   # hyperparams, git info, timestamps
```

Checkpoints are saved to `checkpoints/<model>/<timestamp>/model.pt` with a `metadata.json` containing metrics and training history.

## Pre-checks

Each launcher validates before starting:

1. Python executable exists in conda env `coursia-ml-training`
2. `FeatureEngineer` imports from `shared/features.py`
3. PyTorch + CUDA available
4. SPY CSV data files exist in `datasets/yfinance/`
5. GPU 2 visible via `nvidia-smi`

## Configuration

| Parameter | Default | Notes |
|-----------|---------|-------|
| `CUDA_VISIBLE_DEVICES` | `2` | GPU 2 on ai-01 (RTX 4090) |
| `PYTHONUNBUFFERED` | `1` | Real-time log output |
| Conda env | `coursia-ml-training` | Must have torch, pandas, numpy |
