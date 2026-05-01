# ML Training Pipeline for Financial Prediction

Complete training pipeline for ML models on financial OHLCV data. Designed for GPU training with CPU dry-run validation. All GPU scripts use thermal-safe training via `shared/gpu_training.py` (MAX_TEMP=80C, AMP, batch_thermal_check).

## Architecture

```
scripts/
  features.py                # Reusable feature engineering (indicators + caching)
  train_classification.py    # RandomForest + XGBoost (CPU/GPU)
  train_lstm.py              # PyTorch LSTM/GRU (GPU recommended)
  train_transformer.py       # Financial Transformer (GPU required for full scale)
  train_dqn_rl.py            # DQN Reinforcement Learning (GPU recommended)
  launch_po2025_track_a1.py  # Sequential launcher: Transformer -> DQN -> LSTM
  launch_ai01_track_b.py     # Track B launcher (ai-01 RTX 4090 baselines)
  validate_training_package.py  # Validate all scripts with --dry-run
  registry_update.py         # Build REGISTRY.md from checkpoints
checkpoints/                 # Saved models + metadata (auto-created)
  classification/<timestamp>/
  lstm/<timestamp>/
  transformer/<timestamp>/
  dqn/<timestamp>/
outputs/                     # Training logs and run artifacts
REGISTRY.md                  # Auto-generated checkpoint catalog
```

## Quick Start

### Validate the pipeline (CPU, no data needed)

```bash
python scripts/validate_training_package.py --verbose
```

### Train on real data

```bash
# Classification (RF/XGBoost)
python scripts/train_classification.py --data-dir ../datasets/yfinance --symbol SPY --start 2010-01-01

# LSTM
python scripts/train_lstm.py --data-dir ../datasets/yfinance --symbol SPY --hidden-size 256 --epochs 100

# Transformer (full scale for 24GB GPU)
python scripts/train_transformer.py --data-dir ../datasets/yfinance --symbol SPY \
    --d-model 256 --nhead 8 --num-layers 6 --dim-ff 1024 --epochs 100 --batch-size 64

# DQN RL agent
python scripts/train_dqn_rl.py --data-dir ../datasets/yfinance --symbol SPY \
    --hidden-size 512 --num-episodes 500
```

### Dry-run any script

```bash
python scripts/train_<model>.py --dry-run
```

Uses synthetic data, minimal epochs. Validates the full pipeline without GPU or real data.

## Models

| Script | Model | Task | GPU | Target 24GB |
|--------|-------|------|-----|-------------|
| train_classification.py | RandomForest / XGBoost | Direction classification (up/down) | Optional | 200+ trees, depth 12 |
| train_lstm.py | LSTM / GRU | Return regression | Recommended | hidden=512, layers=4 |
| train_transformer.py | Transformer encoder | Return regression | Required | d_model=256, heads=8, layers=6 |
| train_dqn_rl.py | DQN | Trading actions (buy/sell/hold) | Recommended | hidden=512, 500 episodes |

## Features Engineered

All indicators are available via `scripts/features.py` — composable functions with Parquet caching:

```python
from features import FeatureEngineer

engineer = FeatureEngineer(lookback=20)
features = engineer.transform(df, cache_path="cache/spy.parquet")
```

| Feature | Description |
|---------|-------------|
| ret_1d, ret_5d, ret_10d, ret_20d | Returns at multiple horizons |
| vol_5d, vol_20d | Realized volatility |
| vol_ratio | Volume vs 20-day average |
| ma_ratio_5/10/20/60 | Price vs moving average ratio |
| rsi_14 | Relative Strength Index (14-period) |
| macd, macd_signal | MACD indicator |
| bb_width | Bollinger Band width |
| true_range, atr_14 | True Range and ATR (requires OHLC) |
| obv, obv_norm | On-Balance Volume (raw and normalized) |

## Checkpoints

Each training run saves to `checkpoints/<model>/<timestamp>/`:

```
checkpoints/lstm/20260430_143022/
  model.pt (or model.joblib for sklearn)
  metadata.json
```

### metadata.json structure

```json
{
  "timestamp": "20260430_143022",
  "model_type": "lstm",
  "hyperparams": { ... },
  "metrics": { "mse": 0.000123, "direction_accuracy": 0.5432, ... },
  "history": { "train_loss": [...], "val_loss": [...] },
  "data_hash": "a1b2c3d4e5f6g7h8",
  "architecture": { "input_size": 14, "hidden_size": 128, "num_layers": 2 },
  "files": ["model.pt", "metadata.json"]
}
```

### Loading a checkpoint

```python
import torch, json
from pathlib import Path

ckpt = Path("checkpoints/lstm/20260430_143022")
metadata = json.loads((ckpt / "metadata.json").read_text())

# For PyTorch models (LSTM, Transformer, DQN)
from train_lstm import build_model
model = build_model(
    input_size=metadata["architecture"]["input_size"],
    hidden_size=metadata["architecture"]["hidden_size"],
    num_layers=metadata["architecture"]["num_layers"],
)
model.load_state_dict(torch.load(ckpt / "model.pt", weights_only=True))

# For sklearn models (classification)
import joblib
model = joblib.load(ckpt / "model.joblib")
```

## Data Sources

Designed to work with datasets from `scripts/datasets/` (Track A):

| Source | Script | Default path |
|--------|--------|--------------|
| yfinance | `download_yfinance.py` | `../datasets/yfinance/` |
| Binance | `download_binance_klines.py` | `../datasets/binance/` |
| Crypto archive | `manage_crypto_archive.py` | `../datasets/crypto_archive/` |
| QC lean-cli | `download_qc_data.py` | `../datasets/qc/` |

## Thermal Safety (GPU Training)

All GPU training scripts import from `shared/gpu_training.py` for thermal protection:

```python
from shared.gpu_training import batch_thermal_check, setup_amp, get_gpu_temp
```

| Function | Usage | Default |
|----------|-------|---------|
| `batch_thermal_check(temp, max_temp)` | Pause 30s if GPU exceeds threshold | max_temp=80C |
| `thermal_check(max_temp)` | Check between episodes (DQN) | max_temp=80C |
| `setup_amp(model, optimizer)` | Enable Automatic Mixed Precision | Enabled by default |
| `get_gpu_temp()` | Read GPU temperature via nvidia-smi | n/a |

**Thermal behavior**: When GPU exceeds MAX_TEMP, training pauses 30s. On laptops (MSI GE76 RTX 3080 Ti), expect ~80C baseline, meaning frequent thermal pauses. Training efficiency is ~2-5% wall time on thermally constrained hardware.

## Sequential Launchers

Track A1 (`launch_po2025_track_a1.py`) runs models sequentially with full thermal safety:

```bash
# Full Track A1: Transformer -> DQN -> LSTM
python scripts/launch_po2025_track_a1.py --symbol SPY --data-dir ../datasets/yfinance
```

Track B (`launch_ai01_track_b.py`) runs baselines on ai-01 (RTX 4090, no thermal issues).

## Dependencies

### Core (all scripts)

```
numpy
pandas
scikit-learn
joblib
```

### PyTorch (LSTM, Transformer, DQN)

```
torch>=2.0
```

### Optional

```
xgboost  # Enhanced classification (falls back to RF)
```

## Recommended GPU Training Commands (RTX 4090 24GB)

```bash
# LSTM - full scale
python scripts/train_lstm.py --data-dir ../datasets/yfinance --symbol SPY \
    --hidden-size 512 --num-layers 4 --dropout 0.3 \
    --seq-len 60 --epochs 200 --batch-size 128 --lr 5e-4

# Transformer - max utilization
python scripts/train_transformer.py --data-dir ../datasets/yfinance --symbol SPY \
    --d-model 256 --nhead 8 --num-layers 6 --dim-ff 1024 --dropout 0.15 \
    --seq-len 60 --epochs 150 --batch-size 64 --lr 3e-4

# DQN - extended training
python scripts/train_dqn_rl.py --data-dir ../datasets/yfinance --symbol SPY \
    --hidden-size 512 --num-episodes 1000 --replay-size 200000 \
    --batch-size 128 --lr 5e-4 --eps-decay 0.997
```

## Reproducibility

- **Data hash**: SHA256 of input dataset stored in metadata
- **Hyperparams**: All args saved verbatim
- **Training history**: Loss curves per epoch
- **Seeds**: Synthetic data uses seed=42; for production, set `PYTHONHASHSEED` and `torch.manual_seed()`
