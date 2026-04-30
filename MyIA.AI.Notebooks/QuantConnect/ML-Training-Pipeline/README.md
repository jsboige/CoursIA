# ML Training Pipeline for Financial Prediction

Complete training pipeline for ML models on financial OHLCV data. Designed for RTX 4090 24GB GPU training with CPU dry-run validation.

## Architecture

```
scripts/
  train_classification.py    # RandomForest + XGBoost (CPU/GPU)
  train_lstm.py              # PyTorch LSTM/GRU (GPU recommended)
  train_transformer.py       # Financial Transformer (GPU required for full scale)
  train_dqn_rl.py            # DQN Reinforcement Learning (GPU recommended)
  validate_training_package.py  # Validate all scripts with --dry-run
checkpoints/                 # Saved models + metadata (auto-created)
  classification/<timestamp>/
  lstm/<timestamp>/
  transformer/<timestamp>/
  dqn/<timestamp>/
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

All models share the same feature set from OHLCV data:

| Feature | Description |
|---------|-------------|
| ret_1d, ret_5d, ret_10d, ret_20d | Returns at multiple horizons |
| vol_5d, vol_20d | Realized volatility |
| vol_ratio | Volume vs 20-day average |
| ma_ratio_5/10/20/60 | Price vs moving average ratio |
| rsi_14 | Relative Strength Index (14-period) |
| macd, macd_signal | MACD indicator |
| bb_width | Bollinger Band width |

LSTM/Transformer additionally use **true_range** and **atr_14** when OHLC data is available.

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
