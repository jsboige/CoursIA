# ML Training Pipeline for Financial Prediction

Complete training pipeline for ML models on financial OHLCV data. Designed for GPU training with CPU dry-run validation. All GPU scripts use thermal-safe training via `shared/gpu_training.py` (MAX_TEMP=80C, AMP, batch_thermal_check).

## Architecture

```
scripts/
  # --- Data & Features ---
  features.py                      # Reusable feature engineering (indicators + caching)
  build_dataset_v2.py              # V2 dataset builder: panier + cross-asset features + regime labels
  data_utils.py                    # Data loading, synthetic generation, hashing
  garch_baseline.py                # GARCH(1,1) rolling refit (no data leak) + leaky comparison
  regime_detector.py               # Price-based regime detection (uptrend/downtrend/vol/black_swan)
  baselines.py                     # Majority-class, buy-hold, momentum baselines + Sharpe computation

  # --- Training: Core models ---
  train_classification.py          # RandomForest + XGBoost (CPU/GPU)
  train_lstm.py                    # PyTorch LSTM/GRU (GPU recommended)
  train_transformer.py             # Financial Transformer (GPU required for full scale)
  train_dqn_rl.py                  # DQN Reinforcement Learning (GPU recommended)

  # --- Training: Advanced architectures ---
  train_moe_regimes.py             # MoE with regime-aware routing (Issue #754 Phase B)
  train_moe.py                     # MoE with gating network
  train_patchtst.py                # PatchTST (Nie et al., ICLR 2023)
  train_itransformer.py            # iTransformer (Li et al., ICLR 2024)
  train_mamba.py                   # Mamba SSM baseline
  train_rl_dt.py                   # Decision Transformer for RL

  # --- Training: Volatility & regime ---
  train_volatility_garch_dl.py     # GARCH+DL hybrid volatility forecasting
  train_volatility_regime.py       # Volatility regime classifier
  train_regime_classifier.py       # HMM regime detection
  train_har_baseline.py            # HAR(1,5,22d) vs GARCH-rolling vs naive on crypto RV (#834 M2)
  train_realized_garch.py          # Realized GARCH (M10, Hansen et al. 2012)

  # --- Volatility sweep series (M10-M15) ---
  realized_variance.py             # Daily RV from intraday OHLCV + log transform
  intraday_loader.py               # yfinance hourly data loader with Parquet cache
  har_model.py                     # HAR(1,5,22) model + walk-forward for baseline
  simulate_har_kelly.py            # HAR Kelly sweep (M2 baseline)
  m11g_fee_aware_kelly.py          # Fee-aware Kelly framework (shared by all M-series)
  m11c_sharpe_test.py              # Ledoit-Wolf Sharpe diff SE + sign-test
  m12_har_rv_j.py                  # HAR-RV-J jump-augmented (M12)
  m13_ms_har.py                    # Markov-Switching HAR (M13, Hamilton 1989)
  m14_heavy.py                     # HEAVY bivariate (M14, Shephard & Sheppard 2010)
  m15_lstm_rv.py                   # Log-LSTM RV (M15, neural on log-realized variance)

  # --- Training: Graph Neural Networks ---
  train_gnn.py                     # GNN (GCN/GAT/RGCN) on crypto panier
  train_mtgnn.py                   # Multivariate Time-series GNN
  train_stgat.py                   # Spatial-Temporal GAT

  # --- Training: Baselines ---
  train_baselines_crypto_panier.py # Stage 0 baselines (10 coins, WF 5-fold x 4 seeds)

  # --- Evaluation ---
  eval_rl_dt.py                    # Decision Transformer checkpoint evaluation harness
  eval_chronos_bolt.py             # Chronos-Bolt zero-shot evaluation (Amazon, ~200M params)
  eval_kronos_zeroshot.py          # Kronos zero-shot evaluation (AAAI 2026, 4 sizes)
  eval_finstsb.py                  # FinTSB-style per-regime evaluation (4 regimes)
  eval_existing_checkpoints.py     # Full pipeline: WF + baselines + regimes + transaction costs

  # --- Infrastructure ---
  checkpoint_utils.py              # Shared PyTorch checkpoint saving (model.pt + metadata.json)
  launch_po2025_track_a1.py        # Sequential launcher: Transformer -> DQN -> LSTM
  launch_ai01_track_b.py           # Track B launcher (ai-01 RTX 4090 baselines)
  validate_training_package.py     # Validate all scripts with --dry-run
  registry_update.py               # Build REGISTRY.md from checkpoints
  walk_forward.py                  # Walk-forward splitter (expanding window, 5-fold)

checkpoints/                       # Saved models + metadata (auto-created)
  classification/<timestamp>/
  lstm/<timestamp>/
  transformer/<timestamp>/
  dqn/<timestamp>/
  moe_regimes/<timestamp>/
outputs/                           # Training logs and run artifacts
REGISTRY.md                        # Auto-generated checkpoint catalog
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

### Core (direction prediction)

| Script | Model | Task | GPU | Target 24GB |
|--------|-------|------|-----|-------------|
| train_classification.py | RandomForest / XGBoost | Direction classification (up/down) | Optional | 200+ trees, depth 12 |
| train_lstm.py | LSTM / GRU | Return regression | Recommended | hidden=512, layers=4 |
| train_transformer.py | Transformer encoder | Return regression | Required | d_model=256, heads=8, layers=6 |
| train_dqn_rl.py | DQN | Trading actions (buy/sell/hold) | Recommended | hidden=512, 500 episodes |

### Advanced architectures (Issue #754)

| Script | Model | Task | GPU | Notes |
|--------|-------|------|-----|-------|
| train_moe_regimes.py | MoE + regime router | Direction via regime-aware experts | Recommended | LSTM/GRU/Transformer experts per regime (bull/bear/neutral/vol) |
| train_moe.py | MoE + gating network | Direction via mixture of experts | Recommended | Soft routing via gating |
| train_patchtst.py | PatchTST | Multi-variate forecasting | Required | Patch tokenization (ICLR 2023) |
| train_itransformer.py | iTransformer | Multi-variate forecasting | Required | Inverted attention on variates (ICLR 2024) |
| train_mamba.py | Mamba SSM | Sequence modeling | Recommended | State-space model baseline |
| train_rl_dt.py | Decision Transformer | RL via sequence modeling | Recommended | Offline RL, return-conditioned |

### Volatility & regime

| Script | Model | Task | GPU | Notes |
|--------|-------|------|-----|-------|
| train_volatility_garch_dl.py | GARCH(1,1) + DL hybrid | Volatility forecasting | Recommended | LSTM/Transformer/TFT correction on GARCH residuals |
| train_volatility_regime.py | Regime LSTM | Volatility regime detection | Optional | HMM + LSTM classifier |
| train_regime_classifier.py | HMM | Regime detection (bull/bear/neutral/vol) | CPU | Hidden Markov Model |

### Graph Neural Networks (crypto panier)

| Script | Model | Task | GPU | Notes |
|--------|-------|------|-----|-------|
| train_gnn.py | GCN / GAT / RGCN | Cross-asset spillover | Required | 10-coin crypto panier, rolling corr adjacency |
| train_mtgnn.py | MTGNN | Multivariate graph learning | Required | Learns graph structure |
| train_stgat.py | ST-GAT | Spatial-temporal attention | Required | Attention over spatial + temporal dims |

### Volatility baselines

| Script | Model | Task | GPU | Notes |
|--------|-------|------|-----|-------|
| train_har_baseline.py | HAR(1,5,22d) | Realized Variance forecast | CPU | Walk-forward 5-fold vs GARCH-rolling, crypto hourly OHLCV (#834 M2) |

### Volatility sweep series (M10--M17)

Systematic comparison of volatility models against HAR Classic Kelly on 7 crypto coins (BTC-USD, ETH-USD, SOL-USD, LTC-USD, XRP-USD, ADA-USD, DOT-USD), 3 horizons (h=1,5,10), 4 seeds (0,1,7,42), walk-forward 5-fold expanding. Kelly cap=1.0, fee=50bps. Verdict: sign-test paired Sharpe-diff vs HAR Classic, BEATS requires p<0.05 AND win>=60%.

| Script | Doc | Model | Params | Verdict |
| ------ | --- | ----- | ------ | ------- |
| train_realized_garch.py | M10_REALIZED_GARCH_VOL.md | Realized GARCH (Hansen et al. 2012) | ~8 | NO BEATS (MSE +62%) |
| simulate_har_kelly.py | M2_HAR_BASELINE.md | HAR Classic Kelly (Corsi 2009) | 4 | **Baseline** (Sharpe +0.313 vs BH) |
| m12_har_rv_j.py | M12_HAR_RV_J.md | HAR-RV-J (jump-augmented) | 7 | **BEATS** (p=7.9e-7) |
| m13_ms_har.py | M13_MS_HAR.md | Markov-Switching HAR (Hamilton 1989) | 11 | NO BEATS (39/84, p=0.7774) |
| m14_heavy.py | M14_HEAVY.md | HEAVY (Shephard & Sheppard 2010) | 6 | NO BEATS (48/84, p=0.1149) |
| m15_lstm_rv.py | M15_LSTM_RV.md | Log-LSTM RV (Hochreiter 1997) | ~4.8K (h=32) / ~17.7K (h=64) | **BEATS** h=32 (52/84, p=0.0188) / NO BEATS h=64 (45/84, p=0.2928) |
| har_lj_asym.py | M17_HAR_LJ_ASYM.md | HAR-LJ-Asym (jump+semivariance composite) | 7 | **BEATS** (60/60 DM p<5e-5, caveated: horizon bug, 5 coins) |

Supporting modules: `har_model.py`, `realized_variance.py`, `intraday_loader.py`, `m11g_fee_aware_kelly.py`, `m11c_sharpe_test.py`. Full roadmap: `docs/M_NEXT_VOL_PROPOSAL.md`.

### Evaluation harnesses

| Script | Purpose | Notes |
|--------|---------|-------|
| eval_rl_dt.py | DT checkpoint evaluation | Walk-forward OOS, majority-class comparison, transaction cost analysis |
| eval_chronos_bolt.py | Chronos-Bolt zero-shot | Amazon T5-based, ~200M params, 250x faster than original Chronos |
| eval_kronos_zeroshot.py | Kronos zero-shot | AAAI 2026, pre-trained on 12B K-lines, 4 model sizes (4M-499M) |
| eval_finstsb.py | Per-regime evaluation | 4 regimes (uptrend/downtrend/volatility/black_swan) |
| eval_existing_checkpoints.py | Full pipeline evaluation | WF + baselines + per-regime + transaction costs for any checkpoint |

### Dataset building

| Script | Purpose | Notes |
|--------|---------|-------|
| build_dataset_v2.py | V2 panier dataset builder | 26 symbols, 7 asset classes, cross-asset features, HMM+price regime labels (#754 Phase C) |

### Shared utilities

| Script | Purpose | Notes |
|--------|---------|-------|
| features.py | Feature engineering engine | Composable indicators with Parquet caching |
| data_utils.py | Data I/O utilities | Load yfinance/Binance, synthetic generation, SHA256 hashing |
| baselines.py | Baseline models | Majority-class, buy-hold, momentum. Sharpe computation |
| garch_baseline.py | GARCH utilities | Rolling refit (no data leak) vs leaky comparison. Realized vol computation |
| regime_detector.py | Regime detection | Price-based: uptrend/downtrend/volatility/black_swan |
| checkpoint_utils.py | Checkpoint I/O | `save_pytorch_checkpoint()`: model.pt + metadata.json with architecture/metrics/history |
| walk_forward.py | Walk-forward splitter | Expanding window, configurable n_splits |

### Baselines

| Script | Purpose | Notes |
|--------|---------|-------|
| train_baselines_crypto_panier.py | Stage 0 baselines (10 coins) | Majority, buy-hold, momentum, RF. WF 5-fold x 4 seeds, 10bps costs |

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
| obv | On-Balance Volume (rolling-std normalized) |

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
xgboost      # Enhanced classification (falls back to RF)
arch         # GARCH volatility models (garch_baseline.py, train_har_baseline.py)
hmmlearn     # HMM regime detection (train_regime_classifier.py)
fastparquet  # Parquet I/O for dataset V2 (build_dataset_v2.py)
pyarrow      # Parquet backend (build_dataset_v2.py)
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

## Validation (dry-run)

All scripts support `--dry-run` (synthetic data, 2 epochs) except `train_moe.py`, `train_volatility_garch_dl.py`, and `train_regime_classifier.py` (no dry-run flag).

```bash
# Validate all scripts
python scripts/validate_training_package.py --verbose
```

Dry-run results (CPU, Python 3.13, torch 2.11.0+cpu):

| Script | Status | DirAcc / Metric | Time |
|--------|--------|-----------------|------|
| train_classification.py | PASS | Acc=0.427 | ~2s |
| train_lstm.py | PASS | DirAcc=0.476, MSE=0.001 | ~7s |
| train_transformer.py | PASS | DirAcc=0.512, MSE=0.002 | ~7s |
| train_dqn_rl.py | PASS | OOS Sharpe OK | ~120s |
| train_moe_regimes.py | PASS | DirAcc=0.462, 2 folds | ~15s |
| train_gnn.py | PASS | Edge=-0.035 (FAILS baseline) | ~5s |
| train_patchtst.py | PASS | Edge=-0.169 (FAILS baseline) | ~5s |
| train_itransformer.py | PASS | Edge=-0.120 (FAILS baseline) | ~5s |
| train_mamba.py | PASS | Edge=-0.177 (FAILS baseline) | ~5s |
| train_mtgnn.py | PASS | Edge=-0.004 (FAILS baseline) | ~5s |
| train_stgat.py | PASS | Edge=-0.034 (FAILS baseline) | ~5s |
| train_rl_dt.py | PASS | Edge=+0.223 (BEATS baseline) | ~5s |
| train_volatility_regime.py | PASS | Acc=0.663, Edge=-0.266 | ~5s |

Note: dry-run uses synthetic random data. FAILS baseline is expected with random walks. Real-data results are in `results/` and on the cluster dashboard.

## Reproducibility

- **Data hash**: SHA256 of input dataset stored in metadata
- **Hyperparams**: All args saved verbatim
- **Training history**: Loss curves per epoch
- **Seeds**: Synthetic data uses seed=42; for production, set `PYTHONHASHSEED` and `torch.manual_seed()`
