# Stage 2: Transformers for Time Series (PatchTST & iTransformer)

Two SOTA transformer architectures adapted for financial time-series prediction,
with anti-pattern safeguards from the ML baseline crisis (issue #703).

## Architecture Comparison

| Aspect | PatchTST (ICLR 2023) | iTransformer (ICLR 2024) |
|--------|----------------------|--------------------------|
| Tokens | Patches of time series | Variables (inverted) |
| Key idea | Patching + channel independence | Attention across variables |
| Input | [B, T, N] -> patches per channel | [B, T, N] -> permute to [B, N, T] |
| Best for | Long sequences, many features | Cross-variable dependencies |
| Default params | 635K (d=128, 8h, 3L, patch=16) | 613K (d=128, 8h, 3L) |
| Script | `scripts/train_patchtst.py` | `scripts/train_itransformer.py` |
| Tests | `tests/test_patchtst.py` (11) | `tests/test_itransformer.py` (10) |

## Quick Start

```bash
# Dry-run validation (synthetic data, 2 epochs)
python scripts/train_patchtst.py --dry-run
python scripts/train_itransformer.py --dry-run

# Full training on yfinance data
python scripts/train_patchtst.py --data-dir ../datasets/yfinance --symbol SPY --epochs 100
python scripts/train_itransformer.py --data-dir ../datasets/yfinance --symbol SPY --epochs 100

# Multi-asset
python scripts/train_patchtst.py --symbols SPY,RSP,IWM --seq-len 96 --pred-len 24

# Walk-forward (if walk_forward.py available)
python scripts/train_patchtst.py --symbol SPY --walk-forward --n-splits 5
```

## Anti-Pattern Safeguards

All scripts enforce:

1. **Test ratio honored**: `--test-ratio` defaults to 0.15, actual ratio reported
2. **Train-only normalization**: Z-stats computed on training set only (anti-leakage)
3. **Majority-class baseline**: Always computed and reported; model must beat to claim edge
4. **Thermal watchdog**: `batch_thermal_check()` every 5 batches, MAX_TEMP=80C
5. **AMP**: Automatic Mixed Precision when CUDA available

## Output Format

Checkpoints saved to `--output-dir` (default: `outputs/patchtst_run1/` or `outputs/itransformer_run1/`):

```
outputs/patchtst_run1/
  20260504_220353/
    model.pt          # PyTorch state dict
    metadata.json     # hyperparams, metrics, history, data_hash
```

### Metrics Reported

- `mse`, `mae`: Standard regression metrics
- `direction_accuracy_step1`: Binary direction accuracy at first prediction step
- `majority_class_baseline`: What you'd get always predicting the majority direction
- `edge_over_majority`: `direction_accuracy - majority_class_accuracy` (must be > 0)
- `best_val_loss`: Best validation loss across epochs

## PatchTST Details

**"A Time Series is Worth 64 Words"** (Nie et al., ICLR 2023)

Key hyperparameters:
- `--patch-len 16`: Length of each patch (token)
- `--stride 8`: Stride between patches (overlap = patch_len - stride)
- `--seq-len 96`: Input sequence length
- `--pred-len 24`: Prediction horizon
- `--no-channel-independence`: Disable CI (not recommended)

Channel independence (default ON): each variable is processed independently with
shared weights. This is the paper's key finding — treating channels independently
outperforms multivariate attention on most benchmarks.

## iTransformer Details

**"iTransformer: Inverted Transformers Are Effective for Time Series Forecasting"**
(Li et al., ICLR 2024)

Key insight: instead of attending over time steps (standard Transformer), attend
over variables. Each variable's entire time series becomes a single token of
dimension `seq_len`, then projected to `d_model`. The transformer captures
inter-variable dependencies.

No patch-related hyperparameters. Simpler architecture:
- `--d-model 128`: Embedding dimension for variable tokens
- `--n-heads 8`: Attention heads
- `--n-layers 3`: Transformer layers

## Running Tests

```bash
python -m pytest ML-Training-Pipeline/tests/ -v
```

Tests cover: forward pass shapes, parameter registration, state dict roundtrip,
gradient flow, sequence building, normalization, majority baseline computation.
