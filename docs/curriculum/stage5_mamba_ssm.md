# Stage 5: Mamba / State Space Models for Financial Time Series

**Date**: 2026-05-07 | **Context**: Issue #754 ML SOTA Curriculum, Pivot toward volatility forecasting
**Status**: Exploration note — not a commitment to implement

---

## Why SSMs Matter for Finance

Transformers have O(L^2) attention, limiting sequence length. In finance, long horizons matter:
- 1 year of hourly bars = ~8,760 timesteps
- Multi-year daily bars = 1,000-2,500 timesteps
- LOB data: millions of events per day

Mamba (Gu & Dao, 2023) achieves **O(L) complexity** via selective state spaces, making ultra-long sequences tractable without chunking or memory tricks.

### Transformer vs SSM Comparison

| Aspect | Transformer | Mamba SSM |
|--------|-------------|-----------|
| Complexity | O(L^2) | O(L) |
| Memory | O(L^2) for attention | O(L * d_state) |
| Long-range deps | Full attention | Selective gating via dt, B, C |
| Position info | Explicit (PE/ALiBi) | Implicit in recurrence |
| Parallel training | Native | Via associative scan |
| Inference | KV cache grows | Fixed state (d_model * d_state) |
| GPU requirement | Moderate | Lower (linear) |

---

## Architecture Overview

### Core: Selective State Space Model (S6)

The key innovation over prior SSMs (S4, S5): **input-dependent parameters**.

```
Traditional SSM:  x' = A*x + B*u,  y = C*x + D*u  (A, B, C fixed)
Mamba (S6):       x' = A*x + B(t)*u, y = C(t)*x   (B, C, dt depend on input)
```

This selectivity lets the model:
- **Remember** important tokens (large dt = slow state update = long memory)
- **Forget** noise (small dt = fast state decay)
- **Attend** to relevant features (input-dependent B, C projections)

### MambaBlock Structure (per layer)

```
Input x [B, L, d_model]
  |
  +-- LayerNorm
  +-- Linear in_proj -> [B, L, 2*d_inner]  (d_inner = d_model * expand_factor)
  +-- Split -> x_proj, z (gating)
  +-- Conv1d (causal, kernel=d_conv) on x_proj
  +-- SiLU activation
  +-- Selective SSM:
      - x_proj -> B, C, dt (input-dependent)
      - dt_proj with softplus (positive step sizes)
      - Discretize: dA = exp(A*dt), dB = B*x*dt
      - Sequential scan: h_t = dA_t * h_{t-1} + dB_t
      - Output: y_t = C_t @ h_t
  +-- Skip connection: y = y + D*x
  +-- Gate: y * SiLU(z)
  +-- Linear out_proj -> [B, L, d_model]
  +-- Residual: output = input + dropout(y)
```

### MambaTSModel (our implementation)

```
Input [B, T, n_features]
  -> Linear embedding -> [B, T, d_model]
  -> N x MambaBlock (d_model, d_state=16, d_conv=4, expand=2)
  -> LayerNorm
  -> Flatten last pred_len steps
  -> Linear head -> [B, pred_len]
```

---

## Financial Applications

### P1: Realized Volatility Forecasting (RECOMMENDED)

**Evidence**: 15-30% MSE reduction vs GARCH(1,1) (Zhang et al. NIPS 2018, Roszyk & Slepaczuk 2024).

Why Mamba fits:
- Volatility clustering requires **long memory** — Mamba's selective gating captures this naturally
- O(L) complexity enables multi-year training at daily/hourly granularity
- State space formulation aligns with GARCH's variance recursion (both are state-based)

**Proposed hybrid**: GARCH(1,1) structural prior + Mamba residual learner.
GARCH captures stylized facts (volatility clustering, mean reversion), Mamba learns nonlinear residuals.

### P2: Multi-Asset Correlation Forecasting

SAMBA (Graph-Mamba, Mehrabian et al. 2024) combines GNN structure with SSM temporal processing.
Near-linear complexity for correlation matrices across 50+ assets.

### P3: Intraday Price Movement

O(L) enables minute-bar or tick-level modeling that Transformers cannot handle at full resolution.

---

## Existing Implementation

**File**: `MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/scripts/train_mamba.py`

~500+ LOC, includes:
- `SelectiveSSM`: Pure Python selective scan (CPU-compatible), falls back to CUDA kernel if `mamba-ssm` installed
- `MambaBlock`: LayerNorm + SSM + residual
- `MambaTSModel`: Full model with embedding, N blocks, prediction head
- Anti-pattern safeguards: walk-forward support, train-only normalization, majority-class baseline
- Walk-forward validation via `WalkForwardSplitter`
- Transaction cost integration

**Tests**: `scripts/tests/test_mamba.py`

**References implemented**:
- MambaStock (Zshi et al., 2024)
- CryptoMamba (ShahabSepehri et al., 2024)

### Hyperparameter Guide

| Param | Default | Range | Notes |
|-------|---------|-------|-------|
| `d_model` | 128 | 64-256 | Model dimension; 128 good for finance |
| `d_state` | 16 | 8-32 | SSM state expansion; 16 = paper default |
| `d_conv` | 4 | 3-8 | Local conv kernel; captures short-range patterns |
| `expand_factor` | 2 | 2 | Inner dimension multiplier |
| `n_layers` | 4 | 2-8 | Depth; 4 balances capacity vs overfitting |
| `seq_len` | 1024 | 256-4096 | Input window; Mamba handles long sequences efficiently |
| `pred_len` | 24 | 1-96 | Forecast horizon |

---

## Experimental Results (Issue #754)

**27+ experiments across 8 architectures** (MoE, LSTM, Transformer, PatchTST, iTransformer, Mamba, STGAT, MTGNN) on daily binary direction prediction.

**Result**: All architectures failed to beat majority-class baseline consistently across 5 seeds.
- 4/5 seeds: FAIL
- seed=42: BEAT (+1.5sigma outlier, not reproducible)

**Conclusion**: Daily binary direction prediction is the wrong target for DL architectures.
Pivot to **volatility forecasting** (GARCH+DL hybrid) where DL has proven 15-30% edge.

---

## Curriculum Position

This fits in **Stage 5** of the ML SOTA curriculum:

| Stage | Topic | Status |
|-------|-------|--------|
| 0 | Walk-forward validation, anti-overfitting | DONE (wf_framework) |
| 1 | Classical ML baselines (RF, XGBoost) | DONE (panier baselines) |
| 2 | LSTM / RNN for time series | DONE (train_lstm.py) |
| 3 | Transformer / Attention | DONE (train_transformer.py) |
| 4 | MoE / Regime-aware models | DONE (train_moe.py) |
| **5** | **Mamba / SSM architectures** | **THIS NOTE** |
| 6 | Multi-asset GNN | Planned |
| 7 | Foundation models (TSFM fine-tuning) | Planned |

### Learning Objectives for Stage 5

1. Understand SSM fundamentals (S4 -> S5 -> S6/Mamba evolution)
2. Implement selective scan mechanism from scratch (done in train_mamba.py)
3. Compare O(L) vs O(L^2) complexity empirically on financial data
4. Apply walk-forward validation to Mamba (reuse wf_framework from Stage 0)
5. Evaluate Mamba on volatility forecasting vs GARCH baseline
6. Understand when SSMs outperform Transformers (long sequences, streaming) and when not (short sequences, multi-variate cross-attention)

---

## Key References

1. Gu, A. & Dao, T. (2023). "Mamba: Linear-Time Sequence Modeling with Selective State Spaces." arxiv:2312.00752
2. Gu, A. et al. (2022). "Structured State Spaces for Sequence Modeling" (S4). ICLR.
3. Zshi et al. (2024). "MambaStock: Selective State Space Model for Stock Prediction." GitHub: zshicode/MambaStock
4. ShahabSepehri et al. (2024). "CryptoMamba." GitHub: MShahabSepehri/CryptoMamba
5. Zhang et al. (2018). "Deep Learning for Volatility Forecasting." NIPS.
6. Roszyk & Slepaczuk (2024). "Hybrid GARCH-LSTM Volatility Models." SSRN.
7. Mehrabian et al. (2024). "SAMBA: Graph-Mamba for Multi-Asset." Near-linear complexity.

---

## Next Steps

1. **Volatility pivot**: Retrain MambaTSModel on realized volatility targets (not binary direction)
2. **GARCH hybrid**: Implement GARCH(1,1) feature extraction -> Mamba residual pipeline
3. **Multi-seed walk-forward**: Use wf_framework (Stage 0) for rigorous validation
4. **Sequence length sweep**: Compare Mamba vs Transformer at L=256, 1024, 4096, 16384
5. **Crypto validation**: ETH, BTC, LTC (where baselines show +1-4pp edge over majority)
