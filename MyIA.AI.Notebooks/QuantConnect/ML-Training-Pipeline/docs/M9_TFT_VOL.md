# M9 -- TFT (Temporal Fusion Transformer) for Crypto Volatility Forecasting

**Status:** COMPLETE (Cycle 25 Wave 3, po-2024 Track C1).

## Why

M4 showed DLinear beats HAR on BTC at all horizons (5/21 BEATS). A natural extension: can
a more expressive architecture -- the Temporal Fusion Transformer (Lim et al. 2021) -- improve
on DLinear's results? TFT combines LSTM sequence encoding with multi-head attention and
variable selection, designed for multi-horizon forecasting with interpretable attention weights.

The TFT architecture is significantly more complex than DLinear (~110K params vs ~22 params),
so the question is whether this expressiveness translates to better volatility forecasts or
whether the added complexity hurts generalization on limited crypto data.

## Model

**DLinear (M4 baseline):**
```
y_hat = Linear(seq_len -> horizon)
```

**TFT (Lim et al. 2021, adapted):**
```
1. Variable Selection Network -> select relevant features per timestep
2. LSTM Encoder -> capture local temporal patterns
3. Multi-Head Attention -> capture long-range dependencies
4. Gated Residual Network -> skip connections with gating
5. Output projection -> pred_len predictions
```

Architecture: d_model=64, n_heads=4, lstm_layers=1, dropout=0.1, fc_dropout=0.1
Total params: ~110,801 (BTC) / ~111,061 (ETH)

Input features (18): returns, volatility, volume_ratio, ma_ratios, rsi, macd, bollinger,
true_range_atr, obv (9 indicators x 2 for recent + historical windows).

## Methodology

- Walk-forward expanding window with gap=10 days
- 4 seeds (0, 1, 7, 42)
- 3 horizons (h=1, 5, 10 days)
- 2 coins (BTC-USD, ETH-USD) -- crypto only, no FAANG/Mag7
- 100 epochs, batch_size=64, lr=5e-4, AdamW optimizer
- Gradient clipping 1.0, mixed precision (AMP) on CUDA
- Direction accuracy vs majority-class baseline as primary metric
- Edge = direction_accuracy - majority_class_accuracy (positive = TFT wins)
- Verdict: BEATS if Edge > 0 and significant across seeds; INCONCLUSIVE otherwise

## Files

| File | Role |
|------|------|
| `scripts/train_tft.py` | TFT model + walk-forward training pipeline |
| `scripts/results/m9_tft_*.json` | Results per config |
| `outputs/tft_m9_*/results.json` | Detailed per-run results |
| `docs/M9_TFT_VOL.md` | This document |

## Results

### BTC-USD

| Horizon | Seeds | Folds | DirAcc | Edge | MSE | Verdict |
|---------|-------|-------|--------|------|-----|---------|
| h=1 | 4 | 4 | 0.4963 | -0.0304 | 0.018462 | INCONCLUSIVE |
| h=5 | 4 | 4 | 0.5017 | -0.0250 | 0.016952 | INCONCLUSIVE |
| h=10 | 4 | 4 | 0.4995 | -0.0279 | 0.019945 | INCONCLUSIVE |

### ETH-USD

| Horizon | Seeds | Folds | DirAcc | Edge | MSE | Verdict |
|---------|-------|-------|--------|------|-----|---------|
| h=1 | 4 | 4 | 0.4993 | -0.0284 | 0.003269 | INCONCLUSIVE |
| h=5 | 4 | 4 | 0.5019 | -0.0248 | 0.004326 | INCONCLUSIVE |
| h=10 | 4 | 4 | 0.4969 | -0.0299 | 0.004452 | INCONCLUSIVE |

### Aggregate summary (6/6 configs)

| Metric | Mean across configs | Range |
|--------|---------------------|-------|
| DirAcc | 0.4993 | 0.4963-0.5019 |
| Edge | -0.0277 | -0.0304 to -0.0248 |
| MSE | 0.011234 | 0.003269-0.019945 |

**Overall verdict: 0/6 BEATS (INCONCLUSIVE across all 6 configs)**

### Comparison with baselines

| Model | Params | BEATS count | Best edge |
|-------|--------|-------------|-----------|
| M3b HAR asymmetric | 3-5 | 3/21 | +0.05 (BTC h=1) |
| M4 DLinear | ~22 | 5/21 | -15% MSE (BTC h=1) |
| M5 HMM regime | 8+HMM | 1/6 | +9.6% MSE (ETH h=1) |
| **M9 TFT** | **~110K** | **0/6** | **-0.025 edge** |

## Key findings

1. **TFT fails to beat majority-class baseline.** Across all 6 configs (BTC h=1/5/10,
   ETH h=1/5/10), the aggregate edge is consistently negative (-0.025 to -0.030). The 110K
   param TFT model cannot reliably predict volatility direction better than always predicting
   the majority class. Mean edge = -0.0277, mean DirAcc = 0.4993 (< 50%).

2. **Fold 1 (smallest training set) is catastrophic.** With only ~700 training samples, TFT
   overfits dramatically: edges range from -0.12 to -0.16. Later folds (3-4) with ~2800
   samples sometimes achieve positive edge (+0.02 to +0.05), but not enough to compensate.

3. **More data helps but not enough.** The trend from Fold 1 to Fold 4 is consistently
   improving (e.g., BTC h=1 seed 0: -0.16 -> -0.04 -> -0.02 -> +0.03). However, even
   with the maximum training window, TFT averages only ~50% direction accuracy.

4. **TFT is strictly worse than DLinear.** DLinear (~22 params) achieved 5/21 BEATS with
   15-38% MSE reduction vs HAR. TFT (~110K params, 5000x more parameters) achieves 0/6
   BEATS and cannot even beat the majority-class baseline. This confirms the finding from
   Zeng et al. (2023): transformers struggle on simple time series forecasting tasks.

5. **No meaningful difference between horizons.** h=1, h=5, and h=10 all produce similar
   negative edges (~-0.028). Unlike DLinear which improved with longer horizons, TFT shows
   no horizon-dependent pattern.

6. **Seed stability is moderate.** Standard deviation of edge across seeds is ~0.06, with
   consistent negative mean. The verdict (INCONCLUSIVE) is stable across all seed choices.

## References

- Lim, B., Arik, S.O., Loeff, N. & Pfister, T. (2021) "Temporal Fusion Transformers for
  Interpretable Multi-horizon Time Series Forecasting", International Journal of Forecasting
  37(4), 1748-1764.
- Zeng, A., Chen, M., Zhang, L. & Xu, Q. (2023) "Are Transformers Effective for Time Series
  Forecasting?", AAAI 2023.
- Corsi, F. (2009) "A Simple Approximate Long-Memory Model of Realized Volatility",
  Journal of Financial Econometrics 7, 174-196.
