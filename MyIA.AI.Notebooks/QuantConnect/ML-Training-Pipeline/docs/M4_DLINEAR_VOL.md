# M4 -- DLinear-vol: Linear Deep Learning vs HAR for Volatility Forecasting

**Status:** COMPLETE (Cycle 25 Wave 3, po-2024 Track 2).

## Why

M2-M3 established HAR (Corsi 2009) as the gold-standard baseline for crypto RV forecasting.
M3b showed asymmetric semivariance decomposition benefits BTC. A natural question: can the
simplest possible deep learning model -- DLinear (Zeng et al. AAAI 2023) -- beat HAR?

DLinear was proposed as a surprising result: a single `nn.Linear` layer that matches or
outperforms complex Transformers on long-term time series benchmarks. For volatility
forecasting, the question is whether a learned linear map from `log-RV_{t-seq_len...t}` to
`log-RV_{t+1...t+h}` captures dynamics that HAR's hand-crafted (1d/5d/22d) features miss.

## Model

**HAR (Corsi 2009):**
```
log RV_{t+h} = b0 + b_d*log(RV_t) + b_w*mean(log RV_{t-5..t-1}) + b_m*mean(log RV_{t-22..t-6}) + e
```

**DLinear (Zeng et al. 2023, adapted):**
```
y_hat = Linear(seq_len -> horizon)
```

Where:
- Input: last `seq_len=22` daily log-RV values (normalized)
- Output: next `horizon` log-RV values
- Optional decomposition: trend (AvgPool1d) + seasonal, with separate linear layers

## Methodology

- Walk-forward 5-fold expanding window, refit every 22 days
- 4 seeds (0, 7, 42, 99)
- 3 horizons (h=1, 5, 10 days)
- 7 coins (BTC, ETH, SOL, LTC, XRP, ADA, DOT)
- Diebold-Mariano HAC test vs HAR baseline
- AdamW optimizer, 100 epochs, gradient clipping 1.0, batch size 32
- Normalization: expanding-window mean/std on log-RV

## Files

| File | Role |
|------|------|
| `scripts/dlinear_vol.py` | DLinear-vol model + walk-forward runner |
| `scripts/results/m4_dlinear_vol_full.json` | Full 7-coin results (9082s runtime) |
| `scripts/results/m4_dlinear_vol_test.json` | Quick BTC+ETH test |
| `docs/M4_DLINEAR_VOL.md` | This document |

## Full Results (7 coins, 3 horizons, 4 seeds, 9082s runtime)

### DM verdict summary

| Verdict | Count | Configs |
|---------|-------|---------|
| **BEATS** | 5/21 | BTC h=1, h=5, h=10; ETH h=1; SOL h=1 |
| INCONCLUSIVE | 16/21 | All other (coin, horizon) pairs |
| NO BEATS | 0/21 | -- |

### Per-coin results (aggregated over 4 seeds)

| Coin | Horizon | DLinear MSE | HAR MSE | Reduction | DM p-value | Verdict |
|------|---------|-------------|---------|-----------|------------|---------|
| BTC-USD | 1 | 0.7518 | 0.8877 | -15.3% | <0.0001 | **BEATS** |
| BTC-USD | 5 | 0.3740 | 0.5220 | -28.3% | <0.0001 | **BEATS** |
| BTC-USD | 10 | 0.3521 | 0.5707 | -38.3% | <0.0001 | **BEATS** |
| ETH-USD | 1 | 0.6619 | 0.6844 | -3.3% | 0.036 | **BEATS** |
| ETH-USD | 5 | 0.3590 | 0.3736 | -3.9% | 0.285 | INCONCLUSIVE |
| ETH-USD | 10 | 0.3519 | 0.3745 | -6.0% | 0.316 | INCONCLUSIVE |
| SOL-USD | 1 | 0.5534 | 0.6132 | -9.8% | 0.001 | **BEATS** |
| SOL-USD | 5 | 0.2711 | 0.2835 | -4.4% | 0.221 | INCONCLUSIVE |
| SOL-USD | 10 | 0.2324 | 0.2378 | -2.2% | 0.679 | INCONCLUSIVE |
| ADA-USD | 1 | 0.6561 | 0.6925 | +5.3% | 0.050 | INCONCLUSIVE |
| ADA-USD | 5 | 0.3798 | 0.4114 | +7.7% | 0.206 | INCONCLUSIVE |
| ADA-USD | 10 | 0.3690 | 0.3725 | +0.9% | 0.894 | INCONCLUSIVE |
| LTC-USD | 1 | 0.6258 | 0.6564 | +4.7% | 0.086 | INCONCLUSIVE |
| LTC-USD | 5 | 0.3912 | 0.4304 | +9.1% | 0.100 | INCONCLUSIVE |
| LTC-USD | 10 | 0.3850 | 0.4225 | +8.9% | 0.236 | INCONCLUSIVE |
| DOT-USD | 1 | 0.6182 | 0.6383 | +3.2% | 0.141 | INCONCLUSIVE |
| DOT-USD | 5 | 0.3791 | 0.3802 | +0.3% | 0.931 | INCONCLUSIVE |
| DOT-USD | 10 | 0.3613 | 0.3587 | -0.7% | 0.922 | INCONCLUSIVE |
| XRP-USD | 1 | 0.8516 | 0.8501 | -0.2% | 0.670 | INCONCLUSIVE |
| XRP-USD | 5 | 0.4975 | 0.5227 | +4.8% | 0.353 | INCONCLUSIVE |
| XRP-USD | 10 | 0.5056 | 0.5246 | +3.6% | 0.615 | INCONCLUSIVE |

(Positive reduction = DLinear beats HAR. Bold = statistically significant across all 4 seeds.)

### Per-coin summary

| Coin | h=1 | h=5 | h=10 | Data source | RV days | Preds/fold |
|------|-----|-----|------|-------------|---------|------------|
| BTC-USD | BEATS | BEATS | BEATS | Bitstamp | ~2278 | ~378 |
| ETH-USD | BEATS | INC | INC | Binance | ~1495 | ~248 |
| SOL-USD | BEATS | INC | INC | yfinance | ~725 | ~119 |
| ADA-USD | INC* | INC | INC | yfinance | ~725 | ~119 |
| LTC-USD | INC* | INC | INC | yfinance | ~725 | ~119 |
| DOT-USD | INC | INC | INC | yfinance | ~725 | ~119 |
| XRP-USD | INC | INC | INC | yfinance | ~725 | ~119 |

INC* = 2-3 seeds pass DM but not all 4 (ADA h=1: 3/4, LTC h=1: 2/4).

### MSE reduction vs HAR (DLinear - HAR, negative = DLinear wins)

| Coin | h=1 | h=5 | h=10 |
|------|-----|-----|------|
| BTC-USD | -15.3% | -28.3% | **-38.3%** |
| ETH-USD | -3.3% | -3.9% | -6.0% |
| SOL-USD | -9.8% | -4.4% | -2.2% |
| ADA-USD | +5.3% | +7.7% | +0.9% |
| LTC-USD | +4.7% | +9.1% | +8.9% |
| DOT-USD | +3.2% | +0.3% | -0.7% |
| XRP-USD | -0.2% | +4.8% | +3.6% |

## Key findings

1. **DLinear BEATS HAR on BTC at all horizons (15-38% MSE reduction).** All 4 seeds pass
   the DM test at p<0.0001. The effect grows with horizon: a learned 22-day linear projection
   captures substantially more information than HAR's 3 hand-crafted features at h=10.

2. **ETH and SOL: significant at h=1 only.** ETH (1495 RV days) and SOL (725 RV days) both
   show 4/4 seeds passing DM at h=1, but the advantage does not extend to h=5 or h=10.
   This suggests DLinear captures short-horizon dynamics missed by HAR, but the signal
   weakens at longer horizons without enough data.

3. **Data quantity is the primary bottleneck.** BTC (2278 RV days, ~10 years) is the only
   coin where DLinear significantly beats HAR at ALL horizons. Coins with ~725 days
   (yfinance) show numerical improvements at some horizons (LTC h=5: -9.1%, ADA h=5: -7.7%)
   but none reach significance across all 4 seeds.

4. **XRP is the exception: DLinear slightly worse at h=1.** The only coin where DLinear
   does not consistently improve on HAR at the shortest horizon (MSE -0.2% at h=1, one
   seed worse at p=0.36). XRP's different microstructure (RV+ > RV-) may produce
   dynamics less suited to a global linear projection.

5. **DLinear is remarkably stable across seeds.** For BTC, the MSE spread across 4 seeds
   is <0.002 at any horizon. The model's simplicity (single linear layer) makes it
   inherently low-variance, which is an advantage over more complex architectures for
   small-sample financial data.

6. **HAR's hand-crafted features are a ceiling.** HAR uses 3 features (1d, 5d, 22d means).
   DLinear learns 22 free parameters (seq_len -> 1), effectively learning optimal weights
   on the full 22-day history. When data is sufficient, this flexibility wins. When data
   is scarce, the regularization of HAR's 3-parameter model may be preferable.

7. **Cross-reference with M3b (asymmetric HAR).** M3b found asymmetric HAR beats classic
   HAR for BTC (5-37% reduction). This M4 run shows DLinear also beats HAR for BTC
   (15-38% reduction). The two improvements are complementary: M3b exploits sign
   asymmetry (leverage effect), while M4 exploits full-path information. A natural next
   step would be a DLinear with asymmetric inputs (RV+ and RV- separately).

## References

- Zeng, A., Chen, M., Zhang, L. & Xu, Q. (2023) "Are Transformers Effective for Time Series Forecasting?", AAAI 2023.
- Corsi, F. (2009) "A Simple Approximate Long-Memory Model of Realized Volatility", Journal of Financial Econometrics 7, 174-196.
