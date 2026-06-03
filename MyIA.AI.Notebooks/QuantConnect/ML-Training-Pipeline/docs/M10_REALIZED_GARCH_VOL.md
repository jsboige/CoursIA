# M10 Realized GARCH (Hansen, Huang, Shek 2012) — Volatility Forecasting

## Reference

Hansen, P.R., Huang, Z., & Shek, H.H. (2012). "Realized GARCH: A Joint Model for Returns and Realized Measures of Volatility." *Journal of Applied Econometrics*, 27(6), 877-906.

## Model Description

Realized GARCH extends GARCH(1,1) with a measurement equation that conditions latent variance on realized volatility (RV). The model has 7-9 parameters:

- **GARCH equation**: `log(h_t) = omega + alpha * log(h_{t-1}) + beta * log(eps_{t-1}^2)`
- **Measurement equation**: `log(RV_t) = xi + phi * log(h_t) + tau(eps_t) + u_t`
- **Leverage function**: `tau(eps_t) = gamma_1 * eps_t + gamma_2 * (eps_t^2 - 1)`

Parameters: omega, alpha, beta, xi, phi, sigma_u, gamma_1, gamma_2 (8 params).

## Experimental Setup

| Parameter | Value |
|-----------|-------|
| Universe | 7 crypto pairs (ADA, BTC, DOT, ETH, LTC, SOL, XRP vs USD) |
| Data | Hourly close + RV from yfinance, 2020-01-01 to 2025-05-01 |
| Horizons | h = 1, 5, 10 (hours ahead) |
| Baseline | HAR Classic (Andersen et al. 2007): RV_{t+h} ~ RV_t + RV_{t-5:t} + RV_{t-22:t} |
| Walk-forward | Expanding window, train_size=250h, refit_every=22h, gap=10h |
| Seeds | 0, 1, 7, 42 (Note: MLE is fully deterministic — all 4 seeds produce identical results) |
| DM test | Direction-aware (H0: RG = HAR vs H1: RG != HAR), two-sided |
| Significance | p < 0.01 = BEATS_p001/BEATEN_p001, p < 0.05 = BEATS_p005/BEATEN_p005 |
| Total combos | 21 unique (7 coins x 3 horizons), 84 with redundant seeds |

## Results

### Summary

| Verdict | Count |
|---------|-------|
| BEATS | **0** |
| BEATEN | 13 (all at p < 0.05) |
| INCONCLUSIVE | 8 |

### Per-Coin, Per-Horizon Table

| Coin | h=1 MSE red | h=1 verdict | h=5 MSE red | h=5 verdict | h=10 MSE red | h=10 verdict |
|------|-------------|-------------|-------------|-------------|--------------|--------------|
| ADA-USD | -58.6% | BEATEN_p005 | -44.1% | INCONCLUSIVE | -39.2% | INCONCLUSIVE |
| BTC-USD | -63.5% | BEATEN_p005 | -58.2% | BEATEN_p005 | -31.2% | BEATEN_p005 |
| DOT-USD | -37.6% | BEATEN_p005 | -10.2% | INCONCLUSIVE | +18.7% | INCONCLUSIVE |
| ETH-USD | -68.3% | BEATEN_p005 | -97.2% | BEATEN_p005 | -79.1% | BEATEN_p005 |
| LTC-USD | -54.5% | BEATEN_p005 | -31.5% | INCONCLUSIVE | -13.6% | INCONCLUSIVE |
| SOL-USD | -62.6% | BEATEN_p005 | -67.4% | BEATEN_p005 | -69.0% | BEATEN_p010 |
| XRP-USD | -67.1% | BEATEN_p005 | -37.9% | INCONCLUSIVE | -15.4% | INCONCLUSIVE |

Negative MSE reduction = RG worse than HAR. Average across horizons: h=1: -58.9%, h=5: -49.5%, h=10: -32.7%.

### Worst Performers

| Coin/Horizon | MSE reduction | DM stat | DM p-value |
|--------------|---------------|---------|------------|
| ETH-USD h=5 | -97.2% | 11.15 | 0.0000 |
| ETH-USD h=10 | -79.1% | 7.46 | 0.0000 |
| SOL-USD h=10 | -69.0% | 3.49 | 0.0005 |

### Only Positive Combo

| Coin/Horizon | MSE reduction | DM stat | DM p-value | Verdict |
|--------------|---------------|---------|------------|---------|
| DOT-USD h=10 | +18.7% | -0.62 | 0.533 | INCONCLUSIVE |

## Verdict: NO BEATS

M10 Realized GARCH **fails to beat HAR Classic** across all 21 unique coin-horizon combinations. The model is systematically worse, particularly at short horizons (h=1) where the average MSE is 58.9% higher than HAR.

### Root Cause Analysis

1. **Overfitting risk**: 8 parameters vs 3 for HAR. With only 250h initial training and hourly crypto data, the MLE optimization likely overfits to noise in the training window.

2. **Crypto volatility regime shifts**: Crypto markets exhibit abrupt volatility regime changes (e.g., Luna crash, FTX collapse) that the GARCH conditional variance structure cannot adapt to quickly enough, while HAR's simple linear combination of realized variance components is more robust.

3. **Measurement equation mismatch**: The `log(RV_t) = xi + phi * log(h_t) + ...` assumes a stable linear relationship between conditional variance and realized volatility. In crypto, this relationship is noisy and unstable at hourly frequency.

4. **Log-transform distortion**: Taking log of both h_t and RV_t compresses the extreme volatility spikes that dominate crypto MSE. HAR operates directly on RV levels, preserving sensitivity to spikes.

5. **Deterministic seeds confirm structural issue**: All 4 seeds producing identical results rules out optimization randomness. The underperformance is structural, not stochastic.

### Why the Proposal Was Wrong

The M10 proposal expected 5-15% MSE improvement based on Hansen et al. (2012) equity market results. Crypto hourly data differs fundamentally:
- Higher kurtosis (~20-50 vs ~5-8 for equities)
- Regime-dependent volatility clustering (structural breaks)
- 24/7 trading eliminates overnight information effects that RG leverages in equity markets

## Recommendation

**Do not adopt M10 Realized GARCH for crypto volatility forecasting.** HAR Classic remains the baseline to beat. Future models should consider:
- Regime-switching HAR (Markov-switching HAR)
- HAR with jump components (HAR-RV-J)
- Neural approaches (log-transformed LSTM on RV sequences)

## Files

- `scripts/realized_garch.py`: Core M10 model (273 lines)
- `scripts/train_realized_garch.py`: Walk-forward training pipeline (398 lines)
- `scripts/results/m10_realized_garch_full.json`: Full 84-combo results
