# ESGF Volatility Kit - 3 Cloud-Validated Strategies

## Overview

Three volatility-based strategies for the ESGF pedagogical kit. These strategies use **volatility forecasting** (GARCH and HAR-RV) for position sizing, not directional ML prediction. This is an honest pedagogical outcome: ML financial directional prediction is extremely difficult, and volatility-based risk budgeting provides a more robust foundation.

## Strategic Context

After extensive testing across M5/M6/M7/M8 and T21.26 MoE experiments:
- **0 BEATS** across TFT, Mamba, iTransformer, PatchTST, MoE, and GNN directional models
- Directional accuracy consistently near random (49-51%)
- MoE regime-switching showed 0 BEATS_HAR across 10-coin panier

**Pivot**: Focus on what works — volatility forecasting is a well-established academic domain (Nobel Prize 2003, Engle) with genuine edge in risk management and position sizing.

## Strategies

### 1. ESGF-GARCH-VolTarget (Project 31456084)

**Model**: GARCH(1,1) via variance-targeting MLE grid search (alpha: 0.05-0.25, beta: 0.75-0.95)

**Sizing**: Inverse-volatility targeting at 10% annualized per asset, SMA200 direction filter

**Parameters**: 500-day training window, refit every 22 days, weekly Monday rebalancing

**Backtest Results (2015-2025)**:

| Metric | Value |
|--------|-------|
| Sharpe Ratio | 0.311 |
| CAGR | 6.09% |
| Max Drawdown | 12.1% |
| Net Profit | +80.6% |
| Win Rate | 82% |
| Total Orders | 1178 |
| Fees | $1,769 |
| Alpha | 0.008 |
| Beta | 0.188 |

### 2. ESGF-HAR-RV-Kelly (Project 31456164)

**Model**: HAR(1,5,22) OLS on log-RV (Corsi 2009) with 5-day iterated forecast

**Sizing**: Kelly criterion at 1/4 fraction, 5-day momentum direction

**Parameters**: 500-day rolling window, refit every 22 days, weekly rebalancing

**Backtest Results (2015-2025)**:

| Metric | Value |
|--------|-------|
| Sharpe Ratio | 0.146 |
| CAGR | 4.23% |
| Max Drawdown | 12.8% |
| Net Profit | +51.3% |
| Win Rate | 62% |
| Total Orders | 1354 |
| Fees | $3,879 |
| Alpha | 0 |
| Beta | 0.110 |

### 3. ESGF-VolEnsemble-Conservative (Project 31456204)

**Model**: Ensemble of GARCH(1,1) + HAR(1,5,22) — takes max vol forecast (conservative)

**Sizing**: Inverse-vol at 8% annualized target, regime filter (SPY > SMA200: full, else 50%)

**Parameters**: 500-day window, refit every 22 days, SMA50 direction, 25% per-asset cap

**Backtest Results (2015-2025)**:

| Metric | Value |
|--------|-------|
| Sharpe Ratio | 0.213 |
| CAGR | 4.89% |
| Max Drawdown | 14.3% |
| Net Profit | +61.2% |
| Win Rate | 76% |
| Total Orders | 1298 |
| Fees | $2,352 |
| Alpha | 0.001 |
| Beta | 0.161 |

## Key Design Decisions

1. **No external packages**: GARCH and HAR implemented from scratch in pure numpy — no `arch`, `statsmodels`, or other dependencies. This ensures QC Cloud compatibility.

2. **Variance-targeting MLE**: omega = sigma2 * (1 - alpha - beta) reduces GARCH to a 2-parameter grid search.

3. **Multi-asset universe**: SPY, EFA, EEM, TLT, GLD, DBC — AQR-style trend following across asset classes.

4. **Weekly rebalancing**: Reduces turnover while maintaining responsive vol targeting.

5. **QC API naming**: Use `self.SMA()` (PascalCase) and store indicators as `self.sma_ind` (not `self.sma` which shadows the method).

## Files

| Strategy | Project ID | Local Path |
|----------|-----------|------------|
| GARCH-VolTarget | 31456084 | `projects/ESGF-GARCH-VolTarget/` |
| HAR-RV-Kelly | 31456164 | `projects/ESGF-HAR-RV-Kelly/` |
| VolEnsemble-Conservative | 31456204 | `projects/ESGF-VolEnsemble-Conservative/` |

## References

- Engle, R.F. (2003). "Autoregressive Conditional Heteroscedasticity with Estimates of the Variance of United Kingdom Inflation" — Nobel Prize lecture
- Corsi, F. (2009). "A Simple Approximate Long-Memory Model of Realized Volatility"
- Andersen, Bollerslev, Diebold, Labys (2003). "Modeling and Forecasting Realized Volatility"
