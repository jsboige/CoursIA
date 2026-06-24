# PCA-StatArbitrage

**Asset class:** US Equities (top 100 by dollar volume)
**Cloud project ID:** `33281920` (`1630-baseline-PCAStatArbitrage`, IBKR + aligned 2018-2025; main.py = canonical + date parameterization only)

## Description

QC Cloud-compatible PCA statistical arbitrage using sklearn PCA instead of numpy/scipy. Fits principal components to the log-price panel of a top-100 US-equity universe, regresses each name on the PCA factors, and trades the residual z-scores as a contrarian mean-reversion signal (long the z<-1.5 tail, weights proportional to z-deviation, full monthly rotation via `set_holdings(liquidate=True)`).

**Consolidated from PCA-StatArb** (statsmodels version, not QC Cloud compatible) and **ML-PCA-StatArb** (identical code with extra comments).

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/PCA-StatArbitrage"`
**QC Cloud:** Deployed (see Cloud project ID above). The `main.py` committed here is the canonical copy with `set_brokerage_model(IBKR, MARGIN)` (real fees); the 2015-2024 hardcoded dates are the author default.

## Backtest Metrics

| Metric | Value | Window / fees |
|--------|-------|---------------|
| Method | sklearn PCA + OLS residual mean-reversion | — |
| Rebalance | Monthly (full rotation, `set_holdings liquidate=True`) | — |
| Universe | Top 100 US equities by dollar volume | — |
| Sharpe | **0.205** | 2018-2025, IBKR real fees (#1630-aligned) |
| CAGR | 6.76% | 2018-2025, IBKR |
| MaxDD | 31.8% | 2018-2025, IBKR |
| PSR | 1.4% (noise-level) | 2018-2025, IBKR |
| Sharpe (prior) | 0.399 | 2015-2024, IBKR (author window) |
| Sharpe (no-fee control) | 0.205 (byte-identical) | 2018-2025, no brokerage |

**#1630 caveat (verified 2026-06-23).** The catalog 0.40 does not survive #1630 alignment: 0.399 -> **0.205** (-49%, PSR 1.4% = noise). Two findings: **(a) the drop is a WINDOW-effect, not fee** -- the README 0.399 was already an IBKR number, so the degradation is the aligned window's 2024-25 Mag7-momentum melt-up, structurally hostile to contrarian PCA mean-reversion (oversold residual names keep falling, winners keep winning); **(b) the strategy is fee-IMMUNE** -- a hardcoded no-brokerage clone of the identical logic (backtest `63fce57d`) returns byte-identical 0.205, so removing the brokerage changes nothing at 3-decimal precision. This refutes the pre-run "monthly full-rotation => fee-vulnerable" prediction and extends the #1630 discriminator regime-3 near-immune class (fee-homogeneity of the US-equity basket dominates over per-event turnover; cf EMA-Cross-Stocks IBKR 0.991 = no-brokerage 0.991). Full analysis: `docs/qc/qc-comparative-backtests.md` finding #40 (See #1630).

## Files

- `main.py` — Strategy (sklearn PCA + OLS mean-reversion, consolidated from PCA-StatArb + ML-PCA-StatArb, IBKR brokerage).

## References

- Avellaneda, M. & Lee, J.-H. (2010), *Statistical Arbitrage in the US Equities Market*. (PCA residual mean-reversion framework.)
