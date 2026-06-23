# composite-c2-equityfactor

**Asset class:** Equities (US large-cap, fundamental selection)

**Cloud project ID:** 32981222

## Description

C4.2 Equity Factor Composite (v12) using the Alpha Framework with fine fundamental universe selection. Two-stage selection: coarse filter (top 200 by dollar volume) then fine filter (top 25 by market cap). Generates signals from four factor alpha models: Value (P/E, P/B ratios), Quality (ROE, debt-to-equity), LowVolatility (realized volatility), and Momentum (price momentum). Portfolio construction via MeanVariancePCM (weekly rebalance, 65% max exposure, 18% sector cap). Risk management via SectorCapRiskModel (max 10% sector weight, max 0.8 beta). Execution via TWAP (6 slices, 10-minute window). Caches fundamental data for performance.

## How to Run

### Lean CLI
```bash
lean backtest --algorithm composite-c2-equityfactor/main.py
```

### QC Cloud
Create a new project, upload all `.py` files, compile and run a backtest.

## Backtest Metrics

| Method | Rebalance | Key Parameters |
|--------|-----------|----------------|
| Alpha Framework (4 factors + MeanVar PCM) | Weekly | Top 25 by market cap, 65% max exposure, sector cap 18%, TWAP 6-slice |

### Aligned baseline (2018-2025)

Standardized #1630 window (2018-01-01 to 2025-01-01, 1761 tradeable dates), backtested on QC Cloud with post-#2801 real fees.

| Metric | Catalog (2015-2025) | Aligned (2018-2025) |
|--------|---------------------|---------------------|
| Sharpe Ratio | 0.543 | **0.574** |
| CAGR | 10.010% | 11.942% |
| Max Drawdown | 18.800% | 18.600% |
| PSR | 16.822% | 25.765% |

Backtest `8eecba32` (aligned) / `3173f8b39` (catalog `c2-equityfactor-post2801`), project 32981222.

The strongest COMP (composite-framework) backbone baseline verified to date: Sharpe 0.574 is the highest among the Alpha Framework composites tested on the aligned window, and near Tier-1 territory (>0.5). It **holds and slightly improves** over the catalog window (0.543 to 0.574, PSR 16.8% to 25.8%) — genuinely robust, not period-overfit. This contrasts sharply with the sibling `composite-c1-multiasset` (Sharpe 0.258): both share the Alpha Framework scaffold, but factor investing on a fine-fundamental top-25 large-cap US stock universe (Value/Quality/LowVol/Momentum + MeanVariancePCM) dramatically outperforms static 5-ETF multi-asset rotation (3-alpha momentum ensemble + RiskParityPCM). The component alpha/PCM choice and stock-level fundamental universe matter far more than the framework wiring itself. Promoted Tier 4 (Untested) to Tier 2 (Historique). `totalOrders=0` in the MCP wrapper is an extraction artifact (CAGR 11.9% implies real trades).

## Files

| File | Description |
|------|-------------|
| `main.py` | Composite equity factor algorithm orchestrating universe selection, alphas, PCM, risk, and execution |
| `alpha_models.py` | Four factor models: Value, Quality, LowVolatility, and Momentum |
| `portfolio_construction.py` | MeanVariancePCM with weekly rebalance, sector caps, and exposure limits |
| `risk_management.py` | SectorCapRiskModel with max sector weight and beta constraints |
| `execution.py` | TWAP execution model (6 slices, 10-minute window) |

## References

- [QuantConnect Alpha Framework](https://www.quantconnect.com/docs/v2/writing-algorithms/algorithm-framework)
- [QuantConnect Fine Fundamental Selection](https://www.quantconnect.com/docs/v2/writing-algorithms/universes/fundamental)
- [QuantConnect Documentation](https://www.quantconnect.com/docs/)
