# composite-c2-equityfactor

**Asset class:** Equities (US large-cap, fundamental selection)

**Cloud project ID:** N/A

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
