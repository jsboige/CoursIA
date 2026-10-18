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

### What the composite actually computed (#21137, October 2026)

The four alphas score the same stocks at the same time, on the first pass of each month. Before calling `determine_target_percent`, the Lean base class (`PortfolioConstructionModel.GetTargetInsights`) keeps only the most recent active insight per symbol: on every stock, the alpha that emits last erases the others. This is the mechanism already measured by #19740 on the `Framework_Composite_*` projects.

Three backtests on QC Cloud, same window (2018-01-01 to 2025-01-01, 1761 tradeable dates), same code, two project parameters:

| Variant | `pcm_mode` | `alphas` | Sharpe | CAGR | Max drawdown | PSR | Orders |
|---------|------------|----------|--------|------|--------------|-----|--------|
| A. Code before #21137 | `symbol` | `all` | 0.584 | 13.183% | 20.500% | 7.631% | 7568 |
| B. Control: momentum only | `symbol` | `momentum` | 0.585 | 13.194% | 20.500% | 7.650% | 7362 |
| C. Per-sleeve fix (default) | `sleeve` | `all` | 0.441 | 9.126% | 17.600% | 3.284% | 9003 |

Backtests `e8d5fd4f` (A), `122d1a54` (B), `67da341f` (C), project 37945484.

**Reading.** A and B are almost identical: before #21137, the composite reduced to the momentum factor. The counters written at the end of the backtest (`PCM <alpha>` statistics, active insights / insights received by the PCM) confirm it: only `MomFactor` (5729 / 23837) and `LowVol` (76 / 328, on stocks momentum does not score) reach the PCM, `Value` and `Quality` never.

The per-sleeve fix (C) keeps the latest insight per (symbol, alpha) pair, normalizes scores inside each sleeve, gives each active sleeve an equal share and sums per symbol. It does what the composite claims, and does **worse** than momentum alone over this window: Sharpe 0.441 versus 0.585, with lower volatility (9.1% versus 12.2%) and a smaller max drawdown. Verdict: **NO BEATS**. The fix corrects the accounting; it does not improve performance.

**Still to measure.** `ValueAlpha` and `QualityAlpha` read `valuation_ratios.price_to_book`, `price_to_earnings`, `operation_ratios.return_on_equity` and `debt_to_equity` through `getattr(..., None)`. The other projects in the repository use `pb_ratio`, `pe_ratio` and `roe`. If these names do not exist in Lean, the two alphas never emit anything, and variant C only blends LowVol and momentum. This is not measured yet and belongs to a separate grain.

### Project parameters

| Parameter | Values | Effect |
|-----------|--------|--------|
| `pcm_mode` | `sleeve` (default), `symbol` | `symbol` reproduces the PCM from before #21137 |
| `alphas` | `all` (default), `momentum` | `momentum` wires `MomentumFactorAlpha` only (control) |

### History: baseline published before #21137

These figures were obtained with the PCM from before #21137, hence with momentum alone in practice. Replayed in October 2026, the same code gives row A above: QC data and engine have changed in between.

| Metric | Catalog (2015-2025) | Aligned (2018-2025) |
|--------|---------------------|---------------------|
| Sharpe Ratio | 0.543 | 0.574 |
| CAGR | 10.010% | 11.942% |
| Max Drawdown | 18.800% | 18.600% |
| PSR | 16.822% | 25.765% |

Backtest `8eecba32` (aligned) / `3173f8b39` (catalog `c2-equityfactor-post2801`), project 32981222. The interpretation that came with these figures (four-factor investing beating the multi-asset rotation of `composite-c1-multiasset`) no longer holds: the measured performance was momentum's alone.

## Files

| File | Description |
|------|-------------|
| `main.py` | Composite equity factor algorithm orchestrating universe selection, alphas, PCM, risk, and execution |
| `alpha_models.py` | Four factor models: Value, Quality, LowVolatility, and Momentum |
| `portfolio_construction.py` | MeanVariancePCM with weekly rebalance, sector caps, and exposure limits; per-sleeve mode (`by_sleeve`) and per-alpha counters (#21137) |
| `risk_management.py` | SectorCapRiskModel with max sector weight and beta constraints |
| `execution.py` | TWAP execution model (6 slices, 10-minute window) |

## References

- [QuantConnect Alpha Framework](https://www.quantconnect.com/docs/v2/writing-algorithms/algorithm-framework)
- [QuantConnect Fine Fundamental Selection](https://www.quantconnect.com/docs/v2/writing-algorithms/universes/fundamental)
- [QuantConnect Documentation](https://www.quantconnect.com/docs/)
