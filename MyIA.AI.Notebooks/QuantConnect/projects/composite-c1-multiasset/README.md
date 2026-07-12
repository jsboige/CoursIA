# composite-c1-multiasset

**Asset class:** Multi-asset (Equities, Bonds, Commodities)

**Cloud project ID:** N/A

## Description

C4.1 Multi-Asset Rotation Composite (v10) using the Alpha Framework architecture. Trades 5 ETFs (SPY, TLT, GLD, USO, EFA) with 2x leverage. Combines three alpha models: MomentumAlpha (trend-following), MACDAlpha (MACD signal crossover), and RelativeStrengthAlpha (cross-asset relative strength). Portfolio construction via RiskParityPCM (weekly rebalance, 100% max exposure, 40% sector cap). Risk management applies 12% drawdown cap with 4% trailing stop. Execution via VWAP (4 slices, 15-minute window).

## How to Run

### Lean CLI
```bash
lean backtest --algorithm composite-c1-multiasset/main.py
```

### QC Cloud
Create a new project, upload all `.py` files, compile and run a backtest.

## Backtest Metrics

| Method | Rebalance | Key Parameters |
|--------|-----------|----------------|
| Alpha Framework (3 alphas + RiskParity PCM) | Weekly | Leverage 2x, drawdown cap 12%, trailing stop 4%, VWAP 4-slice execution |

### Aligned baseline (2018-2025)

Standardized #1630 backbone run (QC Cloud project `32981093`, backtest `1236cf59`).

| Metric | Value |
|--------|-------|
| Sharpe Ratio | 0.258 |
| CAGR | 6.490% |
| Max Drawdown | 17.000% |
| Probabilistic Sharpe Ratio | 8.7% |
| Tradeable dates | 1761 |

Interpretation: weak positive Sharpe 0.258 (comparable to the simple momentum rotations AssetClassMomentum 0.22 and Vol-Ensemble-Conservative 0.265). The 3-alpha ensemble (Momentum + MACD + RelativeStrength) combined with the RiskParityPCM (weekly, 100% exposure, 40% sector cap), 12% drawdown cap + 4% trailing stop, and VWAP execution adds little over a single momentum signal on the aligned period -- the composite architecture does not dramatically beat its components. MaxDD is controlled at 17% by the drawdown cap (vs 22.8% for the uncapped GlobalMacro-Regime). Far below the framework composite leaders FamaFrenchAllWeather (0.684) and EMATrend (0.741): COMP composites vary widely (c1 weak vs AllWeather/EMATrend strong), so the component alpha/PCM choice matters more than the framework wiring itself. Notably the aligned Sharpe 0.258 is higher than the catalog-campaign figure (0.175), so alignment did not degrade this composite. PSR 8.7% non-significant. Promoted Tier 4 -> 2 (Historique). totalOrders = 0 = wrapper extraction artifact (CAGR 6.49% implies real trades).

## Files

| File | Description |
|------|-------------|
| `main.py` | Composite algorithm orchestrating alpha models, PCM, risk management, and execution |
| `alpha_models.py` | Three alpha models: Momentum, MACD, and Relative Strength |
| `portfolio_construction.py` | RiskParityPCM with weekly rebalance and sector caps |
| `risk_management.py` | Drawdown cap (12%) and trailing stop (4%) risk models |
| `execution.py` | VWAP execution model (4 slices, 15-minute window) |

## References

- [QuantConnect Alpha Framework](https://www.quantconnect.com/docs/v2/writing-algorithms/algorithm-framework)
- [QuantConnect Documentation](https://www.quantconnect.com/docs/)
