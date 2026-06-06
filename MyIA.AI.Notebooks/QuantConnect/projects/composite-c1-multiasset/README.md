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
