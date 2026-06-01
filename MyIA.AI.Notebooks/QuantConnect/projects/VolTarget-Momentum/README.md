# VolTarget-Momentum

**Asset class:** Multi-asset (Equities, Bonds, Commodities)

**Cloud project ID:** 30784745

## Description

Rank-based allocation on six risky assets (SPY, EFA, EEM, TLT, GLD, DBC) with BND as a defensive safe harbor. v5 best variant achieved Sharpe 0.65, CAGR 14.72%. Uses SMA200 plus 6-month and 12-month momentum filters for asset selection. Targets 15% annualized volatility using 60-day realized volatility for position sizing, with leverage constrained to 0.3-1.5x. Monthly rebalance.

## How to Run

### Lean CLI
```bash
lean backtest --algorithm VolTarget-Momentum/main.py
```

### QC Cloud
Open the cloud project (ID: 30784745), compile and run a backtest.

## Backtest Metrics

| Method | Rebalance | Key Parameters |
|--------|-----------|----------------|
| Rank-based vol targeting + momentum | Monthly | Vol target 15%, 60-day realized vol, leverage 0.3-1.5x, SMA200 + 6m/12m momentum |

## Files

| File | Description |
|------|-------------|
| `main.py` | Volatility targeting with momentum filters and rank-based allocation on 6 risky + 1 defensive asset |
| `config.json` | Project configuration (cloud-id, organization-id, language) |

## References

- [QuantConnect Documentation](https://www.quantconnect.com/docs/)
