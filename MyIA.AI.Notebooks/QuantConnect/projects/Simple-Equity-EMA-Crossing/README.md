# Simple-Equity-EMA-Crossing

**Asset class:** Equities (US large-cap tech)

**Cloud project ID:** N/A

## Description

Simple EMA(20)/EMA(50) crossover strategy on five major tech stocks (AAPL, MSFT, GOOGL, AMZN, NVDA). Goes long when the fast EMA crosses above the slow EMA, exits when the fast crosses below. Allocates 20% weight per position (max 5 positions). Uses EUR cash account with Interactive Brokers CASH account type. Checks for crossovers daily at market close.

## How to Run

### Lean CLI
```bash
lean backtest --algorithm Simple-Equity-EMA-Crossing/main.py
```

### QC Cloud
Create a new project, upload `main.py`, compile and run a backtest.

## Backtest Metrics

| Method | Rebalance | Key Parameters |
|--------|-----------|----------------|
| EMA(20)/EMA(50) crossover | Daily check | Fast EMA 20, slow EMA 50, 20% weight per position |

## Files

| File | Description |
|------|-------------|
| `main.py` | EMA crossover algorithm on 5 tech stocks with EUR cash account |

## References

- [QuantConnect Documentation](https://www.quantconnect.com/docs/)
