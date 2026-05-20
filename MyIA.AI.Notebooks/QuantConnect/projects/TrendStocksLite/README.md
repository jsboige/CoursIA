# TrendStocksLite

**Asset class:** US Equities (15 stocks)
**Cloud project ID:** None (local only)

## Description

Simplified trend-following strategy on a 15-stock universe using SMA200 + EMA filter.
Weekly rebalance: goes long stocks above SMA200 with positive EMA slope, flat otherwise.
Lighter version of TrendStocks-Alpha (which uses 50 stocks + monthly rebalance).

## How to Run

**Lean CLI:**
```bash
lean backtest --project .
```

**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics

| Metric | Value |
|--------|-------|
| Universe | 15 US stocks |
| Rebalance | Weekly |
| Indicators | SMA200 + EMA slope |
| Leverage | Standard (equal weight) |

## Files

- `main.py` - Strategy (SMA200 trend + EMA filter, 15 stocks)
- `research.ipynb` - Universe selection and rebalance frequency analysis
