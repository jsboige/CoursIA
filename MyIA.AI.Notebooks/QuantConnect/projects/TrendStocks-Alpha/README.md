# TrendStocks-Alpha

**Asset class:** US Equities (Large-cap diversified)
**Cloud project ID:** 28885507

## Description

Framework-based trend-following alpha strategy on 15 large-cap stocks across sectors.
Uses `TrendStocksAlpha` with EMA(20/50) for signal and SMA(200) as trend confirmation.
Weekly rebalance via `MultiStrategyPCM`.

The strategy enters long positions when short-term EMA is above long-term EMA AND the price is above the 200-day SMA, confirming the secular uptrend.

## How to Run

**Lean CLI:**
```bash
lean backtest --project .
```

**QC Cloud:** Open project 28885507 in the QuantConnect IDE and click "Backtest".

## Backtest Metrics (2015-2026)

| Metric | Value |
|--------|-------|
| Sharpe Ratio | ~0.61 |
| Benchmark | SPY |
| Rebalance | Weekly |
| Universe | 15 large-cap stocks |

## Files

- `main.py` - Strategy entry point (framework alpha model)
- `alpha_models.py` - TrendStocksAlpha implementation
- `portfolio_construction.py` - MultiStrategyPCM module
- `quantbook.ipynb` - Research notebook

## References

- QC Framework: Alpha Model + Portfolio Construction pattern
- Ref: Faber (2007), "A Quantitative Approach to Tactical Asset Allocation"
