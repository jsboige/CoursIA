# TermStructureCommodities-QC

**Asset class:** Commodities (Futures)
**Cloud project ID:** None (local only)

## Description

Commodity futures term structure strategy from the QuantConnect Strategy Library.
Exploits contango/backwardation in commodity futures curves by rolling between
near and far contracts based on the shape of the term structure.

**Note:** Metrics from original QC Library, not locally reproduced.

## How to Run

**Lean CLI:**
```bash
lean backtest --project .
```

**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics (Original Library)

| Metric | Value |
|--------|-------|
| 5Y CAGR | -15.71% |
| 5Y Drawdown | 80.80% |
| Asset Class | Commodities Futures |

## Files

- `main.py` - Strategy (cloned from QC Strategy Library)

## References

- QuantConnect Strategy Library
- Gorton & Rouwenhorst (2006), "Facts and Fantasies about Commodity Futures"
