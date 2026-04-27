# VIX-TermStructure

**Asset class:** Volatility (SVXY)
**Cloud project ID:** None (local only)
**Status:** ARCHIVED (Sharpe ceiling +0.05)

## Description

VIX term structure strategy using SVXY (short-volatility ETF).
Signals based on the spread between VIX spot and VIX3M (3-month VIX futures).
Goes long SVXY when term structure is in contango (VIX < VIX3M), flat in backwardation.

**Archived because:** Structural ceiling at Sharpe +0.05. Short-vol strategies suffer from
asymmetric payoffs (small gains, rare catastrophic losses). The 2018 Volmageddon event
demonstrates the structural risk. See ARCHIVE.md for full ceiling analysis.

## How to Run

**Lean CLI:**
```bash
lean backtest --project .
```

**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics (2015-2026)

| Metric | Value |
|--------|-------|
| Sharpe Ratio | +0.05 |
| Strategy | Long SVXY in contango |
| Signal | VIX vs VIX3M spread |
| Risk | Volmageddon tail risk |

## Files

- `main.py` - Strategy (v4.1, VIX term structure contango signal)
- `research.ipynb` - VIX spread analysis and regime testing

## References

- Simon & Campasano (2014), "The VIX Fix"
- ARCHIVE.md - Full iteration history and structural ceiling analysis
