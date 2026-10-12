# MeanReversion

**Asset class:** US Sector ETFs
**Cloud project ID:** None (local only)

## Description

Short-term mean reversion strategy on 11 GICS sector ETFs (XLK, XLF, XLE, XLV, XLI, XLY, XLP, XLU, XLB, XLRE, XLC).
Every day at 10:00 (New York), it buys the most oversold ETFs (RSI(14) < 40) whose three-month return is no more than 10 points below SPY's. At most 4 positions at 25% each.
Exit: RSI > 65, 15-day holding period, or a -10% stop-loss.

SMA200 regime filter on SPY: in a bear market, new positions take 12.5% instead of 25%; open positions are not liquidated.
An ETF with fewer than 63 sessions of history (XLRE in late 2015, XLC in 2018) gets a zero three-month return.

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/MeanReversion"`
```bash
lean backtest --project .
```

**QC Cloud:** no persistent cloud project. The backtest below ran in a measurement project (37661669); copy `main.py` to a new QC Cloud project to run it again.

## Backtest Metrics (QC Cloud, 2015-01-01 to 2024-12-31, #20346)

| Metric | Value |
|--------|-------|
| Sharpe Ratio | 0.675 |
| CAGR | 10.42% |
| Max Drawdown | 11.1% |
| PSR | 8.7% |
| Orders | 704 |
| Net Return | +169.6% |

Backtest `ad190cab96bc` (project 37661669, `main.py` sha256 `0b28658c42c7`, the code in this folder). **No verdict**: the v5.x parameters were chosen on this same period (see the `main.py` docstring history), and a single backtest says nothing about an out-of-sample edge. The QC Sharpe includes a risk-free rate. This backtest does not reproduce the v5.2 figures given in the docstring (Sharpe 0.810).

Before #20346, the code crashed on 2018-09-11 with an index error (XLC, too young for the history guard), so it could not produce any metric over its coded window. The figures this README cited before (2015-2026, Sharpe 0.294) do not come from the v5.2 code.

## Files

- `main.py` - Strategy (v5.2, sector ETF mean reversion)
- `research.ipynb` - RSI optimization, stop-loss, and holding period tests

## References

- Jegadeesh (1990), "Evidence of Predictable Behavior of Security Returns"
- De Bondt & Thaler (1985), "Does the Stock Market Overreact?"
