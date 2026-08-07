# Cloud-MeanReversion-Sectors

**Asset class:** Equities (GICS sector ETFs)

**Cloud project ID:** 30822855

## Description

RSI(14) mean reversion strategy on 11 GICS sector ETFs (XLK, XLF, XLE, XLV, XLI, XLY, XLP, XLU, XLB, XLRE, XLC). Three variants with increasing sophistication: v1 uses raw RSI oversold/overbought signals; v2 adds an SMA200 regime filter (only trade in bull markets); v3 adds an 8% stop-loss rule. Scans daily 30 minutes after market open. Interactive Brokers brokerage (real costs), SPY benchmark.

## How to Run

### Lean CLI

```bash
lean backtest --algorithm Cloud-MeanReversion-Sectors/main.py
```

### QC Cloud

Project 30822855. Upload `main.py`, compile and run a backtest, passing the `version` parameter (`v1`/`v2`/`v3`). Hard-coded period: **2018-01-01 → 2025-01-01** (aligned with the cross-strategy baseline #1630).

> **Note:** the `version` parameter must be passed explicitly (`v1`, `v2`, or `v3`). The code default (`"1"`) matches no branch and would raise an `AttributeError` at the first scan; the explicit parameter is required for any run.

## Backtest Metrics

Fresh backtest via QC Cloud MCP, 2026-08-07 (`MeanReversion-v1-honest-read-2026-08`, project 30822855, compile `BuildSuccess`, parameter `version=v1`, 2768 tradeable dates, 417 orders):

| Indicator | Value | Reading |
|---|---|---|
| Sharpe ratio | **0.176** | weakly positive |
| CAGR | **4.961%** | below buy-and-hold SPY over the period |
| Max drawdown | **41.700%** | catastrophic (> 2× SPY) |
| Total net profit | **70.392%** (+$77,345) | over the period |
| PSR (Probabilistic Sharpe Ratio) | **0.052%** | indistinguishable from noise |
| Orders | 417 | real backtest |

**Verdict: NO-BEATS.** Sharpe 0.176, CAGR ~5% for a 41.7% drawdown, PSR ≈ 0: the strategy underperforms buy-and-hold SPY (double-digit CAGR over 2018-2025) with materially higher risk.

## Honest read (v1 variant)

v1 is pure RSI mean reversion: buy the 3 most oversold sector ETFs (RSI < 35), exit on overbought (RSI > 55) or after a 20-day holding period. Structural weaknesses observed over 2018-2025:

- **Value trap in downtrends.** RSI stays oversold as the decline continues; the "buy oversold" signal accumulates losers in bear markets (Q4 2018, COVID 2020, 2022 bear). With no regime filter, v1 stays fully exposed, hence the 41.7% drawdown.
- **Equal-weight of the top-3 oversold.** The 3 most oversold ETFs are often the same ones in freefall; concentrating on them amplifies the loss tail.
- **PSR ≈ 0.** The 0.176 Sharpe is not statistically significant: indistinguishable from noise. Any edge claim would be misleading (rule C, PR-review-discipline §C).

The v2 (+ SMA200 filter) and v3 (+ 8% stop-loss) variants are designed to address these weaknesses but are not backtested here: an honest read documents the baseline variant and its honest verdict, without re-tuning. Re-optimizing the RSI thresholds, position count, or holding period to recover a positive Sharpe on this single window would be overfitting until proven otherwise (EPIC #9768, D2 "unfixed window"). The strategy is shipped with its parameters coded as-is, honest verdict rendered.

## Files

| File | Description |
|------|-------------|
| `main.py` | RSI(14) mean reversion with 3 variants (v1 pure RSI, v2 +SMA200 regime, v3 +8% stop-loss) on 11 GICS sector ETFs |

## References

- [QuantConnect Documentation](https://www.quantconnect.com/docs/)
- QC / Trading consolidation EPIC: #1621
- Governed by EPIC #9768 (backtest-metric drift across revisions)

See #1621 (partial contribution: honest-read of a previously-unaudited strategy).
