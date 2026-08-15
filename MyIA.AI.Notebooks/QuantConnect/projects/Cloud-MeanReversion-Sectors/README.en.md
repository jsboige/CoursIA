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

Fresh backtest via QC Cloud MCP, 2026-08-14 (`MeanReversion-v1-2018-2025-aligned-status-2026-08`, project 30822855, compile `BuildSuccess`, parameter `version=v1`, **1761 tradeable dates — #1630-aligned 2018-2025 baseline**, 273 orders):

| Indicator | Value | Reading |
|---|---|---|
| Sharpe ratio | **0.067** | near zero |
| CAGR | **3.793%** | below buy-and-hold SPY over the period |
| Max drawdown | **41.700%** | catastrophic (> 2× SPY) |
| Total net profit | **29.789%** (+$35,082) | over the period |
| PSR (Probabilistic Sharpe Ratio) | **0.147%** | indistinguishable from noise |
| Orders | 273 | real backtest |

**Verdict: NO-BEATS.** Sharpe 0.067, CAGR ~3.8% for a 41.7% drawdown, PSR ≈ 0: the strategy underperforms buy-and-hold SPY (double-digit CAGR over 2018-2025) with materially higher risk.

> **Measurement history (traceability):** (1) 2026-04-28 run on pre-#1630 code (2014-2025, 2768 days): v1 Sharpe 0.288 / DD 42.4%, v2 0.214, **v3 0.278 / DD 14.7%**; (2) 2026-08-07 run on the same stale code: v1 0.176 / DD 41.7%; (3) **the 2026-08-14 run above — the first on the #1630-aligned code (2018-2025)**: v1 0.067. The alignment drops the strong 2014-2017 years; pre-August figures cited in old catalogs (0.278 / 14.7%) are the **v3** variant over 2014-2025 — NO-BEATS holds across every window and variant, but the numbers are incomparable without a variant + period label.

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
