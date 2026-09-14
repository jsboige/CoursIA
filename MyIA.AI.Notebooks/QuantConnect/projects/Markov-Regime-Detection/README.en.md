# Markov-Regime-Detection

**Asset class:** US Equities/ETF (SPY, TLT, GLD)
**Cloud project ID:** `36387308`

## Description

Markov regime detection using statsmodels MarkovRegression. Identifies 2-regime (bull/bear) states on SPY returns, rotates monthly between SPY (calm regime) and TLT (turbulent regime), with a constant 10% GLD sleeve.

**Consolidated from ML-HMM-Regime** (near-identical copy with same class name, same k_regimes=2, same allocation logic).

## Fear & Greed overlay (v1.2, #15534)

The project consolidates QuantConnect research article [#19465](https://www.quantconnect.com/research/19465/filtering-trades-with-the-fear-and-greed-index/) as an **optional overlay**, gated by the `use_feargreed` parameter (default `0` = v1.1 behavior strictly unchanged).

**Primary source**: Huang, Jiang, Tu & Zhou (2015), "Investor Sentiment Aligned: A Powerful Predictor of Stock Returns", *Review of Financial Studies* 28(3), 791-837 — aligned investor sentiment as a powerful return predictor. The QuantConnect article remains the operational entry point; this reference is its primary academic source.

**Mechanism**: the same tool as the main regime (`MarkovRegression`, `k_regimes=2`) is fit on the trailing Fear & Greed history, and SPY exposure is **halved** when the SPY regime asks for risk but the index regime sits in its greedy state (the remainder stays in cash — never TLT, which would blend two regime signals). The greedy state is identified by its **higher fitted mean**, never by a hardcoded regime number, so a regime renumbering across fits cannot silently flip the filter.

**Dataset**: `FearGreedIndex`, exposed by the `AlgorithmImports` wildcard (no explicit import), ticker `"FG"`. Availability probed on QC Cloud 2026-09-11: >= 2500 daily rows delivered through Dec 2025, coverage from July 2014, not gated.

**Seeds**: the article's seed sweep (30-50) has no object here — the article drew random trades, whereas this strategy is a deterministic monthly rotation whose `MarkovRegression` fit depends on no seed. Robustness is therefore tested by **market sub-periods** instead.

## How to Run

**QC Cloud:** project `36387308`. Parameters: `use_feargreed` (0/1), `start_year`/`end_year`, `lookback_years` (default 3).
**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Markov-Regime-Detection"`

## Backtest Metrics

Measured 2026-09-11 on QC Cloud, Interactive Brokers fees kept in both arms (unlike the article, which removed them via `ConstantFeeModel(0)`), monthly rebalance. Arm A is the baseline (`use_feargreed=0`), arm B the variant (`use_feargreed=1`); each window is an independent run (not a slice of the full run), since the 3-year warm-up and the regime state are not carried across windows.

| Window | Arm | Sharpe | CAGR | MaxDD | Net profit | Net profit ($) | PSR | Orders |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| 2015-2026 | A — baseline | 0.290 | 7.182% | 23.700% | 114.572% | 74,574.09 | 0.197% | 103 |
| 2015-2026 | B — variant | 0.019 | 3.318% | 26.300% | 43.243% | 23,093.34 | 0.004% | 105 |
| IS 2015-2020 | A — baseline | 0.229 | 4.735% | 16.700% | 26.038% | 14,496.06 | 1.859% | 44 |
| IS 2015-2020 | B — variant | 0.051 | 2.653% | 14.500% | 13.996% | 7,532.51 | 0.526% | 45 |
| OOS 2021-2026 | A — baseline | 0.297 | 8.991% | 23.700% | 53.825% | 26,626.13 | 2.596% | 41 |
| OOS 2021-2026 | B — variant | -0.123 | 3.278% | 22.500% | 17.510% | 2,344.36 | 0.121% | 42 |

**Verdict: NO BEATS in all three windows.** The overlay degrades Sharpe (to negative out-of-sample), CAGR and net profit everywhere. The one metric where B does better is IS drawdown (14.500% against 16.700%), a mechanical consequence of halved exposure rather than a better signal. The order count is nearly identical within each window (103/105, 44/45, 41/42), the expected behavior of an overlay that only changes the **exposure weight** and never the decision frequency — turnover is not exposed by the reading tool (qc-mcp-lite maps six statistics), so the order count is the declared proxy.

## Files

- `main.py` - Strategy (v1.2, Markov regime + optional Fear & Greed overlay)
- `README.md` - French version
