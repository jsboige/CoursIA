# HAR-RV-Kelly

**Asset class:** Multi-asset (Equities, Bonds, Commodities)

**Cloud project ID:** See `config.json` (local-id: 230839018)

## Description

HAR-RV (Heterogeneous Autoregressive Realized Variance, Corsi 2009) model for forecasting 5-day realized variance on six assets (SPY, EFA, EEM, TLT, GLD, DBC). Uses the Kelly Criterion at 1/4 fraction for position sizing based on the HAR forecast. Includes 5-day momentum direction. Model refit via OLS every 22 days on a 500-day rolling window. Weekly rebalance.

## How to Run

### Lean CLI
```bash
lean backtest --algorithm HAR-RV-Kelly/main.py
```

### QC Cloud
Open the cloud project (local-id: 230839018), compile and run a backtest.

## Backtest Metrics

| Method | Rebalance | Key Parameters |
|--------|-----------|----------------|
| HAR-RV + Kelly Criterion | Weekly | Kelly fraction 1/4, 5-day forecast, OLS refit every 22 days, 500-day window |

## Deterministic risk kernel (#24698)

The `kernel` parameter adds Steward's deterministic risk kernel (arXiv 2610.30557) to the strategy. The reference port of this kernel in the repository is the `DeterministicRiskKernel-QC` project. With the default value, `kernel=off`, the strategy code is unchanged.

| `kernel` | 90 % exposure cap | 2 ATR(14) stop | −3 % circuit breaker |
|---|---|---|---|
| `off` (default) | no | no | no |
| `cap90` | yes | no | no |
| `kernel_nocb` | yes | yes | no |
| `kernel` | yes | yes | yes |

On six lines rebalanced every Monday, the kernel works as follows:

- **the cap** brings the sum of the weights down to 0.90 when it is higher. The original normalisation, which brings this sum down to 1, runs before it. The cap applies to the order: between two Mondays, rising prices can lift the measured exposure up to 0.917;
- **the stop** is a `StopMarket` order placed 2 ATR(14) below the price at order time, on each line bought. It is placed again at every rebalance. A stopped line stays flat until the next Monday; the other lines stay in place;
- **the circuit breaker** reads the close. If the portfolio value loses 3 % or more over the session, every line is sold at the next open (`MarketOnOpen`). The following session is spent flat, then the weights of the current Monday are taken back;
- **Steward's sizing rule** (0.5 % of capital at the stop) is not implemented. A line keeps its Kelly size, capped at 0.30.

The scale defect reported in #26329 is not fixed here: in the code, the annual variance is underestimated by a factor of 5. The kernel is measured on the code as it is.

### Measurements

Five backtests run on 2026-11-13 in the course backtest space, all over the coded window: 2015-01-01 → 2025-01-01, i.e. 2516 tradeable dates. The `bare` run executes the `main.py` of `0ddc1e46fd`, before the kernel was added (QC project 39328653, compile `93edc4052254b0197f7483fb5a12f230-6725a12c2c2991872db58f69a7accbee`). The other four runs execute the code of this PR (QC project 39328660, compile `08a275404053555c3da676b2590e98d2-9889056cf07ad03339281937e1ce3e09`). Both compiles are `BuildSuccess`. Both codes were uploaded then read back, with a fingerprint check (sha256 `c80afa6189cd…` and `706eef6cefa3…`).

| `kernel` | Backtest | Orders | Sharpe (QC) | CAGR | Max drawdown | Net profit | PSR | Stops | Cuts | Max exposure | Flat sessions |
|---|---|---|---|---|---|---|---|---|---|---|---|
| bare code | `995560424f5e0f6e18ff84a126d03bb3` | 1358 | 0.065 | 3.470 % | 15.7 % | 40.681 % | 0.018 % | — | — | — | — |
| `off` | `c700ad0175a8c8012d5865c2cb7f7379` | 1358 | 0.065 | 3.470 % | 15.7 % | 40.681 % | 0.018 % | 0 | 0 | 1.0191 | 523 / 2516 (21 %) |
| `cap90` | `be3cbb6e8e7d06918de3264259b2f049` | 1355 | 0.060 | 3.430 % | 15.5 % | 40.147 % | 0.016 % | 0 | 0 | 0.9173 | 523 / 2516 (21 %) |
| `kernel_nocb` | `021617f247331e060dcf06731c3892c2` | 2163 | −0.025 | 2.781 % | 12.6 % | 31.584 % | 0.004 % | 222 | 0 | 0.9174 | 629 / 2516 (25 %) |
| `kernel` | `5713297bb5e872b36e7b7b80d4a9090c` | 2164 | −0.022 | 2.809 % | 12.4 % | 31.945 % | 0.005 % | 222 | 2 | 0.9174 | 631 / 2516 (25 %) |

The order count includes cancelled stops: every rebalance cancels a line's stop before placing it again. On `kernel_nocb` there are 1158 filled rebalancing orders, 222 filled stops, 782 cancelled stops, and one stop still live at the end of the window. The two cuts of `kernel` start from the closes of 2020-06-11 and 2022-03-09. The 222 stops spread between 16 and 36 per year. The first order is dated 2016-01-11. Before that date, a line is not traded until it has 500 realised variances; this flat year counts in the flat sessions of every mode.

**Controls.** The `off` run returns the same 1358 orders as the bare code (same date, ticker, quantity and type, one by one) and the same statistics: the kernel code changes nothing when it is disabled. These two runs do not reproduce the line published in `docs/qc/qc-strategies-status.md`, which gives a Sharpe of 0.146, a CAGR of 4.23 % and a drawdown of 12.8 % over the same window. The code has not changed; the cause of the gap is not established.

**Paired test.** `Paradox46Benchmarks/significance.py` runs on the daily returns of the `shadow` traces (2516 sessions, zero risk-free rate). It computes the Ledoit-Wolf Sharpe difference, the Newey-West mean difference and a stationary bootstrap (2000 draws, blocks of 10, seed 0), then corrects the p-values with Holm. The QC Sharpe deducts a risk-free rate; the trace Sharpe, computed at a zero rate, is of another order.

| Mode against `off` | Mode Sharpe | `off` Sharpe | Difference | Correlation | Ledoit-Wolf p | 95 % bootstrap CI | Newey-West p | Holm p |
|---|---|---|---|---|---|---|---|---|
| `cap90` | 0.506 | 0.491 | +0.014 | 0.999 | 0.353 | [−0.016; 0.043] | 0.650 | 1.0 |
| `kernel_nocb` | 0.471 | 0.491 | −0.020 | 0.906 | 0.880 | [−0.280; 0.239] | 0.432 | 1.0 |
| `kernel` | 0.476 | 0.491 | −0.016 | 0.906 | 0.906 | [−0.279; 0.244] | 0.450 | 1.0 |

### Reading

- **The cap bites often, but weighs little.** Under `off`, gross exposure is above 0.95 after 29 % of the 395 rebalances that send orders, and between 0.85 and 0.95 after 16 % of them. This exposure is taken at the fill price and divided by the value at that day's close. Bringing those weeks down to 0.90 costs only 0.04 point of CAGR and gains only 0.2 point of drawdown. The Sharpe difference is not significant.
- **The stop trades return for drawdown.** The drawdown goes from 15.7 % to 12.6 % and the CAGR from 3.47 % to 2.78 %, a fifth of the annual return. The point Sharpe falls. The 222 stops add 106 fully flat sessions to those of `off`, and take many more sessions away from single lines.
- **The circuit breaker is almost inert**: two cuts in ten years, for +0.028 point of CAGR and −0.2 point of drawdown against `kernel_nocb`.
- **No difference is significant.** The stop decorrelates the trace (0.906), which widens the bootstrap interval to about ±0.26 around the difference.

**Verdict: NO BEATS** for `kernel` and `kernel_nocb`, whose point Sharpe is below that of `off`. Verdict **INCONCLUSIVE** for `cap90`, whose positive difference is not significant (Holm p 1.0).

**Predictions written before the runs** (`[CLAIMED]` comment of #24698):

1. Harmlessness holds: **held**.
2. The cap bites often and lowers CAGR and drawdown, with no significant Sharpe difference: **held**, with a smaller effect than expected.
3. The stop lowers the drawdown at a close CAGR: **partly wrong**. The drawdown does fall, but the CAGR loses a fifth of its value.
4. The circuit breaker is almost inert: **held**.
5. `kernel` against `off` gives INCONCLUSIVE: **wrong**. The point Sharpe of `kernel` is lower, hence NO BEATS, with no significance either way.

**Contrast.** Three portfolios now carry the kernel:

| Project | Portfolio | Stop cost on CAGR | Drawdown gain |
|---|---|---|---|
| `Cloud-VolTargeting` | one line, monthly rebalance | heavy: CAGR halved over 2007-2026 | 6.1 to 6.4 points |
| `HAR-RV-Kelly` | six lines, Monday rebalance | intermediate: 0.7 point, a fifth of the CAGR | 3.1 points |
| `DeterministicRiskKernel-QC` (#25221) | ten ETFs, weekly rebalance | almost none | clear |

Here, a stop empties a single line, and at most until the next Monday. One hypothesis, not measured, would explain the intermediate cost: the strategy's return is low (3.5 % a year), so each week a stopped line loses takes a larger share of it.

Possible follow-ups, not measured: rerun the ablation once the scale defect is fixed (#26329), try a wider stop or a re-entry within the week, and measure the 2025-2026 window.

## Files

| File | Description |
|------|-------------|
| `main.py` | HAR-RV volatility forecasting with Kelly Criterion sizing on 6 multi-asset ETFs |
| `config.json` | Project configuration (local-id) |
| `research.ipynb` | Research notebook with HAR-RV model analysis and Kelly fraction exploration |

## References

- Corsi, F. (2009). *A Simple Approximate Long-Memory Model of Realized Volatility*. Journal of Financial Econometrics.
- Kelly, J.L. (1956). *A New Interpretation of Information Rate*. Bell System Technical Journal.
- [QuantConnect Documentation](https://www.quantconnect.com/docs/)
