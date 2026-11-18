# DualMomentumNoTLT — Dual momentum without TLT (Antonacci variant)

**Asset class:** Multi-asset (SPY, QQQ, IEF, GLD, XLP)
**Cloud project ID:** 31244186 (Framework variant)
**Measurement #21669 projects:** `38183910` (current code, with the reference modes) · `38183905` (control, original code)
**Backtested period:** 2015-01-01 → 2024-12-31

French (canonical) version: [README.md](README.md).

## Description

A **dual momentum multi-asset rotation** strategy (Gary Antonacci, *Dual Momentum Investing*, 2014) **excluding long-term bonds (TLT)**. The **absolute** momentum (12-month return > 0) filters out assets in a negative trend; the **relative** momentum selects the 2 best 12-month returns among the survivors, with equal weighting (50 % each). If no asset passes the absolute filter, the portfolio goes entirely to cash.

**Why "No TLT"?** TLT (long-term US bonds, ~20+ years) lost ~40 % during the 2020-2023 rate-hike cycle. This variant replaces the long duration with IEF (intermediate 7-10 year bonds), GLD (gold) and XLP (consumer staples) as diversifiers. The **pedagogical trade-off**: dropping TLT avoids the duration loss when rates rise, **but** it also removes a *flight-to-quality* shelter during equity crashes (TLT rose in March 2020). The compromise is visible in the drawdown (see the honest reading below).

## Strategy Logic

| Component | Parameter | Role |
|-----------|-----------|------|
| Universe | SPY, QQQ, IEF, GLD, XLP | 5 diversified assets |
| Lookback | 252 trading days (12 months) | Momentum measurement |
| Absolute filter | 12M return > 0 | Skip negative momentum |
| Selection | Top 2 by 12M return | Relative momentum |
| Weighting | Equal weight | 50 % per position |
| Rebalance | Monthly | Calendar rebalance |

## Real backtest (QC Cloud, Framework variant, IBKR margin fees included)

This README long displayed a Sharpe of 0.633, a CAGR of 16.91 % and a drawdown of 34.50 % for this variant (QC project 31244186, 2238 orders, 2026-08-06). Those figures came from a code defect, corrected in [#20388](https://github.com/jsboige/CoursIA/issues/20388):

- `InsightWeightingPortfolioConstructionModel` ignores insights that carry no weight. The `FLAT` insights of `DualMomentumAlpha` carried none: the previous `UP` target stayed in place, and a line leaving the top-2 was never sold.
- The account is on margin by default. Lines therefore accumulated on credit: before 104 of 120 issuances, the portfolio held all 5 symbols, and its gross exposure reached 1.71 times net value at period end. Some purchases even exceeded the available margin: 282 buy orders rejected for insufficient buying power.
- Fix: the `FLAT` insights carry `weight=0`. The same fix takes over the bar guard (#20264) and the doubled history request (#20286) of the standalone variant, described below.

Measurement on the QC nodes, brokerage fees included, seven predictions fixed before the backtests ([#20388, c.6200954314](https://github.com/jsboige/CoursIA/issues/20388#issuecomment-6200954314)), all held ([result, c.6201190294](https://github.com/jsboige/CoursIA/issues/20388#issuecomment-6201190294)):

| Window | Variant | Sharpe | CAGR | Max drawdown | Orders | Rejected | Lines held | Gross exposure | Backtest |
|---|---|---|---|---|---|---|---|---|---|
| 2015-01-01 → 2024-12-31 (coded) | before | 0.633 | 16.89 % | 34.4 % | 2225 | 282 | 5 before 104 of 120 issuances | 1.71 at period end | `0f8e0f58df1b2dc01eeb20d35cde65f9` |
| | after | 0.442 | 10.00 % | 21.5 % | 1410 | 0 | 2 at most | 0.998 at most | `02551c21423f1aa958678303eca6ec2b` |
| 2025-01-01 → 2026-07-10 (out of sample) | before | 1.17 | 35.03 % | 16.0 % | 396 | 0 | 4 in 16 of 19 issuances | 1.68 at most | `36c1d64eef77b6a5552ae4616d56e240` |
| | after | 1.20 | 29.94 % | 13.9 % | 374 | 0 | 2 | 0.998 at most | `c0081f5801967cd1880997c1c67f5b1e` |

Sharpe computed by QC, risk-free rate included. The "before" line of the coded window is the reference backtest of #20264, which runs the code of project 31244186 (2225 orders against 2238 in the historical table of August 6; these two distinct executions are not conflated, and the cause of this gap is not established here). Lines held and gross exposure are reconstructed from the fills, just before each issuance; cash there does not count dividends, so the exposure is an upper bound.

### Honest reading — the 16.9 % CAGR came from leverage, not from the signal

Once the defect is fixed, the Framework variant converges with the fixed standalone variant: Sharpe 0.442 vs 0.446, CAGR 10.00 % vs 10.05 %, drawdown 21.5 % vs 21.4 %. The strategy **no longer beats SPY** in absolute return over 2015-2024: SPY held in the same algorithm makes 12.97 % a year, and the strategy does not beat it in Sharpe either (measurement #21669, section "Verdict against held references"). Out of sample, the CAGR drops from 35.0 % to 29.9 % for the same reason, and the Sharpe does not drop.

- **Drawdown of 21.5 %**, vs 34.4 % before the fix: the gap comes mostly from the leverage. It stays above that of the AQR Trend-Following (MaxDD 15 %), which switches to an explicit safe haven in a bear regime. Without the long duration as a *flight-to-quality* shelter, dual momentum **spins** in the falling assets; it does not **flee**. The drawdown date is not measured here.
- **PSR at 1.4 %** on the coded window: the probability that the Sharpe ratio is **statistically above zero** is low. The observed return is **not** evidence of predictive skill; it is largely explained by the tech momentum exposure (QQQ) during an atypical bull decade.
- **Fees**: $1,606 over ten years for the Framework variant, vs $434 for the standalone one (`a32a1a24f317c96e5d0fe2bbb00ca583`). Without a rebalancing function, the portfolio construction model re-targets the active lines every day and sends small adjustments: 1410 orders vs 239, 90 % of them off the issuance days.

**Honest conclusion**: do NOT present this strategy as a statistically significant alpha generator. It is a **managed momentum beta**, with a higher drawdown than a strategy with a defensive switch — the pedagogical example of the limit of dual momentum "pure rotation" without a protection overlay. The defect fixed above gives a second lesson: a CAGR that beats the market is first checked on the held positions, before being attributed to the signal. The natural companion is DualMomentum (with TLT) — a documented counter-example (TLT sabotaged 2020-2023) — see [DualMomentum/README](../DualMomentum/README.md). The two illustrate the **same compromise**: a diversifier that helps in one regime hurts in the other.

## Standalone variant (`main.py`): rebalance moved out of the midnight slice (#20264)

In daily data, Lean delivers dividend notices in a slice dated midnight, which carries no trading bar. IEF pays a dividend every month, and its notice often falls on the first trading day. The month guard of `main.py` was then consumed on that slice: the rebalance decided on the previous day's prices, and its orders left at midnight to be executed at the open. On the coded window, 109 rebalances out of 120 fell at midnight.

Fix in `main.py`: the month is only consumed on a slice carrying a bar of a universe symbol. Measured on QC nodes, brokerage fees included, protocol fixed before the backtests ([#20264, c.6115262186](https://github.com/jsboige/CoursIA/issues/20264#issuecomment-6115262186)):

| Window | Variant | Midnight orders | Sharpe | CAGR | Max drawdown | Orders | Backtest |
|---|---|---|---|---|---|---|---|
| 2015-01-01 → 2024-12-31 (coded) | before | 210 (101 days) | 0.339 | 8.08% | 23.6% | 233 | `a09a48809bcb4dc878e84f511dc00d65` |
| | after | 0 | 0.441 | 9.96% | 21.4% | 234 | `b2ff070974e440f64029c69473bb7af7` |
| 2025-01-01 → 2026-07-10 (out of sample) | before | 38 (17 days) | 1.094 | 28.02% | 14.1% | 42 | `a5a68f401f9cca13dda2a39dfd02d416` |
| | after | 0 | 1.203 | 30.23% | 14.0% | 42 | `bbf5126ce1eac446800cedc56c04f546` |

Sharpe computed by QC, risk-free rate included. Out of sample, the rule fixed in advance gives **no degradation**.

### Half sessions: the two missing months (#20286)

The fix above makes the rebalance decide on the first bar of the month. In July 2017 and July 2023, that bar is the Monday July 3rd one, a half session closing at 1:00 pm. On that slice, a daily-history request by bar count returns about 21 fewer bars than requested. The length guard then discarded the five symbols, and those two months went by without rebalancing.

`main.py` now requests twice as many bars and keeps the most recent ones. On a full session these are the same bars as before. Measured on QC nodes, protocol and predictions fixed before the backtests ([#20286, c.6131650205](https://github.com/jsboige/CoursIA/issues/20286#issuecomment-6131650205)). The "before" line is the "after" line of the previous table:

| Window | Variant | Rebalanced months | Sharpe | CAGR | Max drawdown | Orders | Backtest |
|---|---|---|---|---|---|---|---|
| 2015-01-01 → 2024-12-31 (coded) | before | 118 / 120 | 0.441 | 9.96% | 21.4% | 234 | `b2ff070974e440f64029c69473bb7af7` |
| | after | 120 / 120 | 0.446 | 10.05% | 21.4% | 239 | `a32a1a24f317c96e5d0fe2bbb00ca583` |
| 2025-01-01 → 2026-07-10 (out of sample) | before | 19 / 19 | 1.203 | 30.23% | 14.0% | 42 | `bbf5126ce1eac446800cedc56c04f546` |
| | after | 19 / 19 | 1.203 | 30.23% | 14.0% | 42 | `91eae7e7741ff46af96b5cd83dbccc5a` |

The four predictions hold:

- the two July Mondays now have their `REBAL` line, and those are the only added dates;
- up to June 30th 2017, the orders are identical to the previous ones;
- out of sample, no first bar of a month is a half session, and the result is identical to the cent (same orders, same statistics).

On July 3rd 2017, the selection does not change (QQQ and SPY): the rebalance only adjusts quantities. On July 3rd 2023, it sells gold and moves to QQQ and SPY one month earlier than the before variant. The Sharpe gap (+0.005) stays below the 0.05 threshold fixed in advance.

These figures cover the standalone variant. They are not a strategy verdict: this is the correction of two defects, measured on windows already seen. The Framework variant (`alpha_model.py`) received the same two fixes in #20388, measured together with the `FLAT`-insights one in the table above.

## Standalone variant parameters

| Parameter | Values | Default | Role |
|---|---|---|---|
| `mode` | `strategy`, `spy`, `6040`, `ew5` | `strategy` | `strategy` keeps the code's decision; `spy` holds SPY at 100 %; `6040` holds SPY at 60 % and BND at 40 %; `ew5` holds the five universe symbols at equal weight. The references are rebalanced at the start of each month, one minute after the open |
| `start_date` | date `%Y%m%d` | 2015-01-01 | start of the window |
| `end_date` | date `%Y%m%d` | 2024-12-31 | end of the window |

The four modes trace the portfolio value every day at the SPY open (graph `shadow`, series `e0` to `e4`). In reference mode, `on_data` returns immediately: the strategy decides nothing. BND is subscribed only in `6040` mode. Without parameters, the strategy's decision does not change: the control below verifies it order by order.

## Verdict against held references (#21669)

The protocol was written in #21669 before the first backtest, on the model of #21329 and #21594. The two references of the verdict, SPY held and the 60/40, run in the same algorithm as the strategy, under the same brokerage model. A third reference, the five universe symbols at equal weight (`ew5`), serves as a diagnostic and does not count in the verdict: it asks whether the momentum rule adds anything to simply holding the same symbols.

Four properties of the code are kept as-is:

- the strategy holds at most two symbols: two at 50 % each, or one at 100 % when only one 12-month return is positive. Its risk is concentrated; `ew5`'s is spread over five symbols;
- it is not always invested. On the coded window, exposure is zero from 2023-03-02 to 2023-04-04: a full month in cash, the only case where the code goes to cash being that no 12-month return is positive. After the coded window, it is so only on the very first days, before the first fill;
- the account is declared on margin. The target weights sum to at most 100 %, and the observed exposure barely exceeds 1: at most 1.0089 on the coded window (January 2019), above 1 on 182 of the 3,654 daily points of QC's exposure chart. After the coded window, the maximum is 1.0006 (April 2025), on 30 of 569 points;
- the strategy's orders are submitted at the close of the month's first session: 4 pm New York time, 1 pm on the two half-session days (July 3rd 2017 and July 3rd 2023, see #20286). Lean turns them into market orders at the open, filled at the next session. None was sent at midnight.

The compared series is the portfolio value at each SPY open. The tests go through `Paradox46Benchmarks/significance.py`, with a zero risk-free rate:

- Ledoit-Wolf Sharpe gap;
- stationary bootstrap;
- Newey-West mean gap.

On each window, the Holm correction applies to the six p-values of the verdict. The diagnostic is a separate run, with its own Holm correction over three p-values.

Verdict rule, written before the measurement:

- `BEATS`: positive and significant Sharpe gap (Holm < 0.05, Ledoit-Wolf) against both references;
- `NO BEATS`: strategy Sharpe below that of SPY held;
- `INCONCLUSIVE`: all other cases.

**No-harm control: held.** In `strategy` mode, on the coded window, the instrumented code reproduces the backtest of the original code (`b91de30a86a6396f2782b7e56a86a0ea`, project 38183905):

- 239 orders out of 239, no gap in date, symbol or quantity;
- 27 QC statistics out of 27. These are also the ones published above for the standalone variant after #20286 (QC Sharpe 0.446, CAGR 10.05 %, 239 orders).

| Window | Sessions | Strategy Sharpe (zero rate) | SPY held (zero rate) | 60/40 (zero rate) | p Holm (Ledoit-Wolf, SPY / 60/40) | Verdict |
|---|---|---|---|---|---|---|
| Coded, 2015-01-02 → 2024-12-31 | 2516 | 0.730 | 0.786 | 0.802 | 1.0 / 1.0 | **NO BEATS** |
| Out of sample, 2025-01-02 → 2026-07-22 | 388 | 1.558 | 1.063 | 1.180 | 1.0 / 1.0 | **INCONCLUSIVE** |

QC statistics (computed by QC with its own risk-free rate). Their Sharpes do not compare with those of the table above: QC subtracts a non-zero risk-free rate and starts from its own daily series, while the protocol takes a zero rate on the portfolio value at the open. The verdict is read on the table above.

| Window | Mode | QC Sharpe (QC rate, other scale) | CAGR | Worst decline | Annual std-dev | Orders | Backtest |
|---|---|---|---|---|---|---|---|
| Coded | strategy | 0.446 | 10.05 % | 21.4 % | 0.122 | 239 | `2bb5cfd719626bf4252a4833f4feaf96` |
| Coded | SPY held | 0.533 | 12.97 % | 33.7 % | 0.146 | 1 | `4435593eb600049559cad42ed343f1c7` |
| Coded | 60/40 | 0.442 | 8.41 % | 21.7 % | 0.090 | 201 | `20df703f10f503d24122776e7c609ede` |
| Coded | five symbols equal weight | 0.569 | 9.85 % | 19.3 % | 0.087 | 413 | `31518a3b58f0320aa90e08676b4cc037` |
| Out of sample | strategy | 1.103 | 27.96 % | 14.0 % | 0.142 | 42 | `60c267120580e1ad4bdf04cf86bc46b4` |
| Out of sample | SPY held | 0.646 | 18.37 % | 18.7 % | 0.145 | 2 | `9d779079ddb90e09ca96bce567b16c38` |
| Out of sample | 60/40 | 0.546 | 12.68 % | 11.2 % | 0.089 | 30 | `5976aca33047764d68a33189a99e2538` |
| Out of sample | five symbols equal weight | 0.899 | 17.47 % | 8.8 % | 0.090 | 70 | `b167db74c6736815fbcf55c6b44ff73d` |

The out-of-sample backtest was requested until 2026-10-20, but it stops on 2026-07-22: the QC nodes used cut backtests about 90 days before the current date. Over its 388 sessions, the window has little power. No parameter was tuned on this period.

**Reading.** On the coded window, the strategy has the lowest point Sharpe of the three verdict portfolios: 0.730 vs 0.786 for SPY held and 0.802 for the 60/40. No gap is significant (raw Ledoit-Wolf p 0.77 and 0.72, 95 % bootstrap intervals from −0.45 to +0.28 against SPY and from −0.48 to +0.28 against the 60/40), but the rule does not require a test for this case: the Sharpe is below that of SPY held, the verdict is `NO BEATS`. Out of sample, the strategy has the highest point Sharpe (1.558 vs 1.063 and 1.180). The gap is significant against no reference (raw p 0.49 and 0.60, bootstrap interval against SPY from −1.05 to +1.88): `INCONCLUSIVE`, as announced in the protocol for a window so short.

**Diagnostic: the momentum rule adds nothing measurable to holding the five symbols.** On the coded window, the five symbols held at equal weight have a zero-rate Sharpe of 0.957, vs 0.730 for the strategy. The gap (−0.227) is not significant (Holm p 0.631 for Ledoit-Wolf, bootstrap interval from −0.60 to +0.11); per the rule written before the measurement, a Sharpe below that of `ew5` is enough to conclude the rule adds nothing measurable. The gap comes from risk, not return: the two portfolios have a similar CAGR (10.05 % and 9.85 %), but the strategy, concentrated on two symbols, has an annual std-dev of 0.122 vs 0.087. Out of sample, the two Sharpes are almost equal (1.558 and 1.550, gap +0.008, Holm p 1.0). The momentum chooses which symbols to hold; on these two windows, that choice does no better than holding them all.

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/DualMomentumNoTLT"` (standalone variant, `main.py`).
**QC Cloud:** for the Framework variant, deploy `main_framework.py` under the name `main.py`, with `alpha_model.py`. QC project 31244186 carries this variant in its pre-#20388 version.
**2026-10-20 measurement (#21669):** see the "Verdict against held references" section. The `mode`, `start_date` and `end_date` parameters are passed to the standalone variant's backtest.

## Architecture

The project ships **two implementations** of the same strategy:

- **`main_framework.py` + `alpha_model.py` (Framework)** — QC AlphaModel version: `DualMomentumAlpha` (monthly issuance of 30-day price insights) + `InsightWeightingPortfolioConstructionModel` + `ImmediateExecutionModel`. This is the variant measured in the table above. Its docstring targets a "Sharpe within ±15 % of the standalone"; after #20388, the measured gap is 1 %.
- **`main.py` (standalone)** — direct `QCAlgorithm` version that rebalances the positions once a month, without going through insights. This is the one `lean backtest` runs.
- `config_framework.json` — QC Framework configuration.
- `quantbook.ipynb` — research (momentum signal analysis).
- `dual_momentum_notl_analysis.png` — analysis figure.

**What still distinguishes the two variants**: the order count. Without a rebalancing function, `InsightWeightingPortfolioConstructionModel` recomputes its targets every day while the insights are active, and sends a small adjustment as soon as prices have drifted the weights: 1410 orders in ten years vs 239 for the standalone variant, and $1,606 of fees vs $434. Passing a monthly rebalancing function to the portfolio construction model is a pertinent pedagogical exercise; it is not measured here.

## Concepts taught

- **Dual momentum** (Antonacci 2014): combination of an **absolute** filter (return > 0) and a **relative** ranking (top-N).
- **Diversification trade-off**: the same asset (TLT) can be a nuisance in one regime (rate hikes) and a shelter in another (flight-to-quality) — removing a diversifier is a bet on the future regime.
- **Momentum rotation vs safe-haven switch**: comparing this strategy's drawdown (21.5 %, pure rotation) to the Trend-Following's (15 %, with a safe-haven switch) isolates the value of the defensive overlay.
- **Probabilistic Sharpe Ratio (PSR)**: a positive Sharpe ≠ statistically significant skill (1.4 % here).
- **Framework vs standalone variant**: the same strategy statement can yield different metrics depending on the QC harness. Here, an unweighted `FLAT` insight, ignored by the portfolio construction model, let the account carry up to 1.7 times its net value; once fixed, what remains is the turnover gap due to the daily re-targeting.

## References

- Antonacci (2014), Dual Momentum Investing
