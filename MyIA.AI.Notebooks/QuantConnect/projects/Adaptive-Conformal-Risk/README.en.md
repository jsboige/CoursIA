# Adaptive-Conformal-Risk

**Asset class:** US Equities/ETF (multi-factor)
**Cloud project IDs:** `29841071` (original, ECE-student no-fee 2015-2026) · `33278416` (`1630-baseline-AdaptiveConformalRisk`, IBKR + aligned 2018-2025)
**Projects of measurement #21469:** `38121196` (current code, with the reference modes) · `38121126` (control, original code)
**Source:** ECE student project (El Bakkali, Gr02), adapted for the ESGF pool — Issue #238.

## Description

Adaptive Conformal Inference (ACI) risk overlay on multi-factor momentum. Implements the ACI algorithm (Gibbs & Candès, 2021) as a dynamic risk-management overlay: online alpha-adjustment widens/narrows the conformal prediction interval in response to recent coverage violations, and position size is set inversely to the interval width — wider interval (more uncertainty) means a smaller position. Applied over a 15-stock, 5-sector large-cap universe with a 15% volatility target and monthly rebalancing.

## Parameters

| Parameter | Values | Default | Role |
|---|---|---|---|
| `mode` | `strategy`, `spy`, `6040`, `ew15` | `strategy` | `strategy` keeps the code's decision; `spy` holds SPY at 100%; `6040` holds SPY at 60% and BND at 40%; `ew15` holds the 15 stocks of the universe at equal weight. The references are rebalanced at the start of each month, one minute after the open |
| `start_date` | date `%Y%m%d` | 2015-01-01 | start of the window |
| `end_date` | date `%Y%m%d` | 2026-01-01 | end of the window |

All four modes trace the portfolio value at each SPY open (chart `shadow`, series `e0` to `e4`). In reference mode, the strategy's daily update does nothing. SPY and BND are subscribed in reference mode only. Without parameters the strategy's decision is unchanged: the control below checks it order by order.

## Verdict against held references (#21469)

The protocol was written in #21469 before the first backtest, on the model of #21329. The two references of the verdict, SPY held and the 60/40, run inside the same algorithm as the strategy, under the same brokerage model. A third reference, the 15 stocks of the universe at equal weight (`ew15`), is a diagnostic and does not count in the verdict.

Two properties of the code are kept as they are:

- the strategy is not always 100% invested: the 15% volatility target can reduce the exposure, and the rest stays in cash;
- its first rebalance falls on the 21st session. It stays in cash for the first 21 sessions of each window, whereas the references are invested from the first one.

The compared series are the portfolio value at each SPY open. The tests go through `Paradox46Benchmarks/significance.py`, with a zero risk-free rate:

- Ledoit-Wolf Sharpe difference;
- stationary bootstrap;
- Newey-West difference of means.

On each window, the Holm correction covers the six p-values of the verdict. The diagnostic is a separate run, with its own Holm correction over three p-values.

Verdict rule, written before the measurement:

- `BEATS`: positive Sharpe difference, significant (Holm < 0.05) against both references;
- `NO BEATS`: strategy Sharpe below that of SPY held;
- `INCONCLUSIVE`: every other case.

**Harmlessness control: held.** In `strategy` mode, on the coded window, the instrumented code reproduces the backtest of the original code (`319338b45cae70aabe773a57cc0777b0`, project 38121126):

- 1,533 orders out of 1,533, with no difference in date, symbol or quantity;
- 27 QC statistics out of 27.

The strategy's orders are submitted at 9:40 New York time and filled at the close of the same day, on both windows; none is placed at midnight.

| Window | Sessions | Strategy Sharpe (zero rate) | SPY held (zero rate) | 60/40 (zero rate) | Holm p (Ledoit-Wolf, SPY / 60/40) | Verdict |
|---|---|---|---|---|---|---|
| Coded, 2015-01-02 → 2025-12-31 | 2766 | 0.888 | 0.803 | 0.837 | 1.0 / 1.0 | **INCONCLUSIVE** |
| Out of sample, 2026-01-02 → 2026-07-21 | 137 | 0.198 | 1.255 | 1.173 | 1.0 / 1.0 | **NO BEATS** |

QC statistics (computed by QC with its own risk-free rate). Their Sharpe ratios do not compare with those of the table above: QC subtracts a non-zero risk-free rate and starts from its own daily series, whereas the protocol uses a zero rate on the portfolio value at the open. The ranking of the portfolios can therefore change from one table to the other, and the verdict is read on the table above.

| Window | Mode | QC Sharpe (QC's rate, different scale) | CAGR | Max drawdown | Orders | Backtest |
|---|---|---|---|---|---|---|
| Coded | strategy | 0.583 | 13.15% | 30.9% | 1533 | `393e73a6fca6edabf1585e275381b055` |
| Coded | SPY held | 0.535 | 13.39% | 33.7% | 1 | `596d95b8eae1a9062771402d3dc65eed` |
| Coded | 60/40 | 0.451 | 8.86% | 21.7% | 221 | `c7a90f1e38874b2ca7785c11df233d38` |
| Coded | 15 stocks at equal weight | 0.891 | 22.88% | 35.1% | 1196 | `732abf4b8de0080d5c3cfcb02a93c6d2` |
| Out of sample | strategy | −0.086 | 3.49% | 8.5% | 69 | `362eada8ff0d63be8eaaecad9f281ab7` |
| Out of sample | SPY held | 0.865 | 19.08% | 8.9% | 1 | `a2e3ad4f1e1b41015b9c49aed0a43ad0` |
| Out of sample | 60/40 | 0.570 | 11.30% | 5.8% | 12 | `f141c04c23d40f7658d40e4c5153f665` |
| Out of sample | 15 stocks at equal weight | 1.108 | 22.20% | 8.4% | 81 | `6a9dee5d757418e42233aec2799a88dc` |

The out-of-sample backtest was requested up to 2026-10-19 but stops on 2026-07-21: the QC nodes used cut backtests about 90 days before the current date. Of its 137 sessions, the strategy spends 21 in cash, and the window has almost no power. No parameter was tuned on that period.

**Reading.** On the coded window the strategy has the highest point Sharpe of the three portfolios of the verdict. Its annual volatility (15.3%) holds its target and stays below that of SPY held (17.8%), for a close mean return (13.6% per year against 14.3%). The Sharpe difference is not significant: raw Ledoit-Wolf p 0.69 against SPY held, 95% bootstrap interval from −0.36 to +0.49. Out of sample its Sharpe falls below that of SPY held. The current code therefore beats neither reference measurably.

**Diagnostic: the 15 stocks at equal weight do better than the strategy.** On the coded window their zero-rate Sharpe is 1.161, against 0.888 for the strategy. The Sharpe difference is not significant (Holm p 0.33 for Ledoit-Wolf, bootstrap interval from −0.70 to +0.09). The difference in mean return is: 22.6% per year against 13.6%, Holm p 0.016 for Newey-West. Out of sample the order is the same (1.529 against 0.198, not significant). The rule written before the measurement says that a Sharpe below that of `ew15` means the overlay (momentum and conformal interval) adds nothing measurable to the choice of stocks. That is the case here. The strategy's return comes from its universe, chosen after the fact among the big winners of the decade, and not from the overlay, which reduces it.

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Adaptive-Conformal-Risk"`
**QC Cloud:** Deployed (see Cloud project IDs above). The `main.py` committed here is the canonical copy with `set_brokerage_model(IBKR, MARGIN)` (real fees).
**Measurement of 2026-10-19 (#21469):** see the section "Verdict against held references". The `mode`, `start_date` and `end_date` parameters are passed to the backtest.

## Backtest Metrics

Earlier measurements, on other QC projects and other windows. The current code, with the brokerage model of its `main.py`, gives a QC Sharpe of 0.583 on 2015-2026 (previous section).

| Metric | Value | Window / fees |
|--------|-------|---------------|
| Method | ACI risk overlay + 3-window multi-factor momentum | — |
| Rebalance | Monthly (daily ACI alpha update) | — |
| Sharpe | **0.449** | 2018-2025, IBKR real fees (#1630-aligned) |
| CAGR | 11.5% | 2018-2025, IBKR |
| MaxDD | 22.5% | 2018-2025, IBKR |
| PSR | 12.5% (non-significant) | 2018-2025, IBKR |
| Sharpe (prior, no-fee) | 0.604 | 2015-2026, default fee model (negligible) |

**#1630 caveat (verified 2026-06-23).** Two findings: (a) the low-turnover monthly rebalance + ACI vol-targeting make the overlay **fee-resistant** (0.449 with IBKR is only modestly below the 0.604 no-fee figure, and much of that gap is the harder aligned window) — confirming the #1630 *realized-turnover* discriminator; (b) **but the universe is Mag7-heavy** (AAPL/MSFT/NVDA/AMZN/TSLA = 5 of 7 Mag7), so the Sharpe is substantially Mag7 survivorship drift rather than the marginal value of the conformal overlay (same caveat class as EMATrend). Full analysis: `docs/qc/qc-comparative-backtests.md` finding #38 (See #1630).

The `ew15` diagnostic of #21469 measures finding (b): held at equal weight, the same 15 stocks have a higher Sharpe than the strategy.

## Files

- `main.py` — Strategy (ACI overlay + multi-factor momentum, IBKR brokerage).

## References

- Gibbs, I. & Candès, E. (2021), *Adaptive Conformal Inference Under Distribution Shift*. (The ACI online-alpha algorithm implemented here.)
- Romano, Y., Patterson, E. & Candès, E. (2020), *Conformalized Quantile Regression*. (Conformal-prediction interval framework.)
