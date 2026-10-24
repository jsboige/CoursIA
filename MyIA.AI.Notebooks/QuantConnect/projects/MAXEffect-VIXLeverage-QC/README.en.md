# MAXEffect-VIXLeverage-QC — long-only MAX effect with VIX-scaled leverage

English original of [README.md](README.md) (French is the primary documentation language of this repository).

Distillation of QC Research article 20886 "The MAX Effect with VIX-Based Leverage Scaling" (Derek Melchin, 2026-06-12), part of the `quantconnect.com/research` harvest (EPIC #11698, issue #22290, verdict **NOUVEAU** — no prior strategy in this repository carried the MAX effect).

## Idea

The **MAX(5)** factor of Bali, Cakici and Whitelaw (2011) [*Maxing Out: Stocks as Lotteries and the Cross-Section of Expected Returns*, Journal of Financial Economics 99(2), 427-446] takes, for each stock, the mean of its 5 largest daily returns over the last 21 sessions. High-MAX stocks behave like lottery tickets and **underperform** afterwards. This strategy sells that lottery — long-only:

- universe: filtered US equities (price > $5, market cap > $1B, average dollar volume > $5M, no REITs, no ADRs);
- **bottom** decile of the MAX factor, capped at 25 names, equal-weighted;
- monthly rebalance (first trading day of the month, 8:00 ET);
- VIX-driven leverage overlay: 1.5x when VIX <= 15, linearly down to 1.0x at VIX >= 30, rescaled continuously between rebalances (proportional rescale, relative weights unchanged).

The article reports Sharpe 0.57 (1998-01 -> 2026-06) versus 0.335 for SPY, with 25/25 parameter-sweep configurations beating their benchmark.

## Lag convention

The day-D VIX close is only delivered at D+1 (`CBOE.lag_days = 1`), the repository convention since the anti-lookahead measurements #19825/#19837: reading the same-day close at decision time is a lookahead. The VIX is loaded through a local `CBOE(PythonData)` class reading the public CBOE CDN CSV (the .NET namespace `QuantConnect.Data.Custom.CBOE` cannot be imported from a Python algorithm on QC Cloud).

## Measurements — QC Cloud, 2026-10-24 (project 38366686)

Window 2015-01-01 -> 2026-06-30 (daily series of 4,199 points, 2,847 effective trading days for the candidate), three modes from a single project. The Sharpe column is **QC's own statistic, computed with a non-zero risk-free rate** — verified below, and a correction to what the neighbouring ports of this collection state:

**Correction in flight (review #22330, 2026-10-24) — the `max-vix` row measures a compounding exposure path.** The leverage rescale of the measured version divided by `total_portfolio_value`: each line's weight was recomputed on the **current** exposure (already rescaled the previous time), so exposure **compounded** at every leverage change — 1.50 -> 1.45 yielded 2.17x instead of 1.45x, and returning to 1.0x de-risked nothing. The code is fixed in this PR (denominator = sum of held positions: target weights sum to exactly the requested leverage, so exposure = leverage x equity; verified on the sequence 1.50 -> 1.45 -> 1.50 -> 1.27 -> 1.27 -> 1.00, which yields 1.500 / 1.450 / 1.500 / 1.270 / 1.270 / 1.000). The `max-vix` figures below are therefore those of the **compounded** path, not of the strategy the prose describes; a control backtest on the corrected code will replace them, starting with 2019-2022 — the sub-window where compounding bites hardest. **The `max-only` ablation is unaffected** (fixed 1.0x leverage, the rescale is never reached), as is the `spy` reference (no overlay).

| Mode | Description | Sharpe | CAGR | Max drawdown | Backtest |
|---|---|---|---|---|---|
| `max-vix` | candidate (factor + VIX overlay) | 0.181 | 5.402% | 26.400% | `47d6ad9479ee72e8d8fda2e6fd6d8cd7` |
| `max-only` | ablation (factor only, 1.0x) | 0.288 | 6.124% | 25.900% | `3158bd546830303dc013f8763faf3b98` |
| `spy` | held reference (SPY buy-and-hold) | 0.551 | 13.739% | 33.500% | `b36253509d96547fb0b98baf8a1187eb` |

Candidate total: +83.16% ($100,000 -> $183,163.72); held SPY total: +339.68% ($100,000 -> $439,682.65); ablation total: +98.14% ($100,000 -> $198,139.26).

**Decomposition (factor only vs measured candidate).** The `max-only` ablation — same MAX(5) factor, same universe, same monthly rebalance, fixed 1.0x leverage without overlay — returns Sharpe **0.288** and CAGR **6.12%** where the measured candidate returns 0.181 and 5.40%, at nearly identical drawdown (25.90% vs 26.40%). Over the measured window the VIX overlay **subtracted** performance rather than adding any: −0.107 Sharpe and −0.72pp CAGR, buying no drawdown reduction. Two caveats bound this reading. (1) The candidate row measures the **compounded** path of the rescale bug (see correction above): part of that subtraction comes from the bug, not the overlay — the control backtest on corrected code will say how much. (2) The rotation gap — 32,697 orders and −$10,524 fees for the candidate against 4,550 orders and −$5,114 for the ablation — is likewise partly an artefact of the compounding rescale: every leverage change recomposed the whole target instead of aiming at the requested leverage. The factor alone does not beat the reference either (0.288 vs 0.551; 6.12% vs 13.74%): the missing edge is not carried by the overlay alone, it also sits in the long-only MAX factor over this window.

**The published Sharpe is not computed at a zero risk-free rate — a correction.** The neighbouring ports of this collection advertise a "zero risk-free rate Sharpe"; here, checking against the curve shows QC's figure is computed with a non-zero risk-free rate. The candidate's daily returns (the `Return` series, values in percent) do compound to the backtest total (1.8337 against 1.8458 on equity, a 0.7% rounding gap). Computed on the **2,881 sessions common** to both runs — the only ones where SPY returns a non-zero value — they give a zero-rate Sharpe of **0.518** for the candidate (annualized volatility **11.49%**) and **0.821** for SPY (**17.58%**, compounding to 4.3968, identical to the published +339.683%), where QC publishes 0.181 and 0.551. The gap is the risk-free rate: a constant equivalent rate of **3.9%/yr** reproduces the candidate's 0.181, **4.8%/yr** reproduces SPY's 0.551. QC therefore uses a time-varying rate, which two different implied rates say plainly.

**What that does to the comparison.** Both published Sharpes come from the same engine, over the same window, at the same rate: the 0.181 against 0.551 comparison is homogeneous, and the verdict does not depend on it. But the size of the gap does change: on a zero-rate basis the candidate sits **0.304** of Sharpe below the reference (0.518 against 0.821), not 0.370. Volatility is the other half of the fact: the candidate is **less volatile** than SPY (11.49% against 17.58%) — the leverage overlay does not make a riskier portfolio, it makes a slower one, whose return does not pay for the volatility it saved.

**Session counter — measured, not assumed.** QC reports 4,199 "tradeable dates" for the universe runs (candidate and ablation) against 2,889 for SPY, which looks like two different windows. The daily curves say otherwise: both runs cover the **same grid** of 4,199 and 4,200 points (2015-01-01 -> 2026-06-30), and on that grid SPY returns a non-zero value on **2,882 days** only — the order of magnitude of its counter (2,889). The two counters therefore measure different things (days of the series versus trading days for SPY), not two windows. The comparison does rest on a common window; it is the counter's label that is not homogeneous from one mode to the other. **The choice of basis is not cosmetic**: computed on the 4,199 days of the grid, the zero-rate Sharpes fall to 0.428 and 0.680 — exactly the expected √f factor (f = 0.686, √f = 0.828), since mean and dispersion do not contract at the same pace. That is a calendar dilution, not a property of the portfolio; the figures published here are therefore the session-based ones.

**Verdict: NO BEATS.** Over the measured window the candidate does not beat the held reference, in Sharpe (0.181 vs 0.551) nor in CAGR (5.40% vs 13.74%). One point runs the other way and is stated: the candidate's drawdown is lower than SPY's (26.40% vs 33.50%), the expected effect of the leverage overlay — less loss, but also less return. The candidate's return is carried by a single sub-window (2019-2022: 12.19% CAGR) while 2015-2018 is nearly neutral (0.79%) and 2023-2026-06 is weak (3.22%). **Decomposition delivered:** the `max-only` ablation (fixed 1.0x leverage, ID `3158bd54…`) returns Sharpe 0.288 and CAGR 6.12% — above the measured candidate (0.181 / 5.40%), below SPY (0.551 / 13.74%). The VIX overlay, as measured, subtracts; the factor alone does not carry enough to beat the reference. How much of that subtraction belongs to the compounding bug will be quantified by the control backtest.

**Gap test (block bootstrap).** On the 2,881 common sessions the zero-rate Sharpe gap (candidate − SPY) is **−0.304**. Circular block bootstrap with 21-session blocks, 10,000 draws, fixed seed (20261024), on the **paired** daily returns: 95% confidence interval **[−0.876 ; +0.189]**, one-sided p 0.116, two-sided p 0.258. Holm correction is the identity here — a single comparator, SPY, so no family of tests to correct.

**What this test establishes, and what it does not.** The interval contains zero: on this window, equality of the two Sharpes is not rejected at the 5% level. The NO BEATS verdict therefore does not rest on this test — it rests on the published statistics, which place the candidate below the reference on both measures (0.181 against 0.551; 5.402% against 13.739% CAGR). The test says something more modest and consistent with that: the observed gap is negative and of the order of 0.3, but eleven years of daily returns do not separate it from sampling noise. Publishing it as it stands is the only honest use of the number; withholding it would have suggested an established significance.

### Article claims confronted

The article announces Sharpe 0.57 over 1998 -> present against 0.335 for held SPY. This port measures 2015 -> 2026-06 (the cluster's window convention), so the confrontation bears on the **verdict** — does it beat the held reference on the same window, with the same fees? — not on the Sharpe level. The 0.181 measured over 2015-2026 already sits clearly below the article's 0.57 over a longer window, which suggests the claimed edge eroded over the recent period; the measured ablation (factor alone: 0.288, still below the reference) places the erosion in both storeys — the factor alone underperforms, and the measured overlay subtracts further; the overlay's share attributable to the compounding bug awaits the control.

## Structure

- `main.py` — `MAXEffectVIXLeverage(QCAlgorithm)`, `mode` parameter in {`max-vix`, `max-only`, `spy`}; MAX(5)/21-session factor in `SelectionData` (canonical QC tutorial pattern), local `CBOE(PythonData)` class at the bottom.
- Exposed parameters: `top_returns` (5), `max_portfolio_size` (25), `period` (21), `low_vix` (15), `high_vix` (30), `low_leverage` (1.5), `high_leverage` (1.0).

Related reading: [docs/qc/qc-strategies-status.md](../../../../docs/qc/qc-strategies-status.md) — repository strategy status.
