# Framework Composite - MomentumSector + RegimeSwitching

## Description

Composite strategy combining two complementary approaches via QuantConnect Algorithm Framework:

1. **SectorMomentum (60% slice)**: Dual momentum among SPY/IEF/GLD
   - Multi-lookback composite score (1/3/6/12 months)
   - SMA200 filter for SPY
   - Monthly rebalancing

2. **RegimeSwitching (40% slice)**: Regime-dependent strategy
   - Bull markets: Risk-adjusted momentum on SPY/QQQ (70/30)
   - Bear/Sideways: Mean-reversion (RSI oversold) + defensive (GLD/IEF)
   - Regime detection via SMA50/SMA200 on SPY

The portfolio construction model (`MultiStrategyPCM`) gives each alpha a share of the capital, then adds the two shares on the shared ETFs. This is mode `intent`, the default since #19740.

**Defect fixed by #19740.** Before it calls `determine_target_percent`, Lean's `PortfolioConstructionModel` keeps only the most recent active insight of each symbol. Both alphas emit on the first trading day of the month, and the SectorMomentum universe (SPY, IEF, GLD) is entirely contained in the RegimeSwitching universe. RegimeSwitching, added second to the `CompositeAlphaModel`, therefore wins on every shared ETF: SectorMomentum insights reached the construction model in none of the 403 measured calls. Before #19740, the composite was therefore RegimeSwitching at 40% plus 60% cash:
- average gross exposure 0.40;
- weekly return correlation with RegimeSwitching alone: 1.00;
- Sharpe difference with RegimeSwitching alone: +0.001 [−0.012; +0.016].

This behaviour remains available under `mode` = `base` to reproduce the earlier figures. Under `intent`, the model rebuilds the targets from the most recent active insight of each (symbol, alpha) pair, then adds them per symbol.

## Files

- `main.py`: Algorithm setup with CompositeAlpha and MultiStrategyPouchesPCM
- `alpha_models.py`: SectorMomentumAlpha and RegimeSwitchingAlpha classes
- `SharedPCM/pouches_pcm.py` (QC project library): `MultiStrategyPouchesPCM`, the canonical pouch PCM imported by `main.py` (extraction #19821 brick 1)
- `quantbook.ipynb`: Research QuantBook for the Momentum + RegimeSwitching composite (native QC data, pre-backtest)

## Shared module non-regression (#20188)

Since #21134, `main.py` imports `MultiStrategyPouchesPCM` from `SharedPCM/pouches_pcm.py` instead of the local copy `portfolio_construction.py`. Two QC Cloud backtests run on 2026-10-26, with the default parameters and the window 2015-01-01 → 2025-12-31, check that this change alters no order:

- **A**: the `main` code at commit `54f9b9eec1`, with the shared module;
- **B**: the same `main.py` and `alpha_models.py`, with the old `portfolio_construction.py` copy taken at the commit before the migration (`777f502a2a^`). The argument the old copy does not know (`watch_source="SectorMomentum"`) is removed from the call, and two read-only properties expose its diagnostic counters under the names `main.py` reads.

A and B carry the same instrumentation, which places no order. It records the portfolio value every day at midnight, warm-up included (252 sessions). At the end of the backtest it computes a SHA-256 fingerprint per year of the orders (id, date, security, quantity, status, price) and of the recorded values.

| | A (shared module) | B (old copy) |
|---|---|---|
| Orders | 676 | 676 |
| Recorded values | 4,382 | 4,382 |
| Last recorded value | 238,628.49 | 238,628.49 |
| Sharpe (QC) | 0.353 | 0.353 |
| CAGR | 8.152% | 8.152% |
| Max drawdown | 28.3% | 28.3% |

The yearly fingerprints are equal: 12 of 12 for the orders, 12 of 12 for the values. The 27 QC statistics are equal, turnover included. The diagnostic counters of the portfolio construction model are equal as well. The migration therefore does not change the project's behaviour. Traces kept outside the repository: `QC-traces/20188-nr/`.

## Performance

### Re-measurement #21349 on the `main` code: `NO BEATS`

QC Cloud backtests of 2026-10-22, `main` code at commit `7a2d9b84f0`. The verdict window (2015-01-02 → 2026-07-09, 2894 sessions), the statistic and the rule are those of #19740. The protocol was written on the issue before the first backtest ([#21349](https://github.com/jsboige/CoursIA/issues/21349), comment `c.6329681428`). Since #19740, the alphas have received three fixes: the midnight slice without a bar (#20264) and the short history on a half session (#20286), in a single commit, then the insight of the non-oversold risk asset left alive while oversold (#21352).

| Version | Sharpe | CAGR | Worst drawdown | Turnover per year | Average gross exposure |
|---------|--------|------|----------------|-------------------|------------------------|
| `intent` (default) | 0.70 | 8.9% | −28.3% | 8.6 | 1.00 |
| SectorMomentum alone (`sm`) | 0.48 | 6.6% | −32.5% | 7.9 | 1.00 |
| RegimeSwitching alone (`rs`) | 0.87 | 11.9% | −27.4% | 9.7 | 1.00 |
| SPY held (`spy`) | 0.83 | 13.9% | −33.7% | 0.09 | 1.00 |
| 60% SPY / 40% IEF (`sixty40`) | 0.89 | 9.0% | −21.1% | 0.30 | 1.00 |

**Verdict.** `NO BEATS`, more clearly than in #19740: both differences are negative.

| Candidate | Difference with SPY [95% CI] | Difference with the 60/40 [95% CI] | Holm p |
|-----------|------------------------------|------------------------------------|--------|
| `intent` | −0.13 [−0.60; +0.30] | −0.19 [−0.63; +0.24] | 1.00 |

As in #19740, `intent` leads the references only over 2023 → 2026-07 (+0.23 against SPY, +0.18 against the 60/40); it trails over 2015-2018 and 2019-2022. With the following sessions available (up to 2026-07-24), the differences are −0.14 and −0.19, for information. The rule plans the doubled fees and the grid only for a significant candidate: they were not run. `base` was not re-measured.

**Contribution of each slice** (descriptive differences, outside the Holm correction): +0.22 [+0.01; +0.43] with SectorMomentum alone, −0.17 [−0.52; +0.17] with RegimeSwitching alone. The #19740 reading holds: adding the slices improves on SectorMomentum, not on RegimeSwitching.

**Where the drop from 0.83 to 0.70 comes from.** The control, the #19758 code as merged (`8207c650ab`) run again on the same day, reproduces the #19740 series: no session differs by more than 0.01%. The QC data did not move; the gap comes from the code. Two runs added after reading the verdict, hence descriptive, break it down by commit:

| Code step | Sharpe difference [95% CI] | Sessions differing by more than 0.01% |
|-----------|----------------------------|---------------------------------------|
| Shared PCM extraction (#21134, `777f502a2a`) | 0.000 | 0 |
| Midnight slice and short history (`e8a077acb0`) | −0.120 [−0.298; +0.040] | 483 |
| Risk asset while oversold (#21352) | −0.006 [−0.014; +0.000] | 23 |

These runs do not separate the two fixes of `e8a077acb0`. The history fix acts only when the history comes back short, which #20286 measured on a half session; yet the first differing session, 2015-02-02, is a full session. At least part of the gap therefore comes from the midnight slice: a dividend notice arriving alone at midnight made the alphas emit on the previous close, with an order filled at the open of the same day; they now all emit at the close of the first session of the month. No interval excludes zero. One cannot say that the fixes degraded the strategy, only that the #19740 figures no longer describe the code.

**Limits.** Those of #19740 still apply: IEF chosen with knowledge of the period, end moved back by QC Cloud to the last 90 days, without an error. All versions of this re-measurement ran on the same day, over the same sessions.

### Measurement #19740: `NO BEATS` (code before the fixes)

The #21349 re-measurement above replaces the `intent`, `sm` and `rs` rows of this measurement; the `base` row and the discussion of the default choice remain those of the code at the time.

QC Cloud backtests of 2026-10-07, from 2015-01-02 to 2026-07-09 (2894 sessions), Interactive Brokers fees. The protocol and the verdict rule were fixed before any computation ([#19740](https://github.com/jsboige/CoursIA/issues/19740)). The Sharpe ratio is computed with a zero risk-free rate on the portfolio value at each close, by an analysis outside the repository; it therefore differs from the Sharpe ratio shown by QC, which subtracts a risk-free rate.

| Version | Sharpe | CAGR | Worst drawdown | Turnover per year | Average gross exposure |
|---------|--------|------|----------------|-------------------|------------------------|
| `intent` (default) | 0.83 | 10.6% | −24.4% | 7.8 | 1.00 |
| `base` (code before #19740) | 0.90 | 5.0% | −11.5% | 3.8 | 0.40 |
| SectorMomentum alone (`sm`) | 0.63 | 8.9% | −24.9% | 6.7 | 1.00 |
| RegimeSwitching alone (`rs`) | 0.90 | 12.5% | −27.5% | 9.5 | 1.00 |
| SPY held (`spy`) | 0.83 | 13.8% | −33.7% | 0.09 | 1.00 |
| 60% SPY / 40% IEF (`sixty40`) | 0.88 | 8.9% | −21.1% | 0.29 | 1.00 |

**Verdict.** It is `NO BEATS` for `base` and for `intent`: no Sharpe difference with the references is significant. The difference is tested by a circular block bootstrap with 21-session blocks (10,000 draws, Holm correction over the two references).

| Candidate | Difference with SPY [95% CI] | Difference with the 60/40 [95% CI] | Holm p |
|-----------|------------------------------|------------------------------------|--------|
| `intent` | −0.00 [−0.47; +0.43] | −0.05 [−0.50; +0.37] | 1.00 |
| `base` | +0.08 [−0.29; +0.41] | +0.02 [−0.36; +0.38] | 0.72 |

Neither candidate is positive on two of the three sub-periods (2015-2018, 2019-2022, 2023 → 2026-07). `base` leads the references only over 2015-2018; `intent` only over 2023-2026. The parameter grid and the doubled-fee run were planned only for a significant candidate: they were not run.

**Contribution of each slice.** Under `intent`, the Sharpe difference with SectorMomentum alone is +0.20 [−0.03; +0.43]; with RegimeSwitching alone it is −0.08 [−0.46; +0.29]. Both differences are descriptive, outside the Holm correction. Adding the slices improves on SectorMomentum, not on RegimeSwitching. Under `base`, the composite is RegimeSwitching diluted by cash, and a Sharpe ratio computed with a zero risk-free rate does not see that dilution: hence a Sharpe of 0.90 for a 5.0% CAGR.

**Choice of default.** `intent` is the design the project announces: the `MultiStrategyPCM` docstring describes adding the slices. `base` leaves 60% of the capital in cash and ignores SectorMomentum. Neither beats the references: changing the default makes the project match its description, it creates no measured advantage. Its Sharpe is even lower than that of `base` (0.83 against 0.90).

**Limits.**
- IEF replaced TLT with knowledge of the 2015-2026 period (comment in `alpha_models.py`): there is no out-of-sample period. This bias favoured the candidate, which strengthens the `NO BEATS`.
- The backtests requested an end on 2026-09-30. The QC organisation used holds back the last 90 days and moved the end to 2026-07-09, without an error. All versions ran in the same organisation: the comparisons cover the same sessions.
- Under `intent`, the `PCM calls with SM` statistic stays at 0 by construction, because it counts the insights received by `determine_target_percent`. The addition shows in the gross exposure (1.00) and in the GLD orders (203 against 111 under `base`).

### Figures before #19740

The table below predates the measurement; it is kept for the record (backtest 2015-01-01 → 2025-12-31).

| Metric | Value |
|--------|-------|
| Sharpe Ratio | 0.185 |
| CAGR | 4.728% |
| Net Profit | 66.272% |
| Max Drawdown | 11.500% |
| Total Orders | 520 |
| Win Rate | 73% |
| Alpha | -0.008 |
| Beta | 0.218 |
| Sortino | 0.196 |

The verdict at the time was "Underperforming": RegimeSwitching was said to dilute returns in the 60/40 blend, and the proposed next step was to try T80/RS20 or T90/RS10.

**Reading corrected by #19740.**
- **Table.** The `readme` run (`base` over the same period) reproduces it: QC Sharpe 0.21, CAGR 4.72%, worst drawdown 11.5%, 522 orders. These figures measured RegimeSwitching at 40% plus 60% cash, not a 60/40 blend: SectorMomentum never traded. The low beta (0.218) and the low CAGR come from the cash. Changing the shares under `base` only changes the cash share: the T80/RS20 lead had no object.
- **Registry "Edge" status.** It cited an out-of-sample run over 2023-2026 (project 28871239): QC Sharpe 0.145, PSR 73.52%, 183 orders. The `oos` run (`base`, 2023-01-01 → 2026-05-01, 834 sessions) does not reproduce it: QC Sharpe 0.133, PSR 2.5%, 136 orders. Unverified hypothesis: that project ran another version of the code. The registry's 73.52% is the PSR of this small sample, not a measurement against a reference.

## Parameters

| Parameter | Default | Description |
|-----------|---------|-------------|
| `mode` | `intent` | `intent`: slices added on the shared ETFs · `base`: code before #19740 (RegimeSwitching at 40%, the rest in cash) · `sm`, `rs`: a single alpha, at 100% · `spy`, `sixty40`: held references, rebalanced on the first trading day of the month |
| `sm_allocation` | 0.60 | SectorMomentum slice (0.60 = 60%) |
| `rs_allocation` | 0.40 | RegimeSwitching slice (0.40 = 40%) |
| `sm_weights` | 0.4,0.2,0.2,0.2 | Weights of the 1, 3, 6 and 12-month horizons in the SectorMomentum score |
| `rs_lookback` | 63 | RegimeSwitching momentum horizon, in sessions |
| `start`, `end` | 2015-01-01, 2025-12-31 | Backtest dates (`YYYY-MM-DD`) |
| `brokerage` | `ibkr` | `none`: Lean's default brokerage model, without Interactive Brokers fees |
| `fee_mult` | 1 | Broker fee multiplier (2 = doubled fees) |

The `shadow` chart carries the portfolio value at each close, the cumulative fees and the cumulative turnover (shadow-replay contract, #18923). The runtime statistics `Orders <ETF>` count the filled orders per ETF; `Gross exposure` is the average gross exposure; `PCM calls`, `PCM calls with SM` and `SM UP reaching PCM` count the construction-model calls and the SectorMomentum insights it receives.

## Cloud IDs

- Project ID: 31243821
- Organization: d600793ee4caecb03441a09fc2d00f7f
- Measurement #19740: project 37485593, in an educational organisation sponsored by QuantConnect
- Re-measurement #21349: projects 38257493 (`main`), 38257551 (control), 38258154 and 38258197 (attribution), on QC Cloud

## Backtest Period

Default 2015-01-01 to 2025-12-31. The #19740 measurement and the #21349 re-measurement cover 2015-01-02 to 2026-07-09.
