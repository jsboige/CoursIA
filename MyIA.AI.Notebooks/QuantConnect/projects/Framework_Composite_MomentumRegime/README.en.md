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

- `main.py`: Algorithm setup with CompositeAlpha and MultiStrategyPCM
- `alpha_models.py`: SectorMomentumAlpha and RegimeSwitchingAlpha classes
- `portfolio_construction.py`: MultiStrategyPCM for capital allocation per strategy
- `quantbook.ipynb`: Research QuantBook for the Momentum + RegimeSwitching composite (native QC data, pre-backtest)

## Performance

### Measurement #19740: `NO BEATS`

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

## Backtest Period

Default 2015-01-01 to 2025-12-31. The #19740 measurement covers 2015-01-02 to 2026-07-09.
