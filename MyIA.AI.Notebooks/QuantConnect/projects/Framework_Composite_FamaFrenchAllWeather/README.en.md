# Framework Composite - FamaFrench + AllWeather

## Description

Composite strategy combining two complementary approaches via QuantConnect Algorithm Framework:

1. **FamaFrench (20% slice)**: Factor ETF rotation (VLUE, MTUM, SIZE, QUAL, USMV)
   - Risk-adjusted momentum: 12-month return excluding the last month (`lookback` = 252 sessions, 21 sessions skipped), divided by the annualized realized volatility over 63 sessions (`vol_window`)
   - Skip-month (exclude last month to avoid short-term reversal)
   - All factors with a positive score, equal-weighted; if no score is positive, USMV alone
   - Only the sign of the score decides. Dividing by a positive volatility does not change that sign: the selection is that of raw momentum, and `vol_window` has no effect on orders (measured: the `vol_window` 126 grid point reproduces `intent` exactly)
   - Signal emitted on the first trading day of each month

2. **AllWeather (80% slice)**: Static multi-asset allocation (SPY 30%, IEF 30%, GLD 30%, XLP 10%)
   - Ray Dalio-inspired "All Weather" portfolio (simplified, no TLT)
   - Signal emitted on the first trading day of each month

The portfolio construction model (`MultiStrategyPCM`) splits capital between the two slices and rebalances every 31 days. The code has neither a drift threshold nor a top-2 factor selection.

## Key Design Principle

**NO overlap between universes**: Factor ETFs (equity factors) vs traditional assets (equities/bonds/gold). This creates true diversification:
- FamaFrench: Equity factor exposure (value, momentum, size, quality, low-vol)
- AllWeather: Macro allocation (stocks, bonds, gold, defensive)

**Important**: FamaFrench uses risk-adjusted momentum ONLY (no SMA200 filter). AllWeather handles defense through its static allocation. This is the `intent` mode, the default since #19621.

**Defect fixed by #19621.** `alpha_models.py` also contains a regime filter on the SPY SMA200, which contradicts this principle. Before #19621 the filter was never created: SPY is not in the FamaFrench slice universe, so the slice emitted no signal. It stayed in cash for the whole backtest, and the composite was 80% AllWeather and 20% cash. This behaviour remains available as `mode` = `base` to reproduce the earlier figures; `mode` = `sma` makes the filter effective.

## Files

- `main.py`: Algorithm setup with CompositeAlpha and MultiStrategyPCM
- `alpha_models.py`: FamaFrenchAlpha and AllWeatherAlpha classes
- `portfolio_construction.py`: MultiStrategyPCM for capital allocation per strategy
- `quantbook.ipynb`: Research notebook with backtest analysis

## Performance

### Measurement #19621: `NO BEATS`

QC Cloud backtests of 2026-10-07, from 2015-01-02 to 2026-09-25 (2949 sessions), Interactive Brokers brokerage fees. The protocol and verdict rule were fixed before any computation ([#19621](https://github.com/jsboige/CoursIA/issues/19621)). The Sharpe ratio is computed at a zero risk-free rate on the portfolio value at each close, by an analysis outside the repository; it therefore differs from the Sharpe ratio displayed by QC, which subtracts a risk-free rate.

| Version | Sharpe | CAGR | Max drawdown | Turnover per year | Orders on factor ETFs |
|---------|--------|------|--------------|-------------------|-----------------------|
| `intent` (default) | 1.02 | 9.6% | −17.6% | 0.79 | 232 |
| `base` (code before #19621) | 1.03 | 7.0% | −13.2% | 0.33 | 0 |
| `sma` (effective SMA200 filter) | 1.01 | 9.4% | −17.2% | 1.09 | 243 |
| AllWeather alone (`base`, 0 / 1) | 1.03 | 8.8% | −16.2% | 0.43 | 0 |
| SPY held (`spy`) | 0.83 | 13.9% | −33.7% | 0.09 | — |
| 60% SPY / 40% IEF (`sixty40`) | 0.87 | 8.8% | −21.1% | 0.28 | — |

**Verdict.** It is `NO BEATS` for both `base` and `intent`: no Sharpe difference with the references is significant. The difference is tested by a circular block bootstrap with 21-session blocks (10,000 draws, Holm correction over the two references).

| Candidate | Difference vs SPY [95% CI] | Difference vs 60/40 [95% CI] | Holm p |
|-----------|----------------------------|------------------------------|--------|
| `intent` | +0.19 [−0.13; +0.48] | +0.15 [−0.10; +0.39] | 0.22 |
| `base` | +0.20 [−0.25; +0.59] | +0.16 [−0.20; +0.49] | 0.37 |

The other `BEATS` conditions hold:
- the difference stays positive with doubled fees;
- it is positive in at least two of the three subperiods (2015-2018, 2019-2022, 2023 → 2026-09);
- it is positive at all five grid points (factor share 10% and 40%, `lookback` 189 and 315, `vol_window` 126; the last point is inert, see the description).

Over almost twelve years, the composite's lead remains indistinguishable from noise.

**Contribution of the factor slice.** The Sharpe difference `intent` − AllWeather alone is −0.01 [−0.14; +0.14], and `sma` − AllWeather alone −0.02 [−0.15; +0.12]. When active, the slice raises the annual return by about 0.8 points and the maximum drawdown by 1.4 points, without changing the Sharpe ratio. Under `base` the difference is −0.002: 20% cash does not change a Sharpe ratio computed at a zero risk-free rate.

**Choice of default.** `intent` is the design the project announces. `sma` adds turnover (1.09 vs 0.79 per year) for a Sharpe ratio that is not higher. `base` leaves a fifth of the capital in cash. Neither `intent` nor `sma` beats the references: the change of default makes the project match its description, it does not create a measured advantage.

**Limit.** The measurement window lies inside the allocation sweep window (2010-2026): there is no out-of-sample period. That flaw favoured the candidate, which strengthens the `NO BEATS`.

### Figures prior to #19621

The tables below predate the measurement; they are kept for the record.

| Metric | Value |
|--------|-------|
| Sharpe Ratio | 0.588 |
| CAGR | 9.9% |
| Max Drawdown | 17.1% |
| Period | 2010-2026 |

Standardized #1630 window (2018-01-01 to 2025-01-01, 1761 tradeable dates), backtested on QC Cloud with post-#2801 brokerage fees.

| Metric | README headline (2010-2026 sweep) | Catalog (2015-2025) | Aligned (2018-2025) |
|--------|-----------------------------------|---------------------|---------------------|
| Sharpe | 0.588 | 0.472 | 0.338 |
| CAGR | 9.9% | 7.226% | 6.578% |
| MaxDD | 17.1% | 13.1% | 13.1% |
| PSR | — | 35.0% | 22.9% |

Aligned backtest `e9ac7c66` (1761 tradeable dates) / catalog backtest `70415edc` (`FF20_AW80_2015_2025_extended`, 2766 dates) / "OOS" 2023-2026 figure (Sharpe 0.684, PSR 87.5%) `b08c8956`, on only 835 dates. The `totalOrders=0` read at the time came from the MCP wrapper extraction: the #19621 `orig` run counts 343 orders, all on the AllWeather slice. The project had been promoted from Tier 4 (Untested) to Tier 2 (Historique).

**Reading corrected by #19621.**
- **Aligned window.** The `orig` run (`base` on 2018-01-01 → 2025-01-01) reproduces the aligned row: QC Sharpe 0.341, CAGR 6.57%, maximum drawdown 13.1%, with 0 orders on the factor ETFs. These figures already measured the inert slice. The explanation given until now ("the AllWeather sleeve drags the composite below the FamaFrench rotation") therefore does not hold: there was no FamaFrench rotation, only 20% cash.
- **Registry status.** The 87.5% in the registry is the PSR of that small sample, not a measurement against a reference.
- **2010-2026 sweep.** Its maximum drawdown (17.1%) and the rise of CAGR with the factor share resemble an active slice (`intent` −17.6%, `sma` −17.2%), not the inert slice (−13.2%). Unverified hypothesis: the sweep was produced by an earlier version of the code.

| Allocation | Sharpe | CAGR | Max DD |
|------------|--------|------|--------|
| FF20/AW80 | 0.588 | 9.9% | 17.1% |
| FF40/AW60 | 0.564 | 10.5% | 19.3% |
| FF50/AW50 | 0.539 | 10.8% | 21.7% |
| FF60/AW40 | 0.512 | 11.2% | 24.1% |

| Strategy | Sharpe | CAGR | Max DD |
|----------|--------|------|--------|
| FamaFrench v3.0 | 0.540 | 12.1% | 24.2% |
| AllWeather | 0.667 | 9.3% | 16.4% |
| Composite (FF20/AW80) | 0.588 | 9.9% | 17.1% |

## Parameters

| Parameter | Default | Description |
|-----------|---------|-------------|
| `mode` | `intent` | `intent`: FamaFrench slice without regime filter · `base`: code before #19621 (inert slice) · `sma`: effective SPY SMA200 filter · `spy`, `sixty40`: held references, rebalanced on the first trading day of the month |
| `ff_allocation` | 0.20 | FamaFrench slice (0.20 = 20%) |
| `aw_allocation` | 0.80 | AllWeather slice (0.80 = 80%) |
| `lookback` | 252 | Momentum horizon, in sessions |
| `vol_window` | 63 | Realized volatility window, in sessions (no effect on orders, see the description) |
| `start`, `end` | 2018-01-01, 2025-01-01 | Backtest dates (`YYYY-MM-DD`) |
| `fee_mult` | 1 | Brokerage fee multiplier (2 = doubled fees) |

The `shadow` chart carries the portfolio value at each close, cumulative fees and cumulative turnover (shadow replay contract, #18923). The `Orders <ETF>` runtime statistics count filled orders per ETF.

## Backtest Period

Default 2018-01-01 to 2025-01-01. Measurement #19621 covers 2015-01-01 to 2026-09-25; the earlier allocation sweep covered 2010-01-01 to 2026-03-10.

## Deployment

- **Project ID**: 28882145
- **Organization**: Jean-Sylvain Boige (Researcher PAID)
- **Status**: ✅ Deployed and backtested

## References

- **FamaFrench**: Factor ETF rotation with risk-adjusted momentum
- **AllWeather**: Multi-asset static allocation (no TLT)
- **SESSION5_PATTERNS.md**: AlphaModel Framework pedagogical guide
