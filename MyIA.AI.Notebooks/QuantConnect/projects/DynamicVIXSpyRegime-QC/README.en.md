# DynamicVIXSpyRegime-QC

**Asset class:** US Equities (SPY)
**Cloud project ID:** QC Project ID: 32921262 (redeployed 2026-06-15)

## Description

QC Strategy Library #50 clone (Dynamic VIX-SPY Regime Switching by Ahmet Kasti). VIX-based regime detection on SPY switching between aggressive and defensive positioning. ML overlay (RandomForestClassifier, 11 VIX/SPY features).

## Measures

### Measure #19825: `NO BEATS`, same-day VIX read fixed

QC Cloud backtests of 2026-10-08, from 2015-01-02 to 2026-07-08 (2893 sessions), with the fees of the brokerage model set by the code. The protocol and the verdict rule were fixed before any computation ([#19825](https://github.com/jsboige/CoursIA/issues/19825)). The Sharpe ratio is computed at a zero risk-free rate on the portfolio value at each close, by an analysis outside the repository; it therefore differs from the Sharpe shown by QC, which subtracts a risk-free rate.

**Same-day VIX read.** The `CBOE` class dated each CSV row at its trading day, with no end time. Lean delivers custom data at its start time: the VIX close of day D was therefore visible from D 00:00, and `CheckSignal`, which runs at D 10:00, decided on a close not yet known at that hour. The added counter confirms it:

| Counter | `base` (original code) | `lag` |
|---------|------------------------|-------|
| Decisions whose last VIX row read is from the same day | 2894 of 2894 | 0 of 2894 |
| Monthly trainings whose VIX ends after SPY | 139 of 139 | 2 of 139 |

The `lag` mode dates each row on the day after its trading day: the decision of D only sees the close of D-1, as for SPY. The two residual trainings are not explained; unverified hypothesis: days where the CBOE CSV has a row and SPY has no bar.

| Version | Sharpe | CAGR | Max drawdown | Turnover per year | Fees per year (share of portfolio) |
|---------|--------|------|--------------|-------------------|------------------------------------|
| `lag` (default) | 0.80 | 10.1 % | −30.9 % | 30.7 | 0.24 % |
| `base` (code before #19825) | 0.77 | 9.6 % | −30.2 % | 30.7 | 0.25 % |
| SPY held (`spy`) | 0.82 | 13.7 % | −33.7 % | 0.09 | 0.00 % |
| 60 % SPY / 40 % IEF (`sixty40`) | 0.87 | 8.8 % | −21.2 % | 0.28 | 0.01 % |

**Verdict.** It is `NO BEATS` for `lag` as for `base`: both Sharpe differences with the references are negative, and none is significant. The difference is tested by circular block bootstrap with 21-session blocks (10,000 draws, Holm correction over the two references).

| Candidate | Difference vs SPY [95 % CI] | Difference vs 60/40 [95 % CI] | Holm p |
|-----------|-----------------------------|-------------------------------|--------|
| `lag` | −0.02 [−0.30 ; +0.31] | −0.07 [−0.32 ; +0.22] | 1.00 |
| `base` | −0.05 [−0.31 ; +0.26] | −0.10 [−0.35 ; +0.19] | 1.00 |

By sub-period (2015-2018, 2019-2022, 2023 → 2026-07), `base` leads both references only in 2015-2018; `lag` leads them in 2015-2018 and 2023-2026, and trails in 2019-2022. The parameter grid and the doubled-fees run were planned only for a significant candidate: they were not run.

**Share of the result due to the same-day read.** The Sharpe difference `base` − `lag` is −0.03 [−0.16 ; +0.10], descriptive, outside the Holm correction. Reading the close of the day brought no measurable advantage: both versions place about the same number of orders (3927 vs 3830), and their weekly returns are correlated at 0.98.

**What the strategy holds.** Under `lag`, the closed gain comes mostly from SPY, then GLD; TLT ends at a loss. The weekly returns of `lag` are correlated at 0.86 with SPY held and 0.89 with the 60/40: the rotation follows the equity market closely, with a turnover of more than 30 times the portfolio per year.

**Choice of the default.** The protocol provided that the default mode becomes `lag` if the counter confirmed the same-day read: it did. The change removes information that did not exist at decision time; it creates no measured advantage.

**Limits.**
- The thresholds (VIX 13 and 20, 80th percentile, 3 %, 1.2) and the 2015 window come from the QC library, published after part of the period: there is no out-of-sample period. This bias favoured the candidate, which strengthens the `NO BEATS`.
- The backtests requested a later end; the compute nodes used hold back the last 90 days and brought the end to 2026-07-08, without error. All versions ran on the same nodes: the comparisons cover the same sessions.

### Figures prior to #19825

The table below predates the measure; it is kept for the record.

| Source | Sharpe | CAGR | MaxDD | Period | Universe |
|--------|--------|------|-------|--------|----------|
| **QC Strategy Library #50** (original claim, `main.py:10`) | **1.72** | **29.76%** | **17.80%** | **OOS 1Y** (5Y CAGR — window unspecified) | SPY + TLT + GLD + BIL |
| `research.ipynb` cell[9] (exec=5) — BASELINE (default params) | **0.97** | **23.83%** | **-22.09%** | 2015-01-02 → 2025-12-30 (2765 days) | SPY + TLT + GLD + BIL + ^VIX |
| `research.ipynb` cell[26] (exec=13) — **BEST (H3: Exposure gross=2.0)** | **1.023** | **31.35%** | **-29.07%** | 2015-01-02 → 2025-12-30 (2765 days) | idem |
| `research.ipynb` cell[9] (exec=5) — **Benchmark SPY Buy & Hold** | 0.536 | 13.54% | -33.72% | 2015-2025 | SPY only |

The former README concluded that "the strategy's edge is reproducible" and that `research.ipynb` was the reference for the deployable strategy.

**Reading corrected by #19825.**
- **`research.ipynb` does not measure `main.py`.** The notebook already lags the VIX by one day (`vix_c[i-1]`), applies a gross exposure of 1.5 and computes its Sharpe with a 4 % risk-free rate (`calculate_metrics(..., risk_free=0.04)`). Its figures describe another rule. It does not test its difference with SPY either.
- **`main.py` on its own window.** The `orig` run (`base`, 2015-01-01 → 2024-12-31) gives a Sharpe of 0.70 at a zero risk-free rate (0.39 according to QC), a CAGR of 8.5 %, a max drawdown of −30.2 % and 3386 orders. It reproduces neither the notebook's 0.97 / 23.83 % nor the library claim, whose window is unspecified.
- **Registry status.** The "69.4% (backtest vérifié)" of `docs/qc/qc-strategies-status.md` appeared nowhere in the project; it is replaced by the verdict above.

## Tested hypotheses (from `research.ipynb`)

These configurations apply to the notebook's rule (VIX lagged by one day, configurable gross exposure, Sharpe with a 4 % risk-free rate), not to `main.py`. Cf. `research.ipynb` cell[3] and cell[26] for the full comparative table (12 configurations). Top 3 by Sharpe:

| Config | Sharpe | CAGR | MaxDD | WinRate |
|--------|--------|------|-------|---------|
| **H3: Exposure gross=2.0** | **1.023** | 31.35% | -29.07% | 55.2% |
| H1: ML threshold=0.6 (= baseline) | 0.970 | 23.83% | -22.09% | 55.2% |
| H3: Exposure gross=1.5 | 0.970 | 23.83% | -22.09% | 55.2% |

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/DynamicVIXSpyRegime-QC"`
**QC Cloud:** QC Project ID `32921262` (redeployed 2026-06-15). The `research.ipynb` notebook uses the QC Cloud kernel (RandomForest + StandardScaler + CBOE VIX data not loaded in local Docker).

**Project parameters** (all optional):

| Parameter | Default | Role |
|-----------|---------|------|
| `mode` | `lag` | `lag`: VIX delivered the day after its trading day; `base`: original code (same-day VIX); `spy`: SPY held; `sixty40`: 60 % SPY and 40 % IEF, rebalanced on the first trading day of each month |
| `start`, `end` | `2015-01-01`, `2024-12-31` | backtest window |
| `vix_pct` | 80 | VIX percentile that flags a spike |
| `ml_threshold` | 0.6 | random forest probability threshold |
| `vix_low` | 13 | "low VIX" threshold |
| `fee_mult` | 1 | brokerage fee multiplier |

The `shadow` chart carries the portfolio value at each close; the runtime statistics give the number of orders per ETF and the VIX read counters.

## Files

- `main.py` - Strategy (QC Library #50 clone, 4-asset regime switching + ML overlay), instrumented for measure #19825
- `research.ipynb` - 5 hypotheses H1-H5 + comparative table + SPY benchmark (2015-2025, 2765 days), on the notebook's rule

## References

- QuantConnect Strategy Library #50 - Dynamic VIX-SPY Regime Switching by Ahmet Kasti: https://www.quantconnect.com/strategies/50
- Brock et al. (1992), "Simple Technical Trading Rules and the Stochastic Properties of Stock Returns"
- `research.ipynb` cell[0] (MD): complete methodology with ML hyperparameters and VIX/SPY features
