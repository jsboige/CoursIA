# MomentumRegime-AdaptiveWeights

**Asset class:** US Equities (SPY/QQQ/IEF/GLD)
**Cloud project ID:** 31524424
**Baseline:** Framework_Composite_MomentumRegime (figures prior to #19740: Sharpe 0.185, CAGR 4.73%)

## Description

Adaptive-weight variant of Framework_Composite_MomentumRegime.
Shifts allocation toward SectorMomentum (85/15 vs baseline 60/40),
expands momentum universe to include QQQ, and favors shorter-term lookbacks.

Both alpha models emit on the same four ETFs. `MultiStrategyPCM` states that it adds the two
strategies' sleeves on shared tickers; under the original code, it did not (see the measure
below).

## Measure #19759 (tranche 2): `NO BEATS`

QC Cloud backtests of 2026-10-08, from 2015-01-02 to 2026-07-10 (2895 sessions), with the fees
of the brokerage model set by the code. The protocol and the verdict rule were fixed before any
computation ([#19759](https://github.com/jsboige/CoursIA/issues/19759), same rule as #19740).
The Sharpe ratio is computed at a zero risk-free rate on the portfolio value at each close, by
an analysis outside the repository; it therefore differs from the Sharpe shown by QC, which
subtracts a risk-free rate.

**SectorMomentum never reached the targets.** Lean keeps a single active insight per symbol
before calling `determine_target_percent`. RegimeSwitching emits on SectorMomentum's four ETFs,
and its insight is the one kept.
Le compteur de la liste reçue le montre sous `base` ; il est mesuré avant la reconstruction
des cibles :

| Counter | `base` (original code) | `intent` |
|---------|------------------------|----------|
| Appels de `determine_target_percent` dont la liste reçue contient un insight SectorMomentum (avant reconstruction) | 0 sur 403 | 0 sur 403 |
| Average gross exposure | 0.15 | 1.00 |
| Weekly correlation with RegimeSwitching alone | 1.00 | 0.76 |
| Weekly correlation with SectorMomentum alone | 0.69 | 0.995 |

Under `base`, the portfolio therefore held RegimeSwitching at 15% and 85% cash. The `intent`
mode reuses the `MultiStrategyPCM` of #19758: it rebuilds the targets from the last active
insight of each (ticker, source model) pair, then adds them per ticker. The first counter is 0
in both modes, because it counts the list received by `determine_target_percent`, before that
rebuild; the rebuild shows in the gross exposure and in the correlations.

| Version | Sharpe | CAGR | Max drawdown | Turnover per year | Average gross exposure |
|---------|--------|------|--------------|-------------------|------------------------|
| `intent` (default) | 0.90 | 14.6% | −23.4% | 8.6 | 1.00 |
| `base` (code before #19759) | 0.90 | 1.9% | −4.4% | 1.4 | 0.15 |
| SectorMomentum alone (`sm`) | 0.87 | 14.9% | −26.4% | 8.4 | 1.00 |
| RegimeSwitching alone (`rs`) | 0.91 | 12.5% | −27.4% | 9.5 | 1.00 |
| SPY held (`spy`) | 0.83 | 13.9% | −33.7% | 0.09 | 1.00 |
| 60% SPY / 40% IEF (`sixty40`) | 0.88 | 8.9% | −21.1% | 0.29 | 1.00 |

A Sharpe ratio at a zero risk-free rate does not change when the exposure is scaled down:
`base` has the Sharpe of RegimeSwitching alone, with a CAGR more than six times lower.

**Verdict.** It is `NO BEATS` for `intent` as for `base`: no Sharpe difference with the
references is significant. The difference is tested by circular block bootstrap with
21-session blocks (10,000 draws, Holm correction over the two references).

| Candidate | Difference vs SPY [95% CI] | Difference vs 60/40 [95% CI] | Holm p (SPY / 60/40) |
|-----------|----------------------------|------------------------------|----------------------|
| `intent` | +0.08 [−0.48 ; +0.59] | +0.02 [−0.50 ; +0.54] | 0.83 / 0.83 |
| `base` | +0.07 [−0.30 ; +0.41] | +0.02 [−0.37 ; +0.38] | 0.75 / 0.75 |

Les écarts de Sharpe sont calculés avant l'arrondi des valeurs du tableau : par exemple,
`intent` − SPY vaut 0,0761, `intent` − `sm` vaut 0,0357 et `intent` − `rs` vaut −0,0010.
La soustraction des Sharpes affichés à deux décimales peut donc donner un autre arrondi.

By sub-period (2015-2018, 2019-2022, 2023 → 2026-07), `intent` trails both references in
2015-2018 (−0.21 vs SPY, −0.32 vs the 60/40), then leads (+0.11 and +0.08 vs SPY). `base` does
the opposite: ahead in 2015-2018, behind afterwards. The parameter grid and the doubled-fees
run were planned only for a significant candidate: they were not run.

**Contribution of each model.** Under `intent`, the Sharpe difference with SectorMomentum alone
is +0.04 [−0.02 ; +0.09], and the weekly return correlation is 0.995: at 85%, the composite
behaves like SectorMomentum alone. With RegimeSwitching alone, the difference is 0.00
[−0.45 ; +0.45]. These differences are descriptive, outside the Holm correction.

**What the variant changes.** Compared with the `intent` run of #19758
(Framework_Composite_MomentumRegime, 0.60 / 0.40 sleeves, without the variant's two other
changes), the Sharpe difference is +0.08 [−0.21 ; +0.38] over 2894 common sessions,
descriptive. Once the sleeves are added, the variant's three changes produce no measurable
difference.

**What the strategy holds.** Under `intent`, half of the closed-position result comes from GLD
(50%), then QQQ (37%), SPY (10%) and IEF (3%).

**Choice of the default.** The protocol provided that `intent` becomes the default mode if the
defect was observed under either of two criteria: under `base`, fewer than half of the calls
see SectorMomentum (0 of 403); or the gross exposure of `base` is more than 10 points below
that of `intent` (0.15 vs 1.00).
Le compteur constate le filtrage sous `base`, mais reste à zéro dans les deux modes : il ne
vérifie pas la reconstruction. La preuve qui discrimine les modes est l'exposition brute,
confortée par les corrélations du tableau. Le changement rend le code conforme à ce qu'annonce
`MultiStrategyPCM` ; il ne crée pas d'avantage démontré.

**Limits.**
- The variant (sleeves, QQQ, return weights) was chosen after seeing the out-of-sample Sharpe
  of the original composite, hence with knowledge of part of the period. This bias favoured
  the candidates, which strengthens the `NO BEATS`.
- The backtests requested an end on 2026-09-30. The compute nodes used hold back the last 90
  days and brought the end to 2026-07-10, without error. All versions ran on the same nodes:
  the comparisons cover the same sessions. The `intent` run of #19758 ends on 2026-07-09.

## Project parameters

All optional:

| Parameter | Default | Role |
|-----------|---------|------|
| `mode` | `intent` | `intent`: sleeves added per ticker; `base`: original code; `sm`, `rs`: a single alpha model, at 100%; `spy`: SPY held; `sixty40`: 60% SPY and 40% IEF, rebalanced on the first trading day of each month |
| `start`, `end` | `2018-01-01`, `2025-01-01` | backtest window |
| `sm_allocation`, `rs_allocation` | 0.85, 0.15 | sleeves of the two models |
| `sm_weights` | `0.5,0.2,0.2,0.1` | weights of SectorMomentum's 1, 3, 6 and 12-month returns |
| `rs_lookback` | 63 | RegimeSwitching momentum window, in sessions |
| `fee_mult` | 1 | brokerage fee multiplier |

The `shadow` chart carries the portfolio value at each close; the runtime statistics give the
orders per ETF, the average gross exposure and the PCM counters.

## Figures prior to #19759

The two sections below predate the measure; they are kept for the record.

**Reading corrected by #19759.**
- **Figures.** The `readme` run (`base` over 2018-01-01 → 2025-01-01, 1760 sessions)
  reproduces the registry's figures on the same window: QC Sharpe −0.72 (vs −0.729), CAGR
  1.87% (1.88%), max drawdown 4.4% (4.3%), 290 orders. The PSR differs (0% vs 17.4%); the cause
  was not measured. The table below does not state its window; a 21.1% net profit at 1.76% a
  year matches about eleven years, i.e. the original 2015-2025 window.
- **Negative Sharpe.** QC's Sharpe subtracts a risk-free rate that the 85% cash does not earn
  in the backtest. At a zero risk-free rate, `base` has the Sharpe of RegimeSwitching alone
  (0.90 vs 0.91): the variant did not destroy value through its choices, it was only 15%
  invested.
- **Causes 1 and 2 (over-concentration on SectorMomentum, QQQ diluting the signal).**
  SectorMomentum did not trade under `base`: these causes cannot explain the result. Under
  `intent`, QQQ carries 37% of the closed-position result.
- **Cause 3 (low beta, defensive assets).** The 0.081 beta comes from the 0.15 gross exposure,
  not from the choice of assets.
- **Cause 4 (RegimeSwitching too small to matter).** It was the opposite: RegimeSwitching at
  15% was the only invested sleeve.
- **Baseline.** Framework_Composite_MomentumRegime carried the same defect (#19740): the
  "baseline vs variant" comparison set two versions against each other in which SectorMomentum
  did not trade.

### Backtest Results

| Metric | Baseline (T60/RS40) | This Variant (T85/RS15) | Delta |
|--------|---------------------|--------------------------|-------|
| Sharpe Ratio | 0.185 | **-0.74** | -0.925 |
| CAGR | 4.73% | 1.76% | -2.97pp |
| Max Drawdown | - | 4.4% | - |
| Net Profit | - | 21.1% | - |
| Beta (vs SPY) | - | 0.081 | - |
| Total Orders | - | 403 | - |
| Win Rate | - | 71% | - |

**Verdict: NO BEATS.** Negative Sharpe ratio. The 85/15 shift destroyed value.

### Analysis

The variant dramatically underperforms the baseline. Root causes:

1. **Over-concentration on SectorMomentum**: At 85% weight, SectorMomentum
   dominates allocations. When its monthly signal flips (common with short-term
   lookbacks 0.5/0.2/0.2/0.1), the portfolio churns between assets.

2. **QQQ addition dilutes signal quality**: Adding QQQ to SectorMomentum's
   universe creates a 4-way race where the best-scored asset rotates frequently,
   generating unnecessary turnover.

3. **Low beta (0.081)**: The strategy spends most time in defensive assets (IEF/GLD)
   despite bull market conditions, suggesting SectorMomentum's composite scoring
   with short-term bias overweights transient pullbacks.

4. **RegimeSwitching at 15%**: Too small to matter. The regime-switching safety net
   that protects in bear/sideways markets is effectively disabled.

## Files

- main.py - Strategy (T85/RS15 allocation), instrumented for measure #19759
- alpha_models.py - SectorMomentum + RegimeSwitching alpha models
- portfolio_construction.py - MultiStrategyPCM portfolio construction (`intent` mode taken from #19758)

## References

- Hands-On AI Trading, Section 06
- Baseline: Framework_Composite_MomentumRegime
