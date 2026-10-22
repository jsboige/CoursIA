# Alpha Correlation Analysis

**Type:** Research (analytical notebook, no trading algorithm)
**Environment:** local yfinance (cell[1] `Local environment detected`, mechanism #8772 disclosed) — `QuantBook()` raises `NameError` (QC Cloud / Lean unavailable), explicit `yfinance` fallback branch activated
**Effective period:** 2020-01-02 → 2024-12-31, pinned to the period declared in cell[1] (range printed by cell[6])

> 🇫🇷 **Version française** : voir [`README.md`](README.md)
> **Issue source:** [#140 - Complementary Alpha Combinations](https://github.com/jsboige/CoursIA/issues/140) (CLOSED, scope delivered)

## Objective

Identify truly complementary alpha combinations for QuantConnect composite strategies.

## Problem

Current composites combine correlated alphas:
- **TrendWeather (Sharpe 1.155)** = TrendStocks + AllWeather, but TrendStocks dominates (original claim, see c.1284-L1 ★★ on the "sweep-comment" archetype for the provenance of this 1.155)
- **FamaFrench + AllWeather**: monotone sweep towards AllWeather (FF does not diversify)
- **MomentumSector + RegimeSwitching**: double defense in stress periods (both are defensive at the same time)

## Methodology (cell[1]-[36] of `quantbook.ipynb`)

1. **Return Stream Collection**: adjusted `yfinance` close prices over the pinned 2020-2024 window, then daily return series of the alphas (cell[6] + cell[20])
2. **Correlation Matrix**: correlation matrix between alpha returns (cell[22])
3. **Regime Analysis**: classification into regimes (Bull/Bear/Sideways × High/Med/Low-Vol) then Sharpe by regime (cell[26]-[28])
4. **Complementarity Score**: pair ranking by combined score (inverse correlation × regime diversification × downside protection, cell[30])
5. **Top Pairs Analysis**: detailed analysis of the three leading pairs (cell[32])
6. **Walk-Forward Validation**: rolling quarterly windows, training on 252 sessions then testing on the next 63 (cell[36]) — leading pair **Average Test Sharpe 0.55**

## The window is pinned (#21836)

The `yfinance` fallback used to request `period="5y"`, i.e. the last five years counted from the execution time. Each re-execution moved the window, and the figures of this README with it: the previous version cited a 2021-06-01 → 2026-05-29 window.

The loading cell now passes the same bounds to both paths: `qb.History(symbol, start, end)` on the `QuantBook` side, `history(start=..., end=...)` on the `yfinance` side. Two successive runs differ only beyond the third decimal, and the tables below stay identical once rounded.

## Verified results (cell[N] cited)

### Complementary pairs (cell[34] verbatim)

Ranked by total complementarity score (cell[30]).

| # | Pair | Correlation | Sharpe α₁ | Sharpe α₂ | **Combined Sharpe (50/50)** | Synergy | Regime_Div | DD_Protection |
|---|------|-------------|-----------|-----------|------------------------------|---------|------------|---------------|
| 1 | EMA-Cross-Tech / Mean-Reversion | **0.152** | 1.015 | 0.796 | **1.153** | 0.247 | 1.433 | 0.702 |
| 2 | EMA-Cross-SPY / Mean-Reversion | **0.128** | 0.855 | 0.796 | **1.071** | 0.245 | 0.828 | 0.436 |
| 3 | **Momentum-SPY / Mean-Reversion** | **0.082** | 1.249 | 0.796 | **1.429** ⭐ | 0.407 | 1.452 | 0.000 |
| 4 | Dual-Momentum / Mean-Reversion | **0.283** | 0.574 | 0.796 | **0.735** | 0.050 | 1.056 | 0.341 |
| 5 | EMA-Cross-Tech / All-Weather | **0.368** | 1.015 | 0.517 | **1.001** | 0.235 | 1.572 | 0.064 |
| 6 | Momentum-SPY / All-Weather | **0.400** | 1.249 | 0.517 | **1.065** | 0.182 | 1.446 | 0.000 |
| 7 | Mean-Reversion / All-Weather | **0.152** | 0.796 | 0.517 | **0.799** | 0.143 | 0.727 | 0.000 |
| 8 | EMA-Cross-Tech / Dual-Momentum | **0.434** | 1.015 | 0.574 | **0.951** | 0.157 | 1.210 | 0.000 |
| 9 | EMA-Cross-SPY / Dual-Momentum | **0.450** | 0.855 | 0.574 | **0.795** | 0.081 | 1.013 | 0.000 |
| 10 | EMA-Cross-SPY / All-Weather | **0.428** | 0.855 | 0.517 | **0.825** | 0.139 | 0.843 | 0.183 |

`Synergy` = combined Sharpe minus the mean of the two individual Sharpes; it is positive for every pair in the table.

⭐ **Top combined Sharpe**: Momentum-SPY / Mean-Reversion (1.429), which is also the least correlated pair (0.082). It only ranks third on the total score, because its downside protection is zero (`DD_Protection` 0.000). The leading pair, EMA-Cross-Tech / Mean-Reversion, owes its rank to that component (0.702).

The first three pairs share the same Mean-Reversion leg: the ranking points to a diversifier first, more than to a pair.

### Detail of the three leading pairs (cell[32] verbatim)

| Pair | Combined Return (ann.) | Volatility | Combined Sharpe | Correlation |
|------|------------------------|------------|------------------|-------------|
| EMA-Cross-Tech / Mean-Reversion | 13.93 % | 12.09 % | 1.15 | 0.152 |
| EMA-Cross-SPY / Mean-Reversion | 8.11 % | 7.57 % | 1.07 | 0.128 |
| Momentum-SPY / Mean-Reversion | 9.93 % | 6.95 % | 1.43 | 0.082 |

### Sharpe by regime (cell[28] verbatim)

| Alpha | Bear-High-Vol | Bear-Med-Vol | Bull-High-Vol | Bull-Low-Vol | Bull-Med-Vol | Sideways-High-Vol | Sideways-Low-Vol | Sideways-Med-Vol |
|-------|---------------|--------------|---------------|--------------|--------------|-------------------|------------------|------------------|
| All-Weather | 2.05 | 4.79 | 2.59 | -0.45 | 0.94 | -1.59 | 0.19 | 0.61 |
| Dual-Momentum | 0.52 | 0.32 | 1.61 | 0.20 | 2.25 | 0.75 | 0.41 | 1.47 |
| EMA-Cross-SPY | 0.00 | 0.00 | 1.95 | 0.76 | 1.10 | 2.57 | 1.27 | 0.13 |
| EMA-Cross-Tech | 1.29 | -4.91 | 1.96 | 1.49 | 0.21 | -0.52 | 1.96 | 1.90 |
| Mean-Reversion | 2.74 | 2.49 | 0.00 | -0.35 | 0.92 | 0.38 | 0.17 | -0.12 |
| Momentum-SPY | 0.52 | -4.40 | 1.90 | 0.76 | 1.42 | 2.14 | 1.02 | 1.56 |
| Trend-Following | 2.22 | 2.10 | 1.75 | 0.76 | 1.46 | 0.38 | 1.18 | 1.07 |

The Bear-Med-Vol column rests on very few sessions (cell[26]): its extreme Sharpes (4.79, -4.91) are not to be read as measurements. What can be read: Mean-Reversion and All-Weather hold up in the Bear-High-Vol regime, where the trend alphas on SPY are flat or weak, and this is what makes them diversifiers.

### Walk-forward — leading pair (cell[36] verbatim)

Pair: **EMA-Cross-Tech / Mean-Reversion** (best total score, cell[30]). The period runs from the start of training to the end of the test; `Test_Return` is the daily mean of the test, annualized (×252), not the quarter's return.

| Period | Train_Corr | Test_Return (ann.) | Test_Sharpe |
|---------|-----------|--------------------|-------------|
| 2020-01-02 → 2021-04-01 | 0.196 | -1.6 % | -0.13 |
| 2020-04-02 → 2021-07-01 | 0.071 | +31.6 % | +3.31 |
| 2020-07-02 → 2021-09-30 | 0.082 | +9.3 % | +1.04 |
| 2020-10-01 → 2021-12-30 | 0.130 | +35.5 % | +2.75 |
| 2020-12-31 → 2022-03-31 | 0.121 | -19.4 % | -2.84 |
| 2021-04-05 → 2022-07-01 | 0.080 | -8.1 % | -1.14 |
| 2021-07-02 → 2022-09-30 | 0.059 | -30.9 % | -3.30 |
| 2021-10-01 → 2022-12-30 | 0.034 | -1.4 % | -1.65 |
| 2021-12-31 → 2023-04-03 | 0.012 | +24.7 % | +2.00 |
| 2022-04-01 → 2023-07-05 | 0.010 | +47.0 % | +3.95 |
| 2022-07-05 → 2023-10-03 | 0.022 | -2.3 % | -0.21 |
| 2022-10-03 → 2024-01-03 | 0.031 | -11.5 % | -1.35 |
| 2023-01-03 → 2024-04-04 | 0.017 | +44.2 % | +4.15 |
| 2023-04-04 → 2024-07-05 | 0.022 | +43.1 % | +3.96 |
| 2023-07-06 → 2024-10-03 | 0.141 | -28.0 % | -2.31 |
| **Average** | — | — | **+0.55** |

**Honest reading.** The 0.55 average hides a very wide dispersion, from -3.30 to +4.15: the pair alternates strongly positive and strongly negative quarters, following the regimes (2020-2021 recovery, 2022 decline, 2023 rise). The training correlation stays low over the whole period, which is the result being sought; the performance is not stable.

Two method limits:
- the tested pair is chosen on the whole window (cell[30]), test windows included. These windows are therefore not out-of-sample for the choice of the pair, and the average is optimistic;
- the test covers a single five-year window. Retaining the pair for a composite would require redoing the selection at each walk-forward step, over several market cycles.

## Divergence from the original "Preliminary Results" table

The original README (before c.1285) presented **three hand-chosen pairs**, with no reference to the notebook outputs. Against the pinned window:

| Original line | Measurement (cell[N]) | Verdict |
|---------------|-----------------------|---------|
| "EMA-Cross + All-Weather ~0.3 correlation, combined Sharpe > 0.8" | cell[34] rank 5: EMA-Cross-Tech / All-Weather, correlation **0.368**, combined Sharpe **1.001** | Sharpe > 0.8 verified; correlation closer to 0.4 than to 0.3 |
| "Dual-Momentum + Mean-Reversion ~0.1 correlation, combined Sharpe > 0.7" | cell[34] rank 4: correlation **0.283**, combined Sharpe **0.735** | **Wrong correlation** (≈ 0.3); Sharpe > 0.7 only just |
| "Trend-Following + Mean-Reversion ~0.0 correlation, combined Sharpe > 0.6" | cell[22]: correlation **0.194**; fifth least correlated pair (cell[24]), absent from the complementarity ranking (cell[30], cell[34]) | **Wrong**: 0.194, not ~0.0 |

None of the three lines names the leading pair of the ranking. The figures in this README all come from the notebook outputs, with the cell cited.

## How to run

**Locally** (mechanism #8772 disclosed):
```bash
jupyter nbconvert --execute "MyIA.AI.Notebooks/QuantConnect/projects/Alpha-Correlation-Analysis/quantbook.ipynb" \
  --to notebook --inplace --ExecutePreprocessor.timeout=600
```
**Expected**: `Local environment detected - yfinance will be used for data` (cell[1]), then the 2020-01-02 → 2024-12-31 range in cell[6], and tables identical to those of this README once rounded.

**QC Cloud** (authentic): not tested — `QuantBook()` raises `NameError` in the environment that produced the committed outputs (cell[2]). The `QuantBook` path requests the same window as the fallback; re-execution via QC Cloud remains to be done to obtain authentic `QuantBook` outputs.

**Note on Docker Lean**: `lean research` with this folder uses `QuantBook()`. If the local equity data stops before the end of 2024 (#8734), Lean extends the last bar as a constant (`fillDataForward=True`, flat-line artifact of #8719): check the range printed by cell[6] before reading the figures.

## Files

- `quantbook.ipynb` — **Single source of truth** for the figures. Environment note #8772 and pinned window in cell[2].
- `README.md` — French version.
- `README.en.md` (this file) — Overview + figures cited by cell.

## References

- Issue [#140 - Complementary Alpha Combinations](https://github.com/jsboige/CoursIA/issues/140) (CLOSED, scope delivered).
- Mechanism #8772 (disclosed `yfinance` fallback when `QuantBook()` unavailable, cf `quantbook.ipynb:cell[2]`).
- #21836 (QC notebooks with a sliding window: pin, declare, or classify as false positive).
- Cell[22] (correlation matrix), cell[24] (least correlated pairs), cell[28] (Sharpe by regime), cell[30] (most complementary pairs), cell[32] (detail of the three leading pairs), cell[34] (final recommendations), cell[36] (walk-forward).
- c.1279 arche (DualMomentum README stale 0.350→3 sources, #9511/#9530) — sister pattern "stale figure → multi-source cited table".
- #1621 (drainage epic — real measured prose vs stale in repo).
- #9434 (drainage umbrella — multi-PR cleanup of stale READMEs).
