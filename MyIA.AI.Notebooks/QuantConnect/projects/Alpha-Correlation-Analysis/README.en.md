# Alpha Correlation Analysis

**Type:** Research (analytical notebook, no trading algorithm)
**Environment:** local yfinance (cell[1] `Local environment detected`, mechanism #8772 disclosed) — `QuantBook()` raises `NameError` (QC Cloud / Lean unavailable), explicit `yfinance` fallback branch activated
**Effective period:** 2021-06-01 → 2026-05-29 (5 years, 1255 daily sessions, cell[6] data shape)

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

1. **Return Stream Collection**: `yfinance` local 18 tickers, 1255 days (2021-06-01 → 2026-05-29), 7 alphas built (cell[6] + cell[20])
2. **Correlation Matrix**: 7×7 correlation matrix between alpha returns (cell[22])
3. **Regime Analysis**: classification into 8 regimes (Bull/Bear/Sideways × High/Med/Low-Vol) then Sharpe by regime (cell[26]-[28])
4. **Complementarity Score**: pair ranking by combined score (inverse correlation × regime diversification × downside protection, cell[30])
5. **Top Pairs Analysis**: deep dive on top-3 by complementarity (cell[32])
6. **Walk-Forward Validation**: OOS 15 rolling quarterly windows (cell[36]) — top-1 pair **Average Test Sharpe 0.84** (cell[36])

## Verified results (multi-source: cell[N] cited)

> **Honest note (#1621, drainage #9434)**: the legacy README presented a "Preliminary Results" table with 3 **hand-chosen pairs**, of which **one is fabricated**: "Trend-Following + Mean-Reversion ~0.0 correlation" does NOT exist in the cell[22] correlation matrix — the actual Trend-Following / Mean-Reversion correlation is **0.463** (cell[22] stream output). The 2 other legacy lines ("EMA-Cross + All-Weather ~0.3" and "Dual-Momentum + Mean-Reversion ~0.1") are rounded approximations of the actual cell[34] values (see table below). The table below cites **directly the cell[N] outputs** of the quantbook, without reformulation.

### Top 10 Complementary Pairs (cell[34] verbatim)

| # | Pair | Correlation | Sharpe α₁ | Sharpe α₂ | **Combined Sharpe (50/50)** | Synergy | Regime_Div | DD_Protection |
|---|------|-------------|-----------|-----------|------------------------------|---------|------------|---------------|
| 1 | EMA-Cross-Tech / Mean-Reversion | **0.054** | 1.105 | 0.563 | **1.210** | 0.376 | 1.919 | 0.000 |
| 2 | Momentum-SPY / Mean-Reversion | **0.101** | 0.967 | 0.563 | **1.071** | 0.306 | 1.372 | 0.045 |
| 3 | **EMA-Cross-Tech / Dual-Momentum** | **0.200** | 1.105 | 1.096 | **1.420** ⭐ | 0.320 | 1.253 | 0.163 |
| 4 | Dual-Momentum / Mean-Reversion | **0.138** | 1.096 | 0.563 | **1.171** | 0.342 | 1.084 | 0.000 |
| 5 | Momentum-SPY / Dual-Momentum | **0.248** | 0.967 | 1.096 | **1.302** | 0.270 | 1.299 | 0.000 |
| 6 | EMA-Cross-Tech / All-Weather | **0.277** | 1.105 | 0.598 | **1.128** | 0.277 | 1.616 | 0.051 |
| 7 | EMA-Cross-SPY / Mean-Reversion | **0.113** | 0.872 | 0.563 | **0.989** | 0.272 | 0.840 | 0.021 |
| 8 | Mean-Reversion / All-Weather | **0.273** | 0.563 | 0.598 | **0.722** | 0.142 | 1.080 | 0.000 |
| 9 | Dual-Momentum / Trend-Following | **0.279** | 1.096 | 0.658 | **1.128** | 0.251 | 0.980 | 0.040 |
| 10 | Momentum-SPY / All-Weather | **0.397** | 0.967 | 0.598 | **0.938** | 0.156 | 1.314 | 0.000 |

⭐ **Top combined Sharpe**: EMA-Cross-Tech / Dual-Momentum (1.420). Note: although their correlation (0.200) is higher than other pairs (ex. EMA-Cross-Tech / Mean-Reversion 0.054), the higher combined Sharpe (1.420 vs 1.210) is due to both individual Sharpes being strong (1.105 + 1.096).

### Top-3 detail (cell[32] verbatim)

| Pair | Combined Return (ann.) | Volatility | Combined Sharpe | Correlation |
|------|------------------------|------------|------------------|-------------|
| EMA-Cross-Tech / Mean-Reversion | 11.96 % | 9.89 % | 1.21 | 0.054 |
| Momentum-SPY / Mean-Reversion | 7.00 % | 6.53 % | 1.07 | 0.101 |
| EMA-Cross-Tech / Dual-Momentum | 19.80 % | 13.94 % | 1.42 | 0.200 |

### Sharpe by regime (cell[28] verbatim)

| Alpha | Bear-High-Vol | Bear-Med-Vol | Bull-High-Vol | Bull-Low-Vol | Bull-Med-Vol | Sideways-High-Vol | Sideways-Low-Vol | Sideways-Med-Vol |
|-------|---------------|--------------|---------------|--------------|--------------|-------------------|------------------|------------------|
| All-Weather | 1.98 | 7.04 | 0.33 | 0.18 | 1.48 | -1.14 | 0.40 | 0.51 |
| Dual-Momentum | 0.09 | 5.86 | -0.23 | 1.73 | 2.65 | 0.18 | 0.58 | 1.26 |
| EMA-Cross-SPY | 0.00 | 0.00 | 0.60 | 0.87 | 1.21 | 0.53 | 0.28 | 1.10 |
| EMA-Cross-Tech | 0.00 | -4.16 | 0.41 | 1.70 | 0.77 | -0.44 | 0.39 | 2.28 |
| Mean-Reversion | 1.02 | 4.53 | 0.00 | -0.97 | 1.42 | -1.21 | 2.32 | 0.96 |
| Momentum-SPY | 0.53 | -3.74 | 0.75 | 1.00 | 1.08 | 1.87 | 0.27 | 0.90 |
| Trend-Following | 0.69 | 2.73 | 0.78 | 0.87 | 1.19 | -0.58 | 0.07 | 0.87 |

### Walk-Forward OOS — top-1 pair (cell[36] verbatim, 15 quarterly windows)

Pair: **EMA-Cross-Tech / Mean-Reversion** (best overall score cell[30]).

| Period | Train_Corr | Test_Return | Test_Sharpe |
|---------|-----------|-------------|-------------|
| 2021-06-01 → 2022-08-29 | 0.0575 | -15.19 % | -1.66 |
| 2021-08-30 → 2022-11-28 | 0.0596 | -12.98 % | -4.52 |
| 2021-11-29 → 2023-03-01 | 0.0417 | -4.23 % | -0.43 |
| 2022-03-01 → 2023-05-31 | 0.0184 | +67.48 % | **+5.44** ⭐ |
| 2022-05-31 → 2023-08-30 | 0.0133 | +19.07 % | +1.80 |
| 2022-08-30 → 2023-11-29 | 0.0396 | -25.14 % | -2.72 |
| 2022-11-29 → 2024-03-01 | 0.0176 | +34.72 % | +3.27 |
| 2023-03-02 → 2024-05-31 | 0.0170 | +27.42 % | +2.47 |
| 2023-06-01 → 2024-08-30 | 0.1387 | -9.25 % | -0.72 |
| 2023-08-31 → 2024-11-29 | 0.2589 | +21.55 % | +2.46 |
| 2023-11-30 → 2025-03-05 | 0.2861 | +2.73 % | +0.24 |
| 2024-03-04 → 2025-06-04 | 0.2483 | +9.56 % | +0.75 |
| 2024-06-03 → 2025-09-04 | 0.0742 | +35.99 % | +4.47 |
| 2024-09-03 → 2025-12-03 | 0.0082 | +28.49 % | +2.90 |
| 2024-12-02 → 2026-03-06 | 0.0233 | -9.66 % | -1.20 |
| **Average OOS** | — | — | **+0.84** |

**Honest reading — OOS window 2021-2026 over 5 years**: the **Average Test Sharpe 0.84** is encouraging BUT the inter-window variance is huge (range -4.52 to +5.44, ratio 10×) — **the pair is regime-sensitive** and the positive OOS is mainly driven by 2022-2024 (bear + recovery, Mean-Reversion favorable context). Windows 2023-08 / 2024-12 show a **Train_Corr degradation > 0.25** (vs 0.02 in-sample) → **in-sample → OOS stability is NOT guaranteed**. **NOT a live deployment signal without multi-regime walk-forward** (≥4 bull/bear/sideways cycles).

## Honest reading — legacy vs cell[N] divergence

The "Preliminary Results" table of the legacy README (before c.1285) presented **3 "chosen" pairs**:

| Legacy (before c.1285) | Actual (cell[N]) | Verdict |
|-------------------------|-------------------|---------|
| "EMA-Cross + All-Weather ~0.3 correlation, combined Sharpe > 0.8" | cell[34] row 6: EMA-Cross-Tech / All-Weather corr=**0.277**, Sharpe=**1.128** | **OK** (rounded ~0.3, > 0.8 verified) |
| "Dual-Momentum + Mean-Reversion ~0.1 correlation, combined Sharpe > 0.7" | cell[34] row 4: Dual-Momentum / Mean-Reversion corr=**0.138**, Sharpe=**1.171** | **OK** (rounded ~0.1, > 0.7 verified, but ~0.1 is permissive rounding of 0.138) |
| "Trend-Following + Mean-Reversion ~0.0 correlation, combined Sharpe > 0.6" | cell[22]: Trend-Following / Mean-Reversion corr=**0.463** (NOT in top-10 cell[24] nor cell[34]) | **❌ FABRICATED** — correlation 0.463, NOT ~0.0; the pair does not appear in any top-10 ranking |

**Cause**: the "preliminary" README table appears to be a **manual round-numbered synthesis** without back-citation to cell[N]. The 3rd line is particularly false: the actual correlation 0.463 is in the **medium-high range** of the matrix (cf. cell[22] stream), not "~0.0". **NOT a live deployment signal** for a Trend-Following + Mean-Reversion composite on the strength of this line.

**C.4 §D.5 verdict**: `CAUSE_DOCUMENTED_ONLY` — the divergence is **DOCUMENTED** by the cell[N] outputs. NOT a bug, NOT a regression of code cells. The **fix**: replace the synthetic "preliminary" table with the **cell[34] verbatim table** + honest reading of the divergence. No cosmetic re-alignment (refusal §D.5 "main-align on a volatile number without re-execution").

**Anti-regression diagnostic**: `quantbook.ipynb` is intact (cell[22]/[24]/[28]/[30]/[32]/[34]/[36] unchanged, no code cell touched). The fix is **markdown-only** (C.2 exception).

## How to run

**Locally** (mechanism #8772 disclosed):
```bash
jupyter nbconvert --execute "MyIA.AI.Notebooks/QuantConnect/projects/Alpha-Correlation-Analysis/quantbook.ipynb" \
  --to notebook --inplace --ExecutePreprocessor.timeout=600
```
**Expected**: `Local environment detected - yfinance will be used for data` (cell[1]), then 18 tickers yfinance 2021-06-01 → today, cells[22]/[28]/[34]/[36] outputs identical (± yfinance Daily updates variations).

**QC Cloud** (authentic): NOT tested — `QuantBook()` raises `NameError` in the environment that produced the committed outputs (cell[2] explicit disclose). For the declared window `2020-01-01 → 2024-12-31` of cell[1], **re-execute via QC Cloud** once the environment is restored.

**Note on Docker Lean**: `lean research` with this folder uses `QuantBook()` by default; expect the same `NameError` + yfinance branch. If the Lean docker is restored, `lean research "MyIA.AI.Notebooks/QuantConnect/projects/Alpha-Correlation-Analysis"` should work with the declared 2020-2024 window.

## Files

- `quantbook.ipynb` — 38 cells (37 code + 1 original markdown). **Single source of truth** for the figures. Outputs cell[22]/[28]/[34]/[36] preserved. Disclaimer #8772 in cell[2].
- `README.md` — Overview + multi-source + honest reading (c.1285 fix).
- `README.en.md` (this file) — English sibling sync.

## References

- Issue [#140 - Complementary Alpha Combinations](https://github.com/jsboige/CoursIA/issues/140) (CLOSED, scope delivered).
- Mechanism #8772 (disclosed `yfinance` fallback when `QuantBook()` unavailable, cf `quantbook.ipynb:cell[2]`).
- Cell[22] (correlation matrix 7×7), cell[24] (top-10 least correlated pairs), cell[28] (Sharpe by regime), cell[30] (top-10 complementary pairs), cell[32] (top-3 detailed analysis), cell[34] (final recommendations), cell[36] (walk-forward OOS).
- c.1279 arche (DualMomentum README stale 0.350→3 sources, #9511/#9530) — sister pattern "stale figure → multi-source cited table".
- #1621 (drainage epic — real measured prose vs stale in repo).
- #9434 (drainage umbrella — multi-PR cleanup of stale READMEs).