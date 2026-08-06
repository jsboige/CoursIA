# Paired cross-rung comparison -- Kronos vs M15 (#8607)

**Question**: is M15 significantly different from Kronos on the directional edge?

**Alignment**: 45 paired (symbol, horizon, seed) observations. mean edge A=-0.03016, mean edge B=-0.03064.

| metric | value |
|--------|-------|
| n pairs | 45 |
| mean diff (B-A) | -0.00047 |
| std diff | 0.02845 |
| paired t-stat (df=44) | -0.112 |
| t p-value | 0.9114 |
| CI95 (mean diff) | [-0.00902, +0.00807] |
| Wilcoxon p | 0.7971 |
| sign p (n+=20, n-=25) | 0.5515 |
| direction | B worse than A (more negative edge) |
| **verdict (alpha=0.05)** | not significant: mean paired diff -0.00047 (CI95 [-0.00902, +0.00807]), t=-0.112 (p=0.9114), B worse than A (more negative edge) |

## Interpretation

Both rungs are individually NO BEATS vs majority (cf `seed_significance_verdict.md`). This paired test asks whether they differ **from each other**. A non-significant paired difference means fine-tuning (B) did not change the directional edge relative to zero-shot (A) -- reinforcing the #1409 conclusion that directional forecasting edge is absent regardless of the forecasting paradigm; alpha comes from **action policies** (L4-DT), not price-direction prediction.

## Scope / residual

- This is a paired-by-(config, seed) test on committed per-seed edges, **not** a full Diebold-Mariano by-observation test. The true DM needs the per-window DirAcc series (Kronos dumps only the fold aggregate) -> multi-cycle residual (re-run dumping per-window forecasts).
