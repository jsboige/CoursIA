# Paired cross-rung comparison -- Chronos-Bolt vs M15 (#8607)

**Question**: is M15 significantly different from Chronos-Bolt on the directional edge? (A=Chronos deterministic, paired vs per-seed)

**Alignment**: 35 paired (symbol, horizon, seed) observations. mean edge A=-0.03009, mean edge B=-0.03027.

| metric | value |
|--------|-------|
| n pairs | 35 |
| mean diff (B-A) | -0.00018 |
| std diff | 0.02755 |
| paired t-stat (df=34) | -0.039 |
| t p-value | 0.9694 |
| CI95 (mean diff) | [-0.00964, +0.00928] |
| Wilcoxon p | 0.5988 |
| sign p (n+=24, n-=11) | 0.04096 |
| direction | B worse than A (more negative edge) |
| **verdict (alpha=0.05)** | not significant: mean paired diff -0.00018 (CI95 [-0.00964, +0.00928]), t=-0.039 (p=0.9694), B worse than A (more negative edge) |

## Interpretation

Both rungs are individually NO BEATS vs majority (cf `seed_significance_verdict.md`). This paired test asks whether they differ **from each other**. A non-significant paired difference means fine-tuning (B) did not change the directional edge relative to zero-shot (A) -- reinforcing the #1409 conclusion that directional forecasting edge is absent regardless of the forecasting paradigm; alpha comes from **action policies** (L4-DT), not price-direction prediction.

## Scope / residual

- This is a paired-by-(config, seed) test on committed per-seed edges, **not** a full Diebold-Mariano by-observation test. The true DM needs the per-window DirAcc series (Kronos dumps only the fold aggregate) -> multi-cycle residual (re-run dumping per-window forecasts).
