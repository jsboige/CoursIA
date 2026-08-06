# Paired cross-rung comparison -- Chronos-Bolt vs Kronos (#8607)

**Question**: is Kronos significantly different from Chronos-Bolt on the directional edge? (A=Chronos deterministic, paired vs per-seed)

**Alignment**: 35 paired (symbol, horizon, seed) observations. mean edge A=-0.03009, mean edge B=-0.03209.

| metric | value |
|--------|-------|
| n pairs | 35 |
| mean diff (B-A) | -0.00200 |
| std diff | 0.03719 |
| paired t-stat (df=34) | -0.318 |
| t p-value | 0.7527 |
| CI95 (mean diff) | [-0.01477, +0.01078] |
| Wilcoxon p | 0.8374 |
| sign p (n+=17, n-=17) | 1 |
| direction | B worse than A (more negative edge) |
| **verdict (alpha=0.05)** | not significant: mean paired diff -0.00200 (CI95 [-0.01477, +0.01078]), t=-0.318 (p=0.7527), B worse than A (more negative edge) |

## Interpretation

Both rungs are individually NO BEATS vs majority (cf `seed_significance_verdict.md`). This paired test asks whether they differ **from each other**. A non-significant paired difference means fine-tuning (B) did not change the directional edge relative to zero-shot (A) -- reinforcing the #1409 conclusion that directional forecasting edge is absent regardless of the forecasting paradigm; alpha comes from **action policies** (L4-DT), not price-direction prediction.

## Scope / residual

- This is a paired-by-(config, seed) test on committed per-seed edges, **not** a full Diebold-Mariano by-observation test. The true DM needs the per-window DirAcc series (Kronos dumps only the fold aggregate) -> multi-cycle residual (re-run dumping per-window forecasts).
