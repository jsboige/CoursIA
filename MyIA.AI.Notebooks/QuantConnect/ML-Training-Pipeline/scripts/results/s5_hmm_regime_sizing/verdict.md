# S5 HMM Regime Sizing — Verdict

Hypothesis: regime-conditional SIZING via HMM probability (continuous blend) beats S4's hard regime switch

Date: 2026-07-26 06:58

- **Verdict**: NO BEATS
- Continuous Sharpe: 0.7394
- Hard-switch (S4) Sharpe: 0.7393
- Equal-weight Sharpe: 0.7604
- Inv-vol Sharpe: 0.4214
- Delta vs hard: +0.000103 (SE=0.000313, t=0.328)
- Seeds positive: 2/4 (p_sign=0.6875)
- Gate: delta >= 0.1, t >= 2.0, >= 3/4 seeds positive

## Per-seed summary

| Seed | Continuous | Hard | Delta | Equal | InvVol | mean p_bear |
|------|-----------|------|-------|-------|--------|-------------|
| 0 | 0.7395 | 0.7395 | +0.0000 | 0.7604 | 0.4214 | 0.274 |
| 1 | 0.7397 | 0.7402 | -0.0005 | 0.7604 | 0.4214 | 0.284 |
| 7 | 0.7395 | 0.7396 | -0.0001 | 0.7604 | 0.4214 | 0.254 |
| 42 | 0.7389 | 0.7379 | +0.0010 | 0.7604 | 0.4214 | 0.342 |
