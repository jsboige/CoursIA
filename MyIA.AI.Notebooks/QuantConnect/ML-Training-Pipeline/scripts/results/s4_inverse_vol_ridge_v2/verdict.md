# S4 v2 Inverse Vol Ridge + HMM Regime — Verdict

Date: 2026-05-16 16:48

Universe: SPY + TLT + 9 sector ETFs
Defensive tilt (bear): TLT, XLP, XLU, XLV
Method: HMM regime-conditional inverse-vol Ridge (MarkovRegression 2-regime)
Ridge alphas: [0.01, 0.1, 1.0, 10.0, 100.0]
Tx costs: 5bps per rebalance, 50bps stress
Walk-forward: 5-fold expanding, OOS 2027 strict
Multi-seed: block bootstrap (22-day), seeds [0, 1, 7, 42]

## Results

- **Verdict**: BEATS
- Ridge Sharpe: 1.1238
- Equal-Weight Sharpe: 0.7984
- Delta: +0.325410 (SE=0.000475, t=684.487)
- Delta bear regime: +0.8879
- Seeds positive: 4/4 (p=0.0625)
- Gate: delta > 0.10, t >= 2.0, >= 3/4 seeds positive

## Per-seed detail

| Seed | Ridge | EqW | Delta | Delta-Bear | Bull% | Alpha |
|------|-------|-----|-------|------------|-------|-------|
| 0 | 1.1233 | 0.7984 | +0.3249 | +0.9354 | 69% | 100.0 |
| 1 | 1.1236 | 0.7984 | +0.3252 | +0.8441 | 69% | 100.0 |
| 7 | 1.1231 | 0.7984 | +0.3247 | +0.8554 | 69% | 100.0 |
| 42 | 1.1252 | 0.7984 | +0.3268 | +0.9167 | 69% | 10.0 |
