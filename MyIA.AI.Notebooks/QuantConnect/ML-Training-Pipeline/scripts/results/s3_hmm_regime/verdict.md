# S3 HMM Regime Detection — Verdict

Date: 2026-05-16 09:08

Method: MarkovRegression 2-regime (statsmodels)
Features: SPY returns + TLT returns + VIX level
Allocation: bull -> 100% SPY, bear -> 100% TLT
Tx costs: 10bps per switch
Multi-seed: block bootstrap (22-day blocks), seeds 0/1/7/42
Walk-forward: 5-fold expanding window

## Variant: Daily

- **Verdict**: BEATS
- Mean delta-Sharpe: +0.669322 (SE=0.031510, t=21.241)
- Regime-aware Sharpe: 1.4025 vs B&H 0.7331
- Max Drawdown: -0.3910
- Switching: 5.0/year
- Seeds positive: 4/4 (p=0.0625)
- Gate: delta > 0.20 AND (t >= 2.0 OR all seeds identical) AND >= 3/4 seeds positive

## Variant: Weekly (Long-Horizon)

- **Verdict**: NO BEATS
- Mean delta-Sharpe: -0.481533 (SE=0.102884, t=-4.680)
- Regime-aware Sharpe: 1.0777 vs B&H 1.5593
- Max Drawdown: -0.3859
- Switching: 8.5/year
- Seeds positive: 0/4 (p=1.0000)
- Gate: delta > 0.20 AND (t >= 2.0 OR all seeds identical) AND >= 3/4 seeds positive

## Comparative

| Metric | Daily | Weekly |
|--------|-------|--------|
| Verdict | BEATS | NO BEATS |
| Delta-Sharpe | +0.6693 | -0.4815 |
| Regime Sharpe | 1.4025 | 1.0777 |
| B&H Sharpe | 0.7331 | 1.5593 |
| Switches/year | 5.0 | 8.5 |
| Seeds pos | 4/4 | 0/4 |

## Gate S3

**Gate S3 = GO**
Condition: at least one variant BEATS (delta > 0.2, t >= 2.0, >=3/4 seeds positive)
