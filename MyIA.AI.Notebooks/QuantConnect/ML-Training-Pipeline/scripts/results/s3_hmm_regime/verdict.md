# S3 HMM Regime Detection — Verdict (causal, #21633)

Date: 2026-10-20 19:58

Method: MarkovRegression 2-regime (statsmodels), **causal** walk-forward
Features: SPY returns + TLT returns + VIX level
Regime: fitted on the expanding window [0,t), refit every 22 days, named on the training window, 1-day decision lag
Allocation: bull -> 100% SPY, bear -> 100% TLT
Tx costs: 10bps per switch
Significance: Ledoit-Wolf (HAC) + Holm vs 50/50 rebalanced and SPY held
Multi-seed: block bootstrap of the training slice, seeds 0/1/7/42

## Variant: Daily

- **Verdict**: NO BEATS
- vs 50_50_rebalanced: delta-Sharpe -0.4929 (Ledoit-Wolf p=0.0568, Holm p=0.0568, bootstrap CI95 [-1.020, 0.053])
- vs spy_held: delta-Sharpe -0.6470 (Ledoit-Wolf p=0.0160, Holm p=0.0320, bootstrap CI95 [-1.152, -0.142])
- Mean delta-Sharpe (multi-seed): -0.348926 (SE=0.168380, t=-2.072)
- Regime-aware Sharpe: 0.3693 vs B&H 0.7182
- Max Drawdown: -0.4486
- Switching: 2.7/year
- Seeds positive: 0/4 (p=1.0000)

### Témoin de fuite (in-sample replay)

- Sharpe in-sample (lissé, sans décalage): 1.3601
- Sharpe causal (seed 0): 0.2255
- **Écart porté par la lecture du futur**: +1.1346 (delta-Sharpe +1.1346)

## Variant: Weekly (Long-Horizon)

- **Verdict**: NO BEATS
- vs 50_50_rebalanced: delta-Sharpe -0.9374 (Ledoit-Wolf p=0.0427, Holm p=0.0427, bootstrap CI95 [-1.870, -0.019])
- vs spy_held: delta-Sharpe -1.3854 (Ledoit-Wolf p=0.0088, Holm p=0.0176, bootstrap CI95 [-2.568, -0.443])
- Mean delta-Sharpe (multi-seed): -0.577257 (SE=0.229340, t=-2.517)
- Regime-aware Sharpe: 0.9572 vs B&H 1.5345
- Max Drawdown: -0.3954
- Switching: 2.1/year
- Seeds positive: 1/4 (p=0.9375)

### Témoin de fuite (in-sample replay)

- Sharpe in-sample (lissé, sans décalage): 1.2950
- Sharpe causal (seed 0): 0.5980
- **Écart porté par la lecture du futur**: +0.6970 (delta-Sharpe +0.6970)

## Comparative

| Metric | Daily | Weekly |
|--------|-------|--------|
| Verdict | NO BEATS | NO BEATS |
| Delta-Sharpe | -0.3489 | -0.5773 |
| Regime Sharpe | 0.3693 | 0.9572 |
| B&H Sharpe | 0.7182 | 1.5345 |
| Switches/year | 2.7 | 2.1 |
| Seeds pos | 0/4 | 1/4 |

## Verdict S3 (causal)

**S3 = NO BEATS**
Condition: the Ledoit-Wolf (HAC) delta-Sharpe is positive and Holm-significant (< 0.05) against BOTH references.
