# S4 v2 Inverse Vol Ridge + HMM Regime — Verdict

Date: 2026-10-20 20:12

Universe: SPY + TLT + 9 sector ETFs
Defensive tilt (bear): TLT, XLP, XLU, XLV
Method: HMM regime-conditional inverse-vol Ridge (MarkovRegression 2-regime)
Ridge alphas: [0.01, 0.1, 1.0, 10.0, 100.0]
Tx costs: 5bps per rebalance, 50bps stress
Walk-forward: 5-fold expanding, OOS 2027 strict
Multi-seed: block bootstrap (22-day), seeds [0, 1, 7, 42]

Method (causal, #21633): regime fitted on data strictly before each test block, named on the training window, held across the block; 1-day decision lag at the fold boundary
Significance: Ledoit-Wolf (HAC) + Holm vs equal-weight and SPY held

## Results

- **Verdict**: INCONCLUSIVE
- Ridge Sharpe: 1.1042
- Equal-Weight Sharpe: 0.8650
- Mean delta (multi-seed): +0.239207 (SE=0.000805, t=297.116)
- Delta bear regime: +0.5685
- Seeds positive: 4/4 (p=0.0625)

### Significance (seed 0, pre-registered)

- vs equal_weight: delta-Sharpe +0.2386 (Ledoit-Wolf p=0.1897, Holm p=0.3795, bootstrap CI95 [-0.152, +0.616])
- vs spy_held: delta-Sharpe +0.1955 (Ledoit-Wolf p=0.3383, Holm p=0.3795, bootstrap CI95 [-0.209, +0.593])

### Témoin de fuite (in-sample replay)

- Sharpe in-sample (ré-ajusté sur le bloc de test): 0.0551
- Sharpe causal (seed 0): 1.1036
- **Écart porté par la lecture du futur**: -1.0485

## Per-seed detail

| Seed | Ridge | EqW | Delta | Delta-Bear | Bull% | Alpha |
|------|-------|-----|-------|------------|-------|-------|
| 0 | 1.1036 | 0.8650 | +0.2386 | +0.5685 | 50% | 100.0 |
| 1 | 1.1066 | 0.8650 | +0.2416 | +0.5685 | 50% | 100.0 |
| 7 | 1.1036 | 0.8650 | +0.2386 | +0.5685 | 50% | 100.0 |
| 42 | 1.1031 | 0.8650 | +0.2381 | +0.5685 | 50% | 10.0 |
