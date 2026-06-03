# RECAP KEEPERS V2 — Cross-Strategy Summary

Date: 2026-05-19
Source: Curriculum V2 Meta-Analysis + S3 extended hardening (12 seeds)

## KEEPERS V2 (4 confirmed)

| # | Strategy | Sharpe (BEATS delta) | vs B&H delta | CAGR | MaxDD | p-value | Seeds | Migration QC |
|---|----------|---------------------|-------------|------|-------|---------|-------|-------------|
| 1 | S3 HMM Regime (2-state) | +0.669 | +0.669 | — | -39.1% | 0.0625 (4/4) | 4→12 | Hardcoded regime params |
| 2 | S4 v2 Regime+Ridge | +0.325 | +0.325 | — | -17.7% | 0.0625 (4/4) | 4 | Monthly rebalance loop |
| 3 | S1 M12 HAR-RV-J | BEATS | — | — | — | 0.0015 | 84 combos | Vol forecast module |
| 4 | S1 M15 LSTM h=32 | BEATS | — | — | — | 0.0107 | 84 combos | Torch inference in QC |

### S3 Extended Hardening (12/12 seeds confirmed)

Seeds extended from [0,1,7,42] to [0,1,7,42,99,123,456,789,202,303,404,505].

| Metric | Value |
|--------|-------|
| Seeds BEATS | 12/12 (100%) |
| Sharpe range | 1.34–1.46 |
| Verdict | **BEATS confirmed on extended seeds** |
| Status | Anti-confirmation-bias test PASSED |

## Non-KEEPERS (CLOSED)

| Stage | Strategy | Verdict | Delta | Seeds | Why rejected |
|-------|----------|---------|-------|-------|-------------|
| S2 | DM Ensemble | NO BEATS | -0.068 | 0/4 | Adds noise, not signal |
| S2 | GSP Cross-Asset | NO BEATS | — | — | MSE -12% but no Sharpe translation |
| S4 v1 | Ridge (no regime) | NO BEATS | +0.022 | 4/4 | MaxDD -82.4%, no edge |
| S5 | LASSO Stop-Loss | NO BEATS | -0.311 | 0/4 | Premature exits in bull market |
| S7 | Composite (all layers) | NO BEATS | -0.006 | 1/4 | Signal redundancy, gate never triggers |
| S8 | Trend Long-Horizon ML | NO BEATS | +0.12 | — | AUC 0.61 below 0.55 gate |

## POC (calibration needed)

| Stage | Strategy | Status | Key Metric |
|-------|----------|--------|------------|
| S6 | Cost Forecasting | GO (POC) | 57.7% skip rate, p < 0.001 |

## Recommended Portfolio Construction

```
Signal: S3 HMM Regime (2-state bull/bear)
Weights: S4 v2 Regime-conditional inverse-vol Ridge
Universe: SPY, TLT, XLF, XLK, XLE, XLV, XLY, XLI, XLB, XLU, XLP
Rebalance: Monthly
Tx costs: 10bps per rebalance
Expected Sharpe: ~1.12 (vs 0.80 equal-weight)
Expected MaxDD: -17.7%
Regime switches: ~5/year
```

## QC Migration Notes

| Strategy | Complexity | Dependencies | Feasibility |
|----------|-----------|-------------|-------------|
| S3 HMM Regime | Medium | hmmlearn, sklearn | High — hardcoded params |
| S4 v2 Regime+Ridge | Medium | sklearn, numpy | High — standard ML |
| S1 M12 HAR-RV-J | Low | numpy only | Very high |
| S1 M15 LSTM h=32 | High | torch | Medium — needs Torch in QC |

## Key Methodology

- Walk-forward 5-fold expanding windows
- OOS 2027 strict holdout
- Multi-seed block bootstrap (22-day blocks)
- Seeds: [0,1,7,42] standard, [99,123,456,789] extended, [202,303,404,505] S3 hardening
- Tx costs: 10bps rebalance + 50bps stress
- Universe: Anti-FAANG/Mag7 (SPY, TLT, 9 sector ETFs)
- BEATS gate: delta >= +0.10, >= 3/4 seeds positive
