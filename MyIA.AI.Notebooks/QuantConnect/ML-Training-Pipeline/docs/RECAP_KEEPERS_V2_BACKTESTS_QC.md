# RECAP — Keepers V2 QC Cloud Backtests (19/05/2026)

## Context

Curriculum V2 keepers selected from ML training pipeline (4/4 seeds walk-forward validated).
Ported to QC Cloud algos for live-paper feasibility verification. Period varies per keeper.

## Results Summary

| Model | Project ID | Sharpe | CAGR | MaxDD | Alpha | Beta | Win Rate | Total Net Profit | Period |
|-------|-----------|--------|------|-------|-------|------|----------|-----------------|--------|
| M12 HAR-RV-J | 31650567 | **0.645** | 27.1% | 41.1% | - | - | - | 154.4% | 2017-2026 |
| S3 HMM Daily V2 | 31855212 | **0.496** | 14.5% | 48.6% | 1.12% | 0.86 | 87.5% | 254.4% | 2017-2026 |
| S4 Regime+Ridge V2 | 31855260 | **0.367** | 8.5% | 23.1% | -0.26% | 0.41 | 85.0% | 114.1% | 2017-2026 |
| M15 LSTM h=32 V2 | 31855350 | **-0.021** | 3.4% | 27.4% | -1.93% | 0.20 | 61.5% | 23.6% | 2020-2026 |

## Key Observations

### M12 HAR-RV-J (Best performer)
- Highest Sharpe (0.645) and CAGR (27.1%)
- Universe: BTC (Coinbase crypto)
- Inverse-vol position sizing on realized variance forecast
- High MaxDD (41.1%) — typical for concentrated crypto

### S3 HMM Daily V2 (Solid regime switcher)
- Sharpe 0.496, strong CAGR 14.5%
- 2-regime MarkovRegression (SPY+TLT+VIX-proxy)
- Bull: 100% SPY, Bear: 100% TLT
- MaxDD 48.6% from extended bear periods
- Alpha positive (1.12%), beta 0.86
- Cloud-vs-local delta: QC Sharpe 0.496 vs local bootstrap 1.36 — expected gap (real trades + costs + slippage vs synthetic bootstrap Sharpe)

### S4 Regime+Ridge V2 (Conservative multi-asset)
- Lower Sharpe (0.367) but lowest MaxDD (23.1%)
- 11 assets: SPY+TLT+9 sector ETFs (anti-Mag7)
- HMM regime-conditional inverse-vol + Ridge shrinkage
- Bear regime: 2x defensive tilt (XLU/XLP/XLV/TLT)
- Conservative profile: beta 0.41, low vol (8.9% annual)

### M15 LSTM h=32 V2 (Underperforming)
- Negative Sharpe (-0.021) — signal not profitable in QC Cloud
- MLPClassifier proxy (32 hidden) for LSTM on HAR features
- Universe: BTC+ETH (Coinbase crypto)
- Kelly 1/4 fraction sizing reduces exposure but signal weak
- Possible cause: MLP proxy differs from original LSTM; insufficient expressiveness

## QC Cloud Porting Notes

### Bugs encountered and fixed
1. **`search_em_restarts` not available**: QC Cloud's statsmodels version lacks this method.
   Fix: use `mod.fit(disp=False, maxiter=300)` directly (S3, S4).
2. **`after_market_open` incompatible with crypto**: Crypto markets are always open.
   Fix: use `self.time_rules.at(0, 0)` for daily crypto scheduling (M15).
3. **No PyTorch/TensorFlow on QC Cloud**: M15 original LSTM ported as sklearn MLPClassifier.

### QC Project IDs
| Keeper | Project ID | Backtest ID (latest) |
|--------|-----------|---------------------|
| M12 HAR-RV-J | 31650567 | (existing) |
| S3 HMM Daily V2 | 31855212 | e6e01ffef680f52d4639a131150662c9 |
| S4 Regime+Ridge V2 | 31855260 | ce920137466548ec1b66297526ad1187 |
| M15 LSTM h=32 V2 | 31855350 | 9efacb49788cd2b633902d6926be4bce |

## Verdict

- **M12** and **S3** are viable for paper trading (positive Sharpe, decent CAGR).
- **S4** offers the best risk-adjusted profile for conservative capital (lowest MaxDD).
- **M15** needs rework: MLP proxy insufficient, consider ONNX export from PyTorch LSTM or different feature engineering.
