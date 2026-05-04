# Checkpoint Registry

Auto-generated: 2026-05-03 22:29
Updated: 2026-05-04 — Track B: walk-forward OOS evaluation columns

Total checkpoints: 20

## Anti-Bias Audit (2026-05-04)

**WARNING: All checkpoints trained on SPY single-asset.** This creates bias toward US equity momentum.
SPY majority class (up days) 2015-2024 = **54.59%**. Most models barely beat this.

These checkpoints are **NOT valid for production** — they serve as baselines for Stage 0.
Future trainings MUST use anti-bias panier (26 symbols, 7 asset classes) per Issue #706.

**Forbidden symbols**: AAPL, MSFT, GOOG, AMZN, NVDA, TSLA, META

## Advanced Features (Track A3)

Comparison of baseline vs advanced-feature training on SPY 2015-2024.
Majority class baseline: **54.59%** (freq of up days).

| Model | Baseline DirAcc | Advanced DirAcc | vs Majority | Delta | Features |
| ------- | --------------- | --------------- | ----------- | ----- | -------- |
| Transformer (50ep) | 48.72% | **57.95%** | +3.36pp | +9.23pp | 38 (all 13 indicators) |
| Transformer (30ep prod) | 48.72% | **56.43%** | +1.84pp | +7.71pp | 38 (all 13 indicators) |
| LSTM (h=64 prod) | 51.49% | **54.25%** | -0.34pp | +2.76pp | 38 (all 13 indicators) |
| LSTM (h=256) | 51.49% | 50.98% | -3.61pp | -0.51pp | 38 (all 13 indicators) |
| Classification (RF) | 49.66% | **50.86%** | -3.73pp | +1.20pp | 38 (all 13 indicators) |
| DQN | Sharpe 0.89 | Sharpe -0.02 | N/A (in-sample) | -0.91 | 38 (all 13 indicators) |

Key findings:

- Transformer (d=256, h=8, L=6) is the only model consistently beating majority class (+3.36pp).
  However 3.36pp edge is marginal for 3.2M parameters — likely overfitting to SPY momentum regime.
- LSTM h=64 barely matches majority class (-0.34pp). Not a real edge.
- RF accuracy (50.86%) is BELOW majority class (-3.73pp). No predictive power.
- DQN Sharpe 0.89 is in-sample (no train/test split). Must be re-evaluated with proper time-series split (Issue #703).
- All checkpoints are single-asset (SPY), single-regime (2015-2024 bull market). Not robust.

## Walk-Forward OOS Evaluation (Track B)

Evaluation harness: `scripts/eval_existing_checkpoints.py`
Method: 5-fold walk-forward (3yr train, 1yr test, 5-day gap), per-regime, transaction costs.

| Model | Checkpoint | OOS DirAcc | vs Majority | Regime Avg DirAcc | Gross Sharpe | Net Sharpe | Cost Drag (bps) |
| ----- | ---------- | ---------- | ----------- | ----------------- | ------------ | ---------- | --------------- |
| Transformer | 20260501_134056 (BEST) | PENDING | PENDING | PENDING | PENDING | PENDING | PENDING |
| Transformer | 20260503_222904 (PROD) | PENDING | PENDING | PENDING | PENDING | PENDING | PENDING |
| LSTM | 20260503_221944 (PROD) | PENDING | PENDING | PENDING | PENDING | PENDING | PENDING |
| LSTM | 20260501_133929 | PENDING | PENDING | PENDING | PENDING | PENDING | PENDING |
| RF | 20260501_133837 | PENDING | PENDING | PENDING | PENDING | PENDING | PENDING |
| DQN | 20260501_120415 | PENDING | PENDING | PENDING | PENDING | PENDING | PENDING |

**Status**: Evaluation harness ready (27/27 tests pass). OOS metrics to be populated after GPU evaluation run.
SPY majority class baseline = **54.59%**. Values will be populated by `python eval_existing_checkpoints.py --all`.

## Data Sources

| Dataset | Path | Coverage | Status |
| ------- | ---- | -------- | ------ |
| SPY daily | `datasets/yfinance/SPY_2015-01-01_2026-05-01.csv` | 2015-2026 | Used by all checkpoints |
| BTC/USD 1h stitched | `datasets/crypto/BTC_USD_1h_stitched.csv` | 2011-2024 | Available for Stage 1+ |
| Panier anti-bias | `datasets/panier/` (26 symbols) | 2015-2026 | Available for Stage 0+ |
| Forex FXCM/Oanda | `datasets/forex/` (10 pairs) | 2002-2025 | Available for Stage 1+ |

## dqn

Checkpoints: 5

### 20260501_120415 [OK] [BASELINE] [SPY-ONLY]

- Data hash: `17cb43b404e3ddf1`
- Metrics: best_avg_reward_10=2.2865, max_reward=3.0876, mean_reward=1.0177, mean_trades=749.3, min_reward=-1.8051, sharpe_estimate=0.8921
- Architecture: hidden_size=256, n_actions=3, state_size=242
- Config: device=cuda, hidden_size=256, num_episodes=50, symbol=SPY
- Files: metadata.json, model.pt

### 20260501_142319 [OK] [ADVANCED-FEATURES] [SPY-ONLY]

- Data hash: `4ec8b44b93f4024f`
- Metrics: best_avg_reward_10=0.3888, max_reward=1.8077, mean_reward=-0.0138, mean_trades=782.5, min_reward=-1.2372, sharpe_estimate=-0.0171
- Architecture: hidden_size=256, n_actions=3, state_size=762
- Config: device=cuda, hidden_size=256, num_episodes=20, symbol=SPY, advanced=true
- Files: metadata.json, model.pt

### 20260501_140955 [OK] [SPY-ONLY]

- Data hash: `4ec8b44b93f4024f`
- Metrics: best_avg_reward_10=-0.4572, max_reward=-0.0334, mean_reward=-0.4572, mean_trades=759.3, min_reward=-0.836, sharpe_estimate=-1.6905
- Architecture: hidden_size=128, n_actions=3, state_size=762
- Config: device=cuda, hidden_size=128, num_episodes=10, symbol=SPY, advanced=true
- Files: metadata.json, model.pt

### 20260501_112641 [OK] [SPY-ONLY]

- Data hash: `17cb43b404e3ddf1`
- Metrics: best_avg_reward_10=-0.1559, max_reward=0.9312, mean_reward=-0.5358, mean_trades=739.6, min_reward=-1.5861, sharpe_estimate=-0.8096
- Architecture: hidden_size=32, n_actions=3, state_size=242
- Config: device=cpu, hidden_size=32, num_episodes=20, symbol=SPY
- Files: metadata.json, model.pt

### 20260501_111005 [OK] [SPY-ONLY]

- Data hash: `synthetic-dryrun`
- Metrics: best_avg_reward_10=-0.0017, max_reward=0.1665, mean_reward=-0.0017, mean_trades=44.1, min_reward=-0.2395, sharpe_estimate=-0.0134
- Architecture: hidden_size=256, n_actions=3, state_size=242
- Config: device=cpu, hidden_size=256, num_episodes=10, symbol=SPY
- Files: metadata.json, model.pt

## lstm

Checkpoints: 5

### 20260503_221944 [OK] [SPY-ONLY] [ADVANCED-FEATURES] [PRODUCTION]

- Data hash: `4ec8b44b93f4024f`
- Metrics: direction_accuracy=0.5425, direction_accuracy_significant=0.5506, epochs_trained=50, mae=0.005944, mse=6.2e-05
- Architecture: hidden_size=64, input_size=38, num_layers=2
- Config: device=cuda, epochs=50, hidden_size=64, num_layers=2, symbol=SPY, advanced=true
- Files: metadata.json, model.pt

### 20260501_133929 [OK] [SPY-ONLY] [ADVANCED-FEATURES]

- Data hash: `4ec8b44b93f4024f`
- Metrics: direction_accuracy=0.5098, direction_accuracy_significant=0.503, epochs_trained=50, mae=0.005954, mse=6.2e-05
- Architecture: hidden_size=256, input_size=38, num_layers=3
- Config: device=cuda, epochs=50, hidden_size=256, num_layers=3, symbol=SPY, advanced=true
- Files: metadata.json, model.pt

### 20260501_113924 [OK] [SPY-ONLY]

- Data hash: `17cb43b404e3ddf1`
- Metrics: best_val_loss=0.000144, direction_accuracy=0.4848, direction_accuracy_significant=0.4957, epochs_trained=30, mae=0.008986, mse=0.000147
- Architecture: hidden_size=256, input_size=15, num_layers=3
- Config: device=cuda, epochs=30, hidden_size=256, num_layers=3, symbol=SPY
- Files: metadata.json, model.pt

### 20260501_111103 [OK] [SPY-ONLY]

- Data hash: `17cb43b404e3ddf1`
- Metrics: best_val_loss=0.00015, direction_accuracy=0.5149, direction_accuracy_significant=0.5014, epochs_trained=5, mae=0.009063, mse=0.000153
- Architecture: hidden_size=64, input_size=15, num_layers=1
- Config: device=cpu, epochs=5, hidden_size=64, num_layers=1, symbol=SPY
- Files: metadata.json, model.pt

### 20260501_110937 [OK] [SPY-ONLY]

- Data hash: `synthetic-dryrun`
- Metrics: best_val_loss=0.000261, direction_accuracy=0.5, direction_accuracy_significant=0.5139, epochs_trained=2, mae=0.013328, mse=0.000265
- Architecture: hidden_size=128, input_size=15, num_layers=2
- Config: device=cpu, epochs=2, hidden_size=128, num_layers=2, symbol=SPY
- Files: metadata.json, model.pt

## rf

Checkpoints: 5

### 20260501_133837 [OK] [SPY-ONLY] [ADVANCED-FEATURES]

- Data hash: `4ec8b44b93f4024f`
- Metrics: accuracy=0.5086, f1=0.5031, precision=0.5077, recall=0.5086, test_samples=464, train_samples=1852
- Config: model_type=rf, n_estimators=500, max_depth=10, symbol=SPY, advanced=true
- Files: metadata.json, model.joblib

### 20260501_113900 [OK] [SPY-ONLY]

- Data hash: `17cb43b404e3ddf1`
- Metrics: accuracy=0.4966, f1=0.4958, precision=0.505, recall=0.4966, test_samples=441, train_samples=1764
- Config: symbol=SPY
- Files: metadata.json, model.joblib

### 20260501_111041 [OK] [SPY-ONLY]

- Data hash: `17cb43b404e3ddf1`
- Metrics: accuracy=0.4966, f1=0.4958, precision=0.505, recall=0.4966, test_samples=441, train_samples=1764
- Config: symbol=SPY
- Files: metadata.json, model.joblib

### 20260501_111026 [OK] [SPY-ONLY]

- Data hash: `synthetic-dryrun`
- Metrics: accuracy=0.3933, f1=0.3951, precision=0.4033, recall=0.3933, test_samples=89, train_samples=352
- Config: symbol=SPY
- Files: metadata.json, model.joblib

### 20260501_110930 [OK] [SPY-ONLY]

- Data hash: `synthetic-dryrun`
- Metrics: accuracy=0.3933, f1=0.3951, precision=0.4033, recall=0.3933, test_samples=89, train_samples=352
- Config: symbol=SPY
- Files: metadata.json, model.joblib

## transformer

Checkpoints: 5

### 20260501_134056 [OK] [SPY-ONLY] [ADVANCED-FEATURES] [BEST]

- Data hash: `4ec8b44b93f4024f`
- Metrics: direction_accuracy=0.5795, direction_accuracy_significant=0.5804, epochs_trained=50, mae=0.005895, mse=6.1e-05, total_params=3189633
- Architecture: d_model=256, input_size=38, nhead=8, num_layers=6
- Config: device=cuda, d_model=256, epochs=50, nhead=8, num_layers=6, symbol=SPY, advanced=true
- Files: metadata.json, model.pt

### 20260503_222904 [OK] [SPY-ONLY] [ADVANCED-FEATURES] [PRODUCTION]

- Data hash: `4ec8b44b93f4024f`
- Metrics: direction_accuracy=0.5643, direction_accuracy_significant=0.5595, epochs_trained=30, mae=0.005932, mse=6.1e-05, total_params=3189633
- Architecture: d_model=256, input_size=38, nhead=8, num_layers=6
- Config: device=cuda, d_model=256, epochs=30, nhead=8, num_layers=6, symbol=SPY, advanced=true
- Files: metadata.json, model.pt

### 20260501_113923 [OK] [SPY-ONLY]

- Data hash: `17cb43b404e3ddf1`
- Metrics: best_val_loss=7.3e-05, direction_accuracy=0.4872, direction_accuracy_significant=0.5071, epochs_trained=30, mae=0.009084, mse=0.000149
- Architecture: d_model=128, input_size=17, nhead=8, num_layers=4
- Config: d_model=128, device=cuda, epochs=30, nhead=8, num_layers=4, symbol=SPY
- Files: metadata.json, model.pt

### 20260501_111130 [OK] [SPY-ONLY]

- Data hash: `17cb43b404e3ddf1`
- Metrics: best_val_loss=9.9e-05, direction_accuracy=0.4714, direction_accuracy_significant=0.468, epochs_trained=5, mae=0.011033, mse=0.0002
- Architecture: d_model=64, input_size=17, nhead=4, num_layers=2
- Config: d_model=64, device=cpu, epochs=5, nhead=4, num_layers=2, symbol=SPY
- Files: metadata.json, model.pt

### 20260501_110947 [OK] [SPY-ONLY]

- Data hash: `synthetic-dryrun`
- Metrics: best_val_loss=0.000252, direction_accuracy=0.4762, direction_accuracy_significant=0.4722, epochs_trained=2, mae=0.018693, mse=0.000542
- Architecture: d_model=128, input_size=17, nhead=4, num_layers=4
- Config: d_model=128, device=cpu, epochs=2, nhead=4, num_layers=4, symbol=SPY
- Files: metadata.json, model.pt
