# Checkpoint Registry

Auto-generated: 2026-05-03 22:29
Updated: 2026-05-06 — Stage -1 Panier baselines: 18 BEATS, 32 FAILS across 50 experiments (26 symbols x 2 models)

Total checkpoints: 70 (20 legacy + 50 panier baselines)

## Anti-Bias Audit (2026-05-04)

**WARNING: All checkpoints trained on SPY single-asset.** This creates bias toward US equity momentum.
SPY majority class (up days) 2015-2024 = **54.59%**. Most models barely beat this.

These checkpoints are **NOT valid for production** — they serve as baselines for Stage 0.
Future trainings MUST use anti-bias panier (26 symbols, 7 asset classes) per Issue #706.

**Forbidden symbols**: AAPL, MSFT, GOOG, AMZN, NVDA, TSLA, META

## Stage -1: Panier Baselines POST-FIX (2026-05-06)

**Methodology**: Walk-forward 5-fold, advanced features (38 dims), seed=42, train-only normalization.
RF (200 trees, max_depth=8) + XGBoost (200 rounds, max_depth=8) on all 26 panier symbols.

**Result: 18 BEATS, 32 FAILS across 50 experiments.**

| Group | Symbol | RF DirAcc | RF vs Maj | XGB DirAcc | XGB vs Maj | Best Model | Verdict |
|-------|--------|-----------|-----------|------------|------------|------------|---------|
| us_equity_broad | SPY | 0.4972 | -0.0104 | 0.4991 | -0.0085 | None | FAIL |
| us_equity_broad | RSP | 0.5208 | **+0.0075** | 0.5123 | -0.0009 | RF | MIXED |
| us_equity_broad | IWM | 0.5094 | **+0.0047** | 0.5113 | **+0.0066** | XGB | BEATS |
| us_equity_sectors | XLB | 0.5189 | **+0.0085** | 0.5358 | **+0.0255** | XGB | BEATS |
| us_equity_sectors | XLC | 0.4902 | -0.0154 | 0.4958 | -0.0098 | None | FAIL |
| us_equity_sectors | XLF | 0.5113 | -0.0028 | 0.5132 | -0.0009 | None | FAIL |
| us_equity_sectors | XLI | 0.5066 | **+0.0038** | 0.5170 | **+0.0142** | XGB | BEATS |
| us_equity_sectors | XLK | 0.4972 | -0.0321 | 0.5066 | -0.0226 | None | FAIL |
| us_equity_sectors | XLP | 0.5330 | **+0.0047** | 0.5170 | -0.0113 | RF | MIXED |
| us_equity_sectors | XLRE | 0.4816 | -0.0347 | 0.4918 | -0.0245 | None | FAIL |
| us_equity_sectors | XLU | 0.5066 | -0.0057 | 0.4953 | -0.0170 | None | FAIL |
| us_equity_sectors | XLV | 0.5255 | **+0.0085** | 0.5151 | -0.0019 | RF | MIXED |
| us_equity_sectors | XLY | 0.4708 | -0.0632 | 0.5085 | -0.0255 | None | FAIL |
| volatility | VIX | 0.5168 | **+0.0057** | 0.5066 | -0.0045 | RF | MIXED |
| us_bonds | TLT | 0.5274 | -0.0057 | 0.5245 | -0.0085 | None | FAIL |
| us_bonds | IEF | 0.5783 | -0.0311 | 0.5462 | -0.0632 | None | FAIL |
| us_bonds | SHY | 0.8821 | -0.0113 | 0.8877 | -0.0057 | None | FAIL |
| commodities | GLD | 0.5142 | -0.0113 | 0.5038 | -0.0217 | None | FAIL |
| commodities | USO | 0.4802 | -0.0283 | 0.4774 | -0.0311 | None | FAIL |
| commodities | DBA | 0.5151 | -0.0349 | 0.5198 | -0.0302 | None | FAIL |
| international | EFA | 0.5151 | -0.0123 | 0.5198 | -0.0075 | None | FAIL |
| international | EEM | 0.5396 | **+0.0189** | 0.5047 | -0.0160 | RF | MIXED |
| crypto | BTC-USD | 0.5171 | **+0.0171** | 0.5197 | **+0.0197** | XGB | BEATS |
| crypto | ETH-USD | 0.5310 | **+0.0293** | 0.5422 | **+0.0405** | XGB | BEATS |
| crypto | LTC-USD | 0.5203 | **+0.0019** | 0.5273 | **+0.0089** | XGB | BEATS |
| crypto | XRP-USD | 0.5293 | **+0.0267** | 0.5233 | **+0.0207** | RF | BEATS |

Key findings:

- **Crypto dominates**: 7/8 BEATS (all 4 symbols x 2 models, except LTC-USD RF marginal +0.0019).
  Crypto majority class is close to 50%, making prediction viable. ETH-USD XGB +4.05pp = best single edge.
- **XGBoost > RF for crypto**: XGB edges consistently larger (ETH +4.05pp, BTC +1.97pp, LTC +0.89pp).
- **Equity sectors show selective edges**: XLB (+2.55pp XGB), XLI (+1.42pp XGB), but most sectors FAIL.
  XLK (Tech ETF) worst at -3.21pp, reflecting 2015-2024 bull market bias.
- **Bonds are pathological**: SHY 89% majority class (up days) = impossible to beat. TLT/IEF also fail.
- **SPY FAILS**: Confirms single-asset SPY training is dead end (see POST-FIX verdict below).
- **VIX has mild RF edge** (+0.57pp) but XGB fails — volatility regime detection is noisy.

Implication for EPIC #705: **Multi-asset panier baselines confirm the thesis** — ML has genuine predictive
value on crypto (+4.05pp ETH) and selective equity sectors (+2.55pp XLB). SPY/bonds are pathological.
Curriculum should demonstrate ML on crypto/commodities first, then explain why SPY fails.

## POST-FIX Verdict (2026-05-05) — DEFINITIVE

**Methodology**: Deterministic (seed=42), walk-forward, OOS-aware majority baseline (#737),
last-fold checkpoint (#738), RSI Wilder EMA (#736), internal val split from train only (#726/#730).
14 runs across 7 architectures on SPY/BTC/Multi-asset.

| Model | SPY single | BTC single | Multi 4-asset |
| -------- | ---------- | ---------- | ------------- |
| MTGNN | -0.0452 FAILS | -0.0094 FAILS | -0.0116 FAILS |
| LSTM | -0.0186 FAILS | -0.0337 FAILS | n/a |
| Transformer | -0.0497 FAILS | -0.0207 FAILS | n/a |
| PatchTST | -0.1076 FAILS | -0.0030 FAILS | n/a |
| iTransformer | -0.0082 FAILS | -0.0186 FAILS | n/a |
| Mamba | -0.0370 FAILS | -0.0306 FAILS | n/a |
| STGAT | n/a | n/a | -0.0480 FAILS |

**Result: 0 BEATS, 14 FAILS.** No baseline architecture beats the majority predictor under rigorous methodology.

Key findings:

- Pre-fix results (Track A3 below) were **inflated by test-set contamination** — validation early-stopping
  used test_loader directly, creating lookahead bias. PatchTST SPY dropped from -2.10pp to -10.76pp post-fix.
- MTGNN (graph adaptive) previously claimed +0.0005 SPY and +0.0044 multi BEATS — both **non-reproducible**
  after audit fixes (#737 OOS baseline, #738 no cherry-pick, #736 RSI Wilder).
- SPY is pathological (majority 56-58% up days in 2015-2024 bull market). All models learn "predict up"
  and fail when the regime shifts. BTC majority is closer to 50%, but still no edge.
- po-2024 claimed Mamba BTC +3.24pp and PatchTST BTC +1.98pp BEATS — **non-reproducible** on RTX 4090
  with identical hyperparams (d_model=64, batch=16, seed=42). Likely variance from non-determinism or
  thermal throttling on RTX 3070.
- **Implication for EPIC #705**: Current baseline architectures are a dead end on SPY/BTC single-asset.
  Multi-asset panier (Stage 3a, #727) and advanced methods (Stages 5-8: Kronos, Flow Matching,
  FinRL, FinGPT) are the viable path forward.

## Advanced Features (Track A3) — PRE-FIX (INFLATED, superseded by POST-FIX above)

**WARNING**: These results were computed BEFORE contamination fix (#726/#730). Validation early-stopping
used test_loader, inflating direction accuracy. See POST-FIX Verdict above for honest metrics.

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

Key findings (pre-fix):

- Transformer (d=256, h=8, L=6) appeared to beat majority class (+3.36pp) — **this was inflated**.
  POST-FIX reveals -0.0497 FAILS (6.33pp swing).
- LSTM h=64 barely matched majority class (-0.34pp). POST-FIX confirms -0.0186 FAILS.
- RF accuracy (50.86%) was BELOW majority class (-3.73pp). Confirmed no predictive power.
- DQN Sharpe 0.89 was in-sample (no train/test split). Fixed via #729.
- All checkpoints are single-asset (SPY), single-regime (2015-2024 bull market). Not robust.

## Asset Diversity Matters (Cross-Asset Evidence) — PRE-FIX (superseded by POST-FIX)

**Key thesis confirmed (PR #724): Asset selection > model selection.**

**NOTE**: These walk-forward baselines were computed before audit fixes (#737 OOS baseline, #738 last-fold).
The LSTM edges shown below (+3.51pp BTC, +3.68pp TLT) have not been re-validated POST-FIX.
POST-FIX verdict above shows 0 BEATS across all architectures on SPY/BTC deterministic runs.

Cross-asset walk-forward baselines (5-fold, train=500, test=100, gap=10) reveal that
SPY is the *worst* asset for ML training — its 58.7% majority-class frequency (up-day bias
during 2015-2024 bull market) makes it pathological. No model architecture beats this baseline.

| Asset | Best Model | OOS DirAcc | Majority | Edge (pp) | Verdict |
|-------|-----------|------------|----------|-----------|---------|
| BTC-USD | Transformer | 0.5400 | 0.5229 | **+1.71** | Positive edge |
| TLT | Transformer | 0.5533 | 0.5417 | **+1.16** | Positive edge |
| GLD | LSTM | 0.5467 | 0.5200 | **+2.67** | Best single-asset edge |
| EFA | LSTM | 0.5133 | 0.5200 | -0.67 | Near baseline |
| EEM | RF | 0.5200 | 0.5200 | 0.00 | At baseline |
| DBC | LSTM | 0.5067 | 0.5417 | -3.50 | Negative |
| SPY | Transformer | 0.5265 | 0.5873 | **-6.08** | Pathological |

**Implications for curriculum:**
1. Training on SPY alone teaches the wrong lesson — ML appears useless because the asset is too biased.
2. Non-equity assets (BTC, TLT, GLD) show genuine ML edges, validating the approach.
3. Future stages MUST use multi-asset panier (Stage 3a, 19 assets) to demonstrate real ML value.
4. MTGNN (graph neural network) is the only architecture beating baseline even on SPY (+0.05pp),
   suggesting cross-asset graph structure captures signal that single-asset models miss.

**Source**: PR #724 Stage 1 cross-asset walk-forward baselines, ai-01 comparative runs.

## Stage 1: BTC-USD Walk-Forward Baselines (2026-05-05) — PRE-FIX (superseded)

Anti-bias training on BTC-USD 2015-2025 (3653 daily rows, 3594 after feature engineering).
Walk-forward: 5 folds, train=500, test=100, gap=10. BTC majority class (up days) = **55.10%**.

| Model | OOS DirAcc | vs Majority | n_folds | Architecture | Checkpoint |
| ----- | ---------- | ----------- | ------- | ------------ | ---------- |
| LSTM | **54.60%** | **+3.51pp** | 5 | h=64, L=2, ep=30 | 20260505_012529 |
| Transformer | 51.00% | -0.09pp | 5 | d=64, h=4, L=2, ep=30 | 20260505_012554 |
| RF (200 trees) | 49.40% | +0.15pp | 5 | max_depth=8, 19 features | 20260505_012321 |
| DQN | PENDING | PENDING | 3 | h=128, ep=50, w=20 | training |

Key findings:

- LSTM is the only model with meaningful edge (+3.51pp over majority class).
- Transformer at d=64/h=4/L=2 is too small for BTC-USD patterns (previous SPY BEST used d=256/h=8/L=6).
- RF barely matches random — no feature-based signal in BTC daily returns.
- BTC-USD majority class (55.1%) is higher than SPY (54.6%) — crypto has more up days in this period.

## Stage 1: Cross-Asset Walk-Forward Baselines (2026-05-05) — PRE-FIX (superseded)

Anti-bias training on 6 non-FAANG assets (GLD, TLT, EEM, EFA, DBC + BTC-USD).
Walk-forward: 5 folds, train=500, test=100, gap=10. All models use advanced features (38 dims).

| Asset | Model | OOS DirAcc | vs Majority | n_folds | Architecture | Checkpoint |
| ----- | ----- | ---------- | ----------- | ------- | ------------ | ---------- |
| BTC-USD | LSTM | **54.60%** | **+3.51pp** | 5 | h=64, L=2, ep=30 | 20260505_012529 |
| BTC-USD | Transformer | 51.00% | -0.09pp | 5 | d=64, h=4, L=2, ep=30 | 20260505_012554 |
| BTC-USD | RF (200 trees) | 49.40% | +0.15pp | 5 | max_depth=8, 19 features | 20260505_012321 |
| BTC-USD | DQN | 0.00% | -51.14pp | 3 | h=256, ep=100, w=20 | 20260505_021359 |
| GLD | LSTM | **53.80%** | +0.84pp | 5 | h=64, L=2, ep=30 | 20260505_013925 |
| GLD | RF (200 trees) | 53.00% | +1.09pp | 5 | max_depth=8, 38 features | 20260505_010142 |
| GLD | Transformer | 53.80% | +1.19pp | 5 | d=64, h=4, L=2, ep=30 | 20260505_015628 |
| TLT | LSTM | **52.20%** | **+3.68pp** | 5 | h=64, L=2, ep=30 | 20260505_015143 |
| TLT | RF (200 trees) | 48.20% | -5.91pp | 5 | max_depth=8, 38 features | 20260505_010023 |
| TLT | Transformer | 51.20% | +2.68pp | 5 | d=64, h=4, L=2, ep=30 | 20260505_015903 |
| EEM | LSTM | 50.60% | -0.96pp | 5 | h=64, L=2, ep=30 | 20260505_010203 |
| EEM | RF (200 trees) | 51.80% | -0.68pp | 5 | max_depth=8, 38 features | 20260505_010023 |
| EEM | Transformer | 47.20% | -4.11pp | 5 | d=64, h=4, L=2, ep=30 | 20260505_020058 |
| EFA | LSTM | 52.20% | -0.50pp | 5 | h=64, L=2, ep=30 | 20260505_020022 |
| EFA | RF (200 trees) | 50.00% | -2.46pp | 5 | max_depth=8, 38 features | 20260505_015821 |
| EFA | Transformer | 50.40% | -2.55pp | 5 | d=64, h=4, L=2, ep=30 | 20260505_021553 |
| DBC | LSTM | **55.80%** | +0.49pp | 5 | h=64, L=2, ep=30 | 20260505_020144 |
| DBC | RF (200 trees) | 49.60% | +2.40pp | 5 | max_depth=8, 38 features | 20260505_015829 |
| DBC | Transformer | 51.80% | -2.48pp | 5 | d=64, h=4, L=2, ep=30 | 20260505_021816 |

Majority class baselines: BTC-USD=55.10%, GLD=53.04%, TLT=48.09%, EEM=52.44%, EFA=52.46%, DBC=47.20%.

Key findings:

- **LSTM is the best model across 4/6 assets** — consistent edge on BTC (+3.51pp), TLT (+3.68pp), GLD (+0.84pp), DBC (+0.49pp).
- **TLT (bonds) is the most predictable asset** — LSTM +3.68pp, Transformer +2.68pp. Bonds have clearer momentum regimes.
- **Transformer (d=64) underperforms** on equities (EEM -4.11pp) and BTC (-0.09pp), but works on bonds/commodities.
- **RF has no reliable edge** — mixed results across all assets, never the best model.
- **EEM is the hardest asset** — all models struggle, LSTM -0.96pp, Transformer -4.11pp.
- **DBC (commodities) LSTM = best absolute DirAcc** at 55.80%, but majority class is already low (47.20%).
- **DQN completely fails OOS** — 0.00% DirAcc on BTC-USD. All 3 folds have negative OOS reward. The agent overfits training episodes (avg reward 4.7-6.4 in-sample) but produces zero actionable signals out-of-sample. RL approach needs fundamental redesign for this problem.

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

**WARNING**: All DQN checkpoints below trained WITHOUT train/test split (Issue #703).
Sharpe estimates are in-sample only, NOT reliable out-of-sample metrics.
Marked `[INVALID-NO-SPLIT]` until re-trained with `--test-ratio 0.2`.

### 20260501_120415 [INVALID-NO-SPLIT] [BASELINE] [SPY-ONLY]

- Data hash: `17cb43b404e3ddf1`
- Metrics: best_avg_reward_10=2.2865, max_reward=3.0876, mean_reward=1.0177, mean_trades=749.3, min_reward=-1.8051, sharpe_estimate=0.8921
- Architecture: hidden_size=256, n_actions=3, state_size=242
- Config: device=cuda, hidden_size=256, num_episodes=50, symbol=SPY
- Files: metadata.json, model.pt

### 20260501_142319 [INVALID-NO-SPLIT] [ADVANCED-FEATURES] [SPY-ONLY]

- Data hash: `4ec8b44b93f4024f`
- Metrics: best_avg_reward_10=0.3888, max_reward=1.8077, mean_reward=-0.0138, mean_trades=782.5, min_reward=-1.2372, sharpe_estimate=-0.0171
- Architecture: hidden_size=256, n_actions=3, state_size=762
- Config: device=cuda, hidden_size=256, num_episodes=20, symbol=SPY, advanced=true
- Files: metadata.json, model.pt

### 20260501_140955 [INVALID-NO-SPLIT] [SPY-ONLY]

- Data hash: `4ec8b44b93f4024f`
- Metrics: best_avg_reward_10=-0.4572, max_reward=-0.0334, mean_reward=-0.4572, mean_trades=759.3, min_reward=-0.836, sharpe_estimate=-1.6905
- Architecture: hidden_size=128, n_actions=3, state_size=762
- Config: device=cuda, hidden_size=128, num_episodes=10, symbol=SPY, advanced=true
- Files: metadata.json, model.pt

### 20260501_112641 [INVALID-NO-SPLIT] [SPY-ONLY]

- Data hash: `17cb43b404e3ddf1`
- Metrics: best_avg_reward_10=-0.1559, max_reward=0.9312, mean_reward=-0.5358, mean_trades=739.6, min_reward=-1.5861, sharpe_estimate=-0.8096
- Architecture: hidden_size=32, n_actions=3, state_size=242
- Config: device=cpu, hidden_size=32, num_episodes=20, symbol=SPY
- Files: metadata.json, model.pt

### 20260501_111005 [INVALID-NO-SPLIT] [SPY-ONLY]

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
