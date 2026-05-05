# ML/Trading Curriculum SOTA 2026

Anti-bias multi-asset training pipeline for quantitative trading research.

**Principle**: No single-asset, single-regime training. All stages use diversified data
from 7 asset classes (see anti-bias policy below).

**Current state**: Stage 1 cross-asset baselines complete (PR #724). Stage 0 SPY-only
checkpoints confirmed pathological — **asset selection > model selection** (SPY edge -6.08pp,
BTC +1.71pp, TLT +1.16pp, GLD +2.67pp).

---

## Anti-Bias Policy

**FORBIDDEN symbols** (individual FAANG+ tech): AAPL, MSFT, GOOG, AMZN, NVDA, TSLA, META

**Required**: broad indices, sector ETFs, bonds, commodities, international equities, crypto.

**Why**: Single-asset training on SPY (2015-2024 bull market) produces models that
memorize US equity momentum, not learn generalizable market signals.
SPY majority class (up days) = 54.59%. Best Transformer = 57.95% (+3.36pp only).

---

## Pipeline Stages

### Stage -1: Data Engineering (DONE)

Scripts for building multi-asset datasets.

| Script | Input | Output | Status |
|--------|-------|--------|--------|
| `stitch_crypto.py` | Bitstamp + Binance + yfinance | BTC/USD 1h continuous (2013-2024) | Done (~101K rows) |
| `build_panier_anti_bias.py` | yfinance (26 symbols) | Multi-asset panier CSVs | Done (26/26 OK) |
| `dezip_forex.py` | FXCM/Oanda zip archives | Forex bid/ask OHLCV | Done (16 files) |

Data locations:
- `datasets/yfinance/SPY_2015-01-01_2026-05-01.csv` — SPY daily baseline
- `datasets/crypto/BTC_USD_1h_stitched.csv` — BTC/USD hourly 2013-2024
- `datasets/panier/` — 26 symbols across 7 asset classes
- `datasets/forex/` — 10+ currency pairs, daily + hourly

### Stage 0: Baselines (DONE)

Establish majority-class and simple-model baselines on the anti-bias panier.

| Model | Target | Metric | Baseline (SPY) | Cross-Asset Best | Target (Panier) |
|-------|--------|--------|----------------|------------------|-----------------|
| Majority class | DirAcc | 54.59% (SPY) | 0.5873 (SPY pathological) | Compute per-symbol | Beat on >50% symbols |
| Random Forest | DirAcc | 50.86% (SPY) | 0.5200 (EEM) | Beat majority class on avg | |
| LSTM (h=64) | DirAcc | 54.25% (SPY) | 0.5467 (GLD, +2.67pp edge) | Beat majority + RF | |
| Transformer (d=256) | DirAcc | 57.95% (SPY) | 0.5533 (TLT, +1.16pp edge) | Beat majority + LSTM | |
| MTGNN | DirAcc | N/A | 0.5235 (SPY, +0.05pp only model beating) | Cross-asset graph | |
| DQN | Sharpe | 0.89 (in-sample, INVALID) | Walk-forward OOS pending (#703) | Out-of-sample Sharpe > 0 | |

Key requirement: **walk-forward validation** (5-fold, train=500, test=100, gap=10).
No in-sample Sharpe reporting. All DQN Sharpe values marked INVALID until #703 resolved.

**SPY pathology confirmed**: 58.73% majority class makes SPY the worst asset for ML.
BTC (+1.71pp), TLT (+1.16pp), GLD (+2.67pp) show genuine edges over their baselines.

### Stage 1: Multi-Asset Training (IN PROGRESS)

Cross-asset walk-forward baselines on 7 assets (SPY, BTC-USD, GLD, TLT, EFA, EEM, DBC).

**Completed (PR #724)**: Walk-forward OOS evaluation across all architectures.
- Transformer best on BTC (+1.71pp) and TLT (+1.16pp)
- LSTM best on GLD (+2.67pp, best single-asset edge)
- SPY confirmed pathological (-6.08pp vs majority)
- MTGNN only model beating SPY baseline (+0.05pp)

**Next**: Panier 19-asset expansion (Stage 3a), cross-asset features, regime-conditional models.

### Stage 2: Feature Engineering

Advanced features beyond basic OHLCV.

- 13 technical indicators (RSI, MACD, Bollinger, ATR, OBV, etc.)
- Cross-asset features (bond-equity ratio, commodity momentum, FX carry)
- Volatility regime features (VIX level, term structure)
- Macro features (rate changes, inflation surprises)

### Stage 3: Ensemble Methods

Combine multiple model types.

- LSTM + Transformer stacking
- RL policy gradient with supervised pre-training
- Regime-conditional ensemble (different models per regime)
- Uncertainty-weighted prediction averaging

### Stage 4: Walk-Forward Optimization

Proper out-of-sample validation.

- Rolling window backtests (2-year train, 6-month test)
- Parameter stability analysis across windows
- Regime transition robustness
- Slippage and transaction cost modeling

### Stage 5: Risk Management

Position sizing and portfolio construction.

- Kelly criterion position sizing
- Maximum drawdown constraints
- Correlation-based allocation
- Tail risk hedging signals

### Stage 6: Live Paper Trading

Deploy to QuantConnect paper trading.

- Real-time signal generation
- Order execution quality analysis
- Latency and fill tracking
- Compare paper vs backtest performance

### Stage 7: Production Hardening

- Monitoring and alerting
- Model drift detection
- Automatic retraining pipeline
- Failover and circuit breakers

### Stage 8: Curriculum Review

- Aggregate results across all stages
- Pedagogical notebook production
- Student exercises and assignments
- SOTA benchmark comparison

---

## Checkpoint Registry

See [REGISTRY.md](REGISTRY.md) for complete checkpoint catalog.

Current: 20 SPY-only checkpoints (all biased). 7 cross-asset walk-forward baselines (PR #724).
Target: 50+ checkpoints across panier.

---

## Quality Gates

Each stage must pass before proceeding:

| Gate | Criteria |
|------|----------|
| Data quality | No NaN in close prices, <1% gaps, overlap validation <0.5% diff |
| Baseline | Model must beat majority class on >50% of panier symbols out-of-sample |
| Multi-asset | Sharpe > 0 on walk-forward, not just in-sample |
| Ensemble | Must improve over best single model by >5% Sharpe |
| Walk-forward | No parameter regime-fitting (stable across 3+ windows) |
| Risk | Max DD < 20% in worst walk-forward window |
| Paper trading | Track record > 30 days, <5% deviation from backtest |
