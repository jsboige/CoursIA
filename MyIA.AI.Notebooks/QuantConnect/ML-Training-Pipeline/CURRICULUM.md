# ML/Trading Curriculum SOTA 2026

Anti-bias multi-asset training pipeline for quantitative trading research.

**Principle**: No single-asset, single-regime training. All stages use diversified data
from 7 asset classes (see anti-bias policy below).

**Current state**: Stage -1 complete (data engineering). Baseline checkpoints (Stage 0)
trained on SPY only are **NOT valid for production**.

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
| `stitch_crypto.py` | Bitstamp + Binance + yfinance | BTC/USD 1h continuous (2012-2024) | Done (107K rows) |
| `build_panier_anti_bias.py` | yfinance (26 symbols) | Multi-asset panier CSVs | Done (26/26 OK) |
| `dezip_forex.py` | FXCM/Oanda zip archives | Forex bid/ask OHLCV | Done (16 files) |

Data locations:
- `datasets/yfinance/SPY_2015-01-01_2026-05-01.csv` — SPY daily baseline
- `datasets/crypto/BTC_USD_1h_stitched.csv` — BTC/USD hourly 2011-2026
- `datasets/panier/` — 26 symbols across 7 asset classes
- `datasets/forex/` — 10+ currency pairs, daily + hourly

### Stage 0: Baselines (IN PROGRESS)

Establish majority-class and simple-model baselines on the anti-bias panier.

| Model | Target | Metric | Baseline (SPY) | Target (Panier) |
|-------|--------|--------|----------------|-----------------|
| Majority class | DirAcc | 54.59% (SPY up days) | Compute per-symbol | Beat on >50% symbols |
| Random Forest | DirAcc | 50.86% (SPY) | Beat majority class on avg | |
| LSTM (h=64) | DirAcc | 54.25% (SPY) | Beat majority + RF | |
| Transformer (d=256) | DirAcc | 57.95% (SPY) | Beat majority + LSTM consistently | |
| DQN | Sharpe | 0.89 (in-sample) | Out-of-sample Sharpe > 0 | |

Key requirement: **walk-forward validation** (train 2015-2019, val 2019-2021, test 2021-2024).
No in-sample Sharpe reporting.

### Stage 1: Multi-Asset Training

Train on panier (26 symbols) instead of single asset.

- Cross-asset features (relative momentum, sector rotation signals)
- Regime-conditional models (bull/bear/sideways across asset classes)
- Walk-forward across 3 market regimes (COVID crash, 2022 rate hike, 2024-2025)

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

Current: 20 checkpoints (all SPY-only, biased). Target: 50+ checkpoints across panier.

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
