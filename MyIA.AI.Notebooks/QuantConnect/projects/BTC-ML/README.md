# BTC-ML

**Asset class:** Crypto (BTC)
**Cloud project ID:** 29318876 (deployed on QC Cloud)

## Description

Machine learning strategy on Bitcoin using sklearn `RandomForestClassifier` over
trend/momentum features (SMA, RSI, EMA 10/20/50/200, ADX, ATR, annualized
volatility) with strict walk-forward feature construction, periodic retraining
(60-day interval, 2-year lookback), probabilistic position sizing, volatility
filter, and risk management (stop-loss -8%, take-profit +15%). Strict train/OOS
split: training 2017-2020, out-of-sample backtest 2021-2026 (no overlap).

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/BTC-ML"`
**QC Cloud:** Deployed (project 29318876). Verified via backtest po2026-verify-btc-ml-oos-2021-2026 (2026-07-15): BuildSuccess, 0 compile errors.

## Backtest Metrics

Verified out-of-sample backtest (2021-01-01 to 2026-03-01, Binance cash, USDT):

| Metric | Value |
|--------|-------|
| Method | RandomForestClassifier (n=50, depth=4, leaf=10) |
| Universe | BTCUSDT (Binance, daily) |
| Rebalance | Daily |
| Sharpe ratio | 0.057 |
| Probabilistic Sharpe | 1.520% |
| Compounding annual return | 3.692% |
| Max drawdown | 15.400% |
| Total net profit | +20.612% (USDT 20,612 on 100k) |
| Total orders | 13 |
| Tradeable days | 1886 |

The low Sharpe (0.057) and near-zero Probabilistic Sharpe (1.52%) indicate the
strategy's edge over this OOS window is statistically indistinguishable from
noise — i.e. **NO BEATS** vs buy-and-hold BTC over the same period. Honest
verdict: the strategy runs cleanly and is correctly structured (no compile
errors, no data leakage), but does not demonstrate alpha. Suitable as a
pedagogical reference for ML-strategy scaffolding, not as a live alpha source.

## Files

- main.py - Strategy (`MyEnhancedCryptoMlAlgorithm`)
- research.ipynb - Research notebook
- quantbook.ipynb - QuantBook exploration
