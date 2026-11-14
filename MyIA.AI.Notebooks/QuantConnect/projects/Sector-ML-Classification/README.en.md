# Sector ML Classification

**Status**: research strategy, measured on QC Cloud on 2026-11-04 (see [Measured results](#measured-results)). Starting point: the ML classification chapter of *Hands-On AI Trading*.

## Description

Sector rotation driven by a Random Forest classifier. For each of the eight SPDR sector ETFs in the universe, the model estimates the probability that the return over the next 10 trading days exceeds +1.2%. The algorithm holds the best-ranked sectors at equal weight, and falls back to defensive sectors when SPY trades below its 200-day moving average.

### Universe

| Ticker | Sector | Defensive |
|--------|--------|-----------|
| XLK | Technology | |
| XLF | Financials | |
| XLV | Health Care | yes |
| XLE | Energy | |
| XLY | Consumer Discretionary | |
| XLP | Consumer Staples | yes |
| XLI | Industrials | |
| XLU | Utilities | yes |

SPY is the benchmark (`set_benchmark`) and the regime filter; it is never held.

### How it works

- **Regime**: the market is bearish when SPY closes below its 200-day SMA.
- **Biweekly rebalance**, 30 minutes after the open: first trading day of the month, then fourteen trading days later (`month_start("SPY", 14)`).
- **Bull market**: the 4 sectors with the highest BUY-class probability.
- **Bear market**: only XLU, XLP and XLV are scored. The algorithm keeps the top 2, or moves fully to cash if the best probability is below 0.35.
- **Allocation**: equal weight; only positions that leave the selection are liquidated.
- **Monthly retraining**, on the first trading day of the month, 60 minutes after the open. The training window ends 15 days before the retraining date and goes back `TRAIN_LOOKBACK_DAYS = 252 * 4` days. This value is passed to `timedelta` as calendar days, so the window covers about 2.8 years, not the 4 years stated by the code comment. One sample is drawn every 5 trading days.
- **Model**: `RandomForestClassifier(n_estimators=100, max_depth=5, min_samples_leaf=10, random_state=42)` after a `StandardScaler`. The seed is fixed: two runs of the same code on the same data produce the same orders.
- **Warm-up**: 220 days.

### Features (11)

- returns over 5, 10, 20 and 50 trading days (4 features);
- volatility of daily returns over 20 trading days;
- normalized RSI 14, `(RSI - 50) / 50`: the QC `RSI` indicator (Wilder smoothing) at prediction time, a simple rolling mean of gains and losses at training time;
- SMA 20 / SMA 50 ratio;
- position of the price within the range of the last 20 trading days;
- ratio of the price to the 52-week high;
- return relative to SPY over 5 and 10 trading days (2 features).

### Labels

Return over the next 10 trading days: class 2 (BUY) above +1.2%, class 0 (AVOID) below -0.8%, class 1 (HOLD) in between. Only the class-2 probability is used for ranking.

## Measured results

QC Cloud backtests of 2026-11-04, coded window 2015-01-01 → 2024-12-31, starting capital 100,000, brokerage model and account type of the code (`set_brokerage_model`, margin account), default parameters. The two strategy arms differ only in how the training RSI is computed.

| Arm | Backtest | Sharpe (QC) | CAGR | Max drawdown | Orders |
|-----|----------|-------------|------|--------------|--------|
| Current code, training RSI fixed (#23329) | `7ae7eab21fb1455fa56f4f051d714ed0` | 0.382 | 9.57% | 35.3% | 1033 |
| Code before #23329, constant training RSI | `c9ba4426833348253d1b31b2285b99a3` | 0.46 | 11.20% | 35.3% | 1024 |
| Control: SPY held alone | `6c2bce7882ff4af927e3bd67fc84847b` | 0.535 | 12.99% | 33.5% | 1 |

**Reading.** On this window, neither arm does better than SPY held alone: the current code returns a Sharpe of 0.382 and a CAGR of 9.57%, against 0.535 and 12.99% for the control, with a deeper maximum drawdown (35.3% against 33.5%). The training-RSI fix (#23329) does not improve the measurement: the earlier arm, whose RSI feature was constant in training, returned a Sharpe of 0.46 and a CAGR of 11.20%. Giving the model back an informative feature is therefore not enough here. The gap between the two arms (one feature out of eleven) is measured on a single window with a single seed: it is not evidence that the feature hurts. The Sharpe is the one QC computes, risk-free rate deducted. These figures describe a research strategy; they are not a recommendation.

The history in the `main.py` docstring (v2b to v5) is an iteration log: it was measured on windows (2015-2026, 2018-2026 for v2b) that are no longer the code's window, before the RSI fix. The current code does not reproduce it.

## Files

- `main.py`: QC algorithm (Random Forest classifier, SMA 200 regime filter).
- `research.ipynb`: research notebook (features, labels, training, 2023-2025 simulation, analysis of the selected sectors).
- `test_historical_rsi.py`: tests of the training RSI, without the QC engine (`python -m unittest test_historical_rsi` from the project folder).
- `config.json`: project configuration.

## References

- **Book**: *Hands-On AI Trading* (ML Classification chapter).
- **Related notebook**: QC-Py-19-ML-Supervised-Classification.ipynb.
