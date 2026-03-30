# BTC-MachineLearning Robustness Research

## Overview

This research notebook validates the ML strategy robustness through:

1. **Extended Training Period Analysis** (2017-2022 vs 2021-2022)
2. **Feature Importance by Market Regime** (bull vs bear patterns)
3. **Walk-Forward Validation** (the gold standard for ML trading)
4. **Optimal Retraining Frequency** (30 vs 60 vs 90 days)
5. **ML vs Buy-and-Hold Benchmark**

## Files

- **`research_robustness.ipynb`**: Main research notebook (execute in QuantConnect Research)
- **`research_robustness_local.py`**: Standalone demo script (uses synthetic data)
- **`RESEARCH.md`**: This file

## Motivation

The current strategy (main.py) has:
- Training: 2021-2022 (2 years)
- Testing: 2023-2024 (1.5 years)
- Retraining: Every 30 days
- **Never backtested** → No validation of actual performance

**Research Questions**:
- Does training on 2017-2022 (5 years, multiple bull/bear cycles) improve generalization?
- Which features are stable vs regime-dependent?
- Is 30-day retraining optimal, or should we use 60/90 days?
- Does ML actually beat buy-and-hold after transaction costs?
- Is the strategy robust across different time periods (walk-forward)?

## Methodology

### Walk-Forward Validation

The notebook implements the industry-standard walk-forward validation:

```
Train [==============] Test [===] Retrain [==============] Test [===] ...
  730 days (2 years)    90 days      730 days              90 days
```

**Why Walk-Forward?**
- Simulates production: train on past, predict future
- Tests adaptability to regime changes
- Avoids cherry-picking a lucky test period
- Reveals if performance is consistent or luck

### Features Analyzed (9 total)

1. `sma_ratio`: close / SMA(20)
2. `rsi`: RSI(14)
3. `daily_return`: Daily price change
4-7. `ema_10/20/50/200`: EMA ratios
8. `adx`: ADX(14) - trend strength
9. `atr`: ATR(14) / close - volatility

### Metrics Tracked

| Metric | Description | Target |
|--------|-------------|--------|
| **Sharpe Ratio** | Risk-adjusted return | > 0.5 |
| **Accuracy** | Classification accuracy | > 55% |
| **Max Drawdown** | Worst peak-to-trough | < -20% |
| **Total Return** | Cumulative return | > Buy-and-Hold |
| **Consistency** | % positive Sharpe windows | > 60% |

## How to Execute

### Option 1: QuantConnect Research (Recommended)

1. **Open Project 21047688** (BTC-MachineLearning) in QuantConnect
2. **Navigate to Research** tab
3. **Upload** `research_robustness.ipynb`
4. **Execute cells sequentially** (top to bottom)
   - Cell 1: Introduction (markdown)
   - Cell 2: Load BTC data from 2017-01-01
   - Cell 3: Compute 9 features
   - Cell 4: H1 - Extended training period
   - Cell 5: H2 - Feature importance by regime
   - Cell 6: Walk-forward validation
   - Cell 7: H3 - Retraining frequency
   - Cell 8: H4 - ML vs Buy-and-Hold
   - Cell 9: Findings summary (markdown)
   - Cell 10: Recommendations JSON

5. **Expected runtime**: 10-15 minutes (depends on data loading)

### Option 2: Local Demo (Synthetic Data)

```bash
cd MyIA.AI.Notebooks/QuantConnect/ESGF-2026/examples/BTC-MachineLearning
python research_robustness_local.py
```

**Note**: Local script uses synthetic data for demonstration. Real results require QuantConnect.

## Expected Results

### Hypotheses to Test

| Hypothesis | Expected Outcome | Confidence |
|------------|------------------|------------|
| **H1**: 5Y training > 2Y training | Sharpe improves by 10-20% | Medium |
| **H2**: Features vary by regime | RSI important in bear, EMA in bull | High |
| **H3**: 60d optimal retraining | Better stability than 30d | Medium |
| **H4**: ML beats buy-and-hold | Sharpe 0.5-0.8 vs ~0.3 | Low |
| **H5**: Walk-forward consistent | > 60% positive windows | Medium |

### Realistic Expectations

**Crypto ML is hard**:
- High volatility → Low Sharpe (0.3-0.8 is good)
- Non-stationary → Regime changes break models
- Data leakage risk → Walk-forward is critical

**Success criteria**:
- ✓ Walk-forward Sharpe > 0.4 (median)
- ✓ > 60% positive windows
- ✓ Beats buy-and-hold on risk-adjusted basis
- ✓ No signs of data leakage (training accuracy < 0.65)

## Key Insights Expected

### 1. Training Period Impact

Longer training (2017-2022) includes:
- 2017 bull run (+1400%)
- 2018 bear (-80%)
- 2019-2020 recovery (+300%)
- 2021 bull (+100%)
- 2022 bear (-60%)

**Expected**: Better generalization but potentially lower peak performance.

### 2. Feature Importance by Regime

**Bull markets** (momentum-driven):
- EMA crossovers (10/20/50) likely most important
- ADX (trend strength) high importance
- RSI less useful (stays overbought)

**Bear markets** (mean-reversion):
- RSI likely most important (oversold bounces)
- ATR (volatility) high importance
- Long-term EMAs less useful

### 3. Retraining Trade-off

- **30 days**: High adaptation, high noise → unstable
- **60 days**: Balance adaptation/stability → likely optimal
- **90 days**: Low noise, slow adaptation → lag regime changes

### 4. ML vs Buy-and-Hold

**Crypto HODL is strong**:
- BTC 2023-2025: likely +50-100% total return
- ML needs to reduce drawdowns to win on Sharpe
- Transaction costs not modeled → real edge smaller

**Expected**: ML beats on Sharpe (risk-adjusted) but not total return.

### 5. Walk-Forward Reality Check

**Common outcomes**:
- First windows: good (model fresh)
- Middle windows: mixed (regime changes)
- Recent windows: worse (overfitting to past regimes)

**Red flags**:
- Only 1-2 windows positive → lucky period
- Sharpe variance > 1.0 → unstable
- Recent windows all negative → model degrading

## Notebook Structure (10 Cells)

### Cell 1: Introduction (Markdown)
- ML trading challenges (overfitting, data leakage, regime changes)
- Why walk-forward is the gold standard
- 5 hypotheses to test

### Cell 2: Data Loading (Code)
```python
qb = QuantBook()
btc = qb.AddCrypto("BTCUSDT", Resolution.Daily)
history = qb.History(btc, datetime(2017, 1, 1), datetime.now())
# ~3000 daily bars expected
```

### Cell 3: Feature Engineering (Code)
```python
features_df = compute_features(df)
# Output: 9 features + 1 label, ~2900 samples after dropna
# Data leakage check: training accuracy should be < 0.65
```

### Cell 4: H1 - Training Period (Code)
```python
result_2y = train_and_evaluate("2021-2022", test="2023-now")
result_5y = train_and_evaluate("2017-2022", test="2023-now")
# Compare Sharpe, accuracy, excess return vs BnH
```

### Cell 5: H2 - Feature Importance (Code)
```python
# Train separate models on:
# - 2017 Bull, 2018 Bear, 2020-2021 Bull, 2022 Bear, 2023+ Recovery
# Heatmap of feature importance by regime
# Identify stable vs regime-dependent features
```

### Cell 6: Walk-Forward (Code)
```python
wf_results = walk_forward_validation(train=730d, test=90d, retrain=60d)
# Output: ~20-30 windows, each with Sharpe/accuracy/return
# Plot Sharpe by window, cumulative returns
```

### Cell 7: H3 - Retraining Frequency (Code)
```python
# Compare 30, 60, 90 day retraining
# Metrics: mean Sharpe, std Sharpe, % positive windows
# Bar charts for comparison
```

### Cell 8: H4 - ML vs BnH (Code)
```python
# Test period: 2023-now
# Compare: Total return, Sharpe, Max DD, Volatility
# Verdict: Does ML beat HODL?
```

### Cell 9: Findings (Markdown)
- Summary of each hypothesis (confirmed/rejected)
- Key insights on feature stability
- Recommendations for main.py parameters

### Cell 10: Recommendations JSON (Code)
```python
recommendations = {
    "optimal_training_period": "2017-2022" or "2021-2022",
    "optimal_retraining_interval": 30/60/90,
    "expected_sharpe": 0.X,
    "implementation_steps": [...]
}
```

## Implementation After Research

### Update main.py

Based on notebook findings, update:

```python
# Current values
TRAIN_START = datetime(2021, 1, 1)  # May change to 2017
TRAIN_END = datetime(2022, 12, 31)
RETRAIN_INTERVAL_DAYS = 30  # May change to 60 or 90

# Feature selection
# Remove low-importance features if identified
# Add regime detection if needed
```

### Compile and Backtest

```python
# Via MCP QC tools
read_file(projectId=21047688, name="main.py")
create_compile(projectId=21047688)
# Wait for compile success
# Backtest via web UI (API requires paid account)
```

### Validation Checklist

- [ ] Walk-forward Sharpe > 0.4 (median)
- [ ] > 60% positive windows
- [ ] No data leakage (training acc < 0.65)
- [ ] Backtest Sharpe matches walk-forward expectation (±30%)
- [ ] Max drawdown acceptable (< -25%)

## Limitations

### Research Limitations

1. **No transaction costs**: Spread, slippage, fees not modeled
2. **Perfect execution**: Assumes instant fills at predicted price
3. **Historical patterns**: Past may not predict future
4. **Static features**: No adaptive feature engineering
5. **Daily resolution**: Intraday patterns ignored

### Strategy Limitations

1. **Regime dependency**: May fail in unprecedented market conditions
2. **Overfitting risk**: RandomForest can memorize training data
3. **Feature stability**: Important features may change over time
4. **Position sizing**: Probabilistic sizing adds complexity
5. **Stop-loss/TP**: Fixed levels may not suit all regimes

## Next Steps After Execution

1. **Fill in recommendations JSON** (Cell 10) with actual values from outputs
2. **Update main.py** with optimal parameters
3. **Compile** via MCP QC
4. **Backtest** via web UI
5. **Compare** backtest results to walk-forward predictions
6. **Monitor** if deployed live: track actual vs expected Sharpe

## Success Criteria

Research is **successful** if:
- ✓ Walk-forward validation completed (20+ windows)
- ✓ Mean Sharpe > 0.3 (crypto baseline)
- ✓ Feature importance insights actionable
- ✓ Optimal retraining frequency identified
- ✓ Clear recommendation for TRAIN_START date

Research is **failed** if:
- ✗ All windows negative Sharpe → model fundamentally broken
- ✗ Data leakage detected (training acc > 0.7)
- ✗ Walk-forward Sharpe variance > 2.0 → too unstable
- ✗ ML loses to BnH on both return AND Sharpe

## References

### ML in Trading Best Practices

- **Lopez de Prado, M.** (2018). *Advances in Financial Machine Learning*
  - Walk-forward validation (Ch. 7)
  - Feature importance stability (Ch. 8)
  - Backtesting pitfalls (Ch. 11)

- **Aronson, D.** (2006). *Evidence-Based Technical Analysis*
  - Data mining bias
  - Multiple testing problem

### QuantConnect Documentation

- [Research Environment](https://www.quantconnect.com/docs/v2/research/overview)
- [QuantBook API](https://www.quantconnect.com/docs/v2/research/quantbook-api)
- [Machine Learning](https://www.quantconnect.com/docs/v2/writing-algorithms/machine-learning)

## Author

Research notebook created: 2026-02-17
Project: BTC-MachineLearning (21047688)
Strategy: RandomForest classification for BTC daily direction

---

**IMPORTANT**: This notebook uses real market data from QuantConnect. Results will vary based on:
- Data quality and availability
- Market conditions during test periods
- Random seed in RandomForest (set to 42 for reproducibility)

Always validate findings with multiple runs and out-of-sample testing.
