# ML-TextClassification

**Asset class:** US Equities (5 stocks: AAPL, MSFT, GOOGL, AMZN, TSLA)
**Cloud project ID:** None (local only)

## Description

Text classification strategy using Naive Bayes on simulated news sentiment. Predicts stock direction from news headlines (simulated via random sampling for demo purposes). Daily classification with biweekly retraining.

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/ML-TextClassification"`
**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics

| Metric | Value |
|--------|-------|
| Model | Naive Bayes text classifier |
| Universe | 5 stocks (AAPL, MSFT, GOOGL, AMZN, TSLA) |
| Rebalance | Daily (classification-based) |

## Files

- main.py - Strategy (262L, MLTextClassificationAlgorithm)
