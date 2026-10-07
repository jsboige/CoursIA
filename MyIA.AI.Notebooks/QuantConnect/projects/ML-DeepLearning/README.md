# ML-DeepLearning

**Asset class:** US Equities (SPY, QQQ, IWM — TLT s'ajoute dans le quantbook)
**Cloud project ID:** None (local only)

## Description

Prédiction de direction par deep learning avec un **vrai LSTM** (tensorflow/keras dans le quantbook, PyTorch dans main.py). Prédit la direction du lendemain (hausse/baisse/stable) sur les ETF de l'univers à partir de rendements open-close décalés. L'ancien libellé « Ridge as LSTM proxy » décrivait une itération antérieure du projet.

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/ML-DeepLearning"`
**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics

| Metric | Value |
|--------|-------|
| Model | LSTM (tensorflow/keras dans le quantbook, PyTorch dans main.py) |
| Universe | SPY, QQQ, IWM (+ TLT dans le quantbook) |
| Rebalance | Weekly |

## Files

- main.py - Strategy (172L, MLDeepLearningAlgorithm)
