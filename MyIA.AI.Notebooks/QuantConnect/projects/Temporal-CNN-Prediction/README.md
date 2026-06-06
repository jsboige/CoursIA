# Temporal-CNN-Prediction

**Asset class:** US Equities (8 diversified ETFs: SPY, QQQ, IWM, XLK, XLF, XLV, DIA, EFA)
**Cloud project ID:** None (local only)

## Description

Temporal CNN-inspired direction prediction using sklearn MLPClassifier (128, 64, 32) on multi-scale temporal features. Note: despite the name, uses MLPClassifier (not Conv1D). Features mimic CNN temporal patterns at 5d/10d/20d scales. 3-class prediction (UP/DOWN/NEUTRAL) with biweekly rebalance.

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Temporal-CNN-Prediction"`

**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics

| Metric | Value |
|--------|-------|
| Model | MLPClassifier (128, 64, 32) |
| Universe | 8 ETFs (SPY, QQQ, IWM, XLK, XLF, XLV, DIA, EFA) |
| Rebalance | Biweekly |

## Files

- `main.py` - Strategy (v2, MLPClassifier with temporal features)
- `research.ipynb` - Feature engineering and hyperparameter tuning
