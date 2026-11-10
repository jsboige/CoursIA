# DL-LSTM

**Asset class:** US Equities/ETF
**Cloud project ID:** None (local only)

## Description

Stratégie LSTM de deep learning sous **PyTorch**. Prédit le **prix normalisé** de SPY à J+1 à partir d'une séquence de 20 prix normalisés (min-max scaling ajusté sur le train uniquement) ; la prédiction est dénormalisée en prix, puis convertie en rendement prédit pour la décision d'achat/liquidation.

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/DL-LSTM"`
**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics

| Metric | Value |
|--------|-------|
| Model | LSTM (PyTorch) |
| Rebalance | Daily |

## Files

- `main.py` - Stratégie (algorithme LEAN, modèle LSTM PyTorch embarqué, SPY daily)
- `quantbook.ipynb` - Notebook de recherche QuantBook : entraînement du LSTM PyTorch sur les prix normalisés SPY, split train/test 80/20 avec évaluation sur le test set
