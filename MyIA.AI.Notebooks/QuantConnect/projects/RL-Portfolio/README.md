# RL-Portfolio

**Asset class:** Template (RL portfolio)
**Cloud project ID:** None (local only)

## Description

Projet de référence en optimisation de portefeuille par RL : la stratégie Q-Learning effective vit dans les notebooks (recherche documentée, baseline incluse), `main.py` reste un squelette de structure.

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/RL-Portfolio"`
**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics

| Metric | Value |
|--------|-------|
| Status | Reference implementation (Q-Learning dans les notebooks ; main.py squelette) |

## Files

- main.py - Template structure
- quantbook.ipynb - QuantBook de recherche : allocation de portefeuille par apprentissage par renforcement
- research.ipynb - Recherche : analyse et optimisation de la stratégie Q-Learning d'allocation (implémentation effective - main.py reste un template)
