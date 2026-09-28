# Chronos-Foundation-Forecasting

**Asset class:** US Equities/ETF (8 ETFs)
**Cloud project ID:** 29443479

## Description

Ensemble GradientBoosting + Ridge (sklearn) sur features de prix (lag returns, volatilité glissante, prix vs SMA, cross-asset SPY), avec filtre de régime SMA200 (positions défensives en bear). L'étude de départ est Chronos (modèle fondation, voir research.ipynb), mais le déploiement n'utilise pas d'embeddings Chronos : le v1 (poids d'attention hardcodés) a été remplacé par cet ensemble réel (docstring main.py). Prédiction du rendement 10 j avancé sur un univers de 8 ETFs.

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Chronos-Foundation-Forecasting"`

**QC Cloud:** Deployed as project 29443479.

## Backtest Metrics

| Metric | Value |
|--------|-------|
| Model | Ensemble GB + Ridge |
| Universe | 8 ETFs |
| Rebalance | Biweekly |
| Sharpe Ratio (v2) | 0.253 |

## Files

- main.py - Strategy (v2, ensemble sklearn GBM + Ridge, régime filter SMA200)
- research.ipynb - Étude Chronos (Ex09) : modèle fondation T5, sensibilité au nombre de tokens, et §7.5 confrontation du backtest QC Cloud (main.py) aux approches fondation

## References

- Amazon Chronos: Learning the Language of Time Series
