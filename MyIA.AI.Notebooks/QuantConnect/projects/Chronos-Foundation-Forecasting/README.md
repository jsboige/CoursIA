# Chronos-Foundation-Forecasting

**Asset class:** US Equities/ETF (8 ETFs)
**Cloud project ID:** 29443479

## Description

Ensemble GradientBoosting + Ridge (sklearn) sur features de prix (lag returns, volatilité glissante, prix vs SMA, cross-asset SPY), avec filtre de régime SMA200 (positions défensives en bear). L'étude de départ est Chronos (modèle fondation, voir research.ipynb), mais le déploiement n'utilise pas d'embeddings Chronos : le v1 (poids d'attention hardcodés) a été remplacé par cet ensemble réel (docstring main.py). Prédiction du rendement 10 j avancé sur un univers de 8 ETFs.

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Chronos-Foundation-Forecasting"`

**QC Cloud:** Deployed as project 29443479.

## Backtest Metrics

> **Deux versions, l'ID Cloud ne reproduit plus le dépôt (#19018, sondage du 2026-10-03).** Le projet Cloud 29443479 porte désormais **v2b** (modifié 2026-03-29 : GBM n_estimators 80 / lr 0.03 / min_samples_leaf 8, fin étendue à 2026-03-01, rebalancement **hebdomadaire**), tandis que le `main.py` commité ici est **v2** (n_estimators 50 / lr 0.05 / min_samples_leaf 5, fin 2026-01-01, rebalancement **bimensuel**). Un backtest lancé sur 29443479 aujourd'hui mesure v2b, pas le fichier de ce dépôt ; les chiffres ci-dessous décrivent une exécution du code v2 (version dépôt).

| Metric | Value |
|--------|-------|
| Model | Ensemble GB + Ridge |
| Universe | 8 ETFs |
| Rebalance | Biweekly (v2, dépôt) — v2b Cloud : weekly |
| Sharpe Ratio (v2, code dépôt) | 0.253 (fenêtre 2015-01-01 → 2026-01-01) |

## Files

- main.py - Strategy (v2, ensemble sklearn GBM + Ridge, régime filter SMA200)
- research.ipynb - Étude Chronos (Ex09) : modèle fondation T5, sensibilité au nombre de tokens, et §7.5 confrontation du backtest QC Cloud (main.py) aux approches fondation

## References

- Amazon Chronos: Learning the Language of Time Series
