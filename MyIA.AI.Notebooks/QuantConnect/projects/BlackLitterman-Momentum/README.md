# BlackLitterman-Momentum

**Classe d'actifs :** Actions/ETF US (multi-actifs)
**ID projet Cloud :** 29816300

## Description

Portefeuille Black-Litterman avec vues de momentum multi-fenêtres (1M, 3M, 6M, 12M). L'optimisation BL produit les poids finaux.

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/BlackLitterman-Momentum"`

**QC Cloud :** Déployé en tant que projet 29816300.

## Métriques du backtest

| Métrique | Valeur |
|----------|--------|
| Méthode | Black-Litterman + vues momentum |
| Lookbacks | 1M, 3M, 6M, 12M |
| Rebalancement | Mensuel |

## Fichiers

- main.py - Stratégie (v1.0, BL momentum)

## Références

- Black & Litterman (1992), Global Portfolio Optimization
