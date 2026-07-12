# AdaptiveAssetAllocation

**Classe d'actifs :** Actions/ETF US (diversifié)
**ID projet Cloud :** Aucun (local uniquement)

## Description

Top-4 ETFs par momentum 6 mois avec optimisation de portefeuille à variance minimum. Sélection parmi SPY, QQQ, TLT, GLD, EFA, IWM.

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/AdaptiveAssetAllocation"`
**QC Cloud :** Pas encore déployé. Copier les fichiers dans un nouveau projet QC Cloud pour exécuter.

## Métriques du backtest

| Métrique | Valeur |
|----------|--------|
| Méthode | Momentum 6M + variance min. |
| Univers | 6 ETFs (top 4) |
| Rebalancement | Mensuel |

## Fichiers

- main.py - Stratégie (iter2c, allocation adaptative)

## Références

- Faber (2007), A Quantitative Approach to Tactical Asset Allocation
