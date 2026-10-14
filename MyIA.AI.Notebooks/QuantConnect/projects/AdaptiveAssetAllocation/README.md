# AdaptiveAssetAllocation

**Classe d'actifs :** Actions/ETF US (diversifié)
**ID projet Cloud :** Aucun (local uniquement)

## Description

Top-4 ETFs par momentum 6 mois avec optimisation de portefeuille à variance minimum. Sélection parmi SPY, EFA, EEM, VNQ, GLD, DBC, TLT, IEF, TIP, HYG (10 ETFs, top 4).

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/AdaptiveAssetAllocation"`
**QC Cloud :** Pas encore déployé. Copier les fichiers dans un nouveau projet QC Cloud pour exécuter.

## Métriques du backtest

| Métrique | Valeur |
|----------|--------|
| Méthode | Momentum 6M + variance min. |
| Univers | 10 ETFs (top 4) |
| Rebalancement | Mensuel |

## Recherche

`quantbook.ipynb` — QuantBook d'étude de la stratégie AAA (exécution via QC Cloud) : chargement des données 2008-2026 (cycle complet incluant une crise), implémentation momentum + min-variance, balayage des trois paramètres (Top N, période de momentum, fenêtre de volatilité), comparaison aux benchmarks SPY/QQQ et visualisations. Il conclut sur les paramètres retenus dans `main.py` (top 4, momentum 126 jours, volatilité 60 jours). Son univers d'étude est élargi aux large-cap US (commentaire « Docker data availability » dans le notebook) ; la stratégie déployée (`main.py`) reste sur les 10 ETFs ci-dessus.

## Fichiers

- main.py - Stratégie (iter2c, allocation adaptative)
- quantbook.ipynb - QuantBook de recherche : sweeps de paramètres, benchmarks, verdict

## Références

- Butler, Philbrick, Gordillo (2012), Adaptive Asset Allocation: A Primer, SSRN 2328254
