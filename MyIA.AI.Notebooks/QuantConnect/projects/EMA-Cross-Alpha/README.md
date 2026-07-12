# EMA-Cross-Alpha

**Classe d'actifs :** Actions US (Grandes capitalisations tech)
**ID projet Cloud :** 28885488

## Description

Stratégie alpha de croisement EMA basée sur le framework, sur 5 grandes valeurs tech (AAPL, MSFT, GOOGL, AMZN, NVDA).
Utilise le framework QuantConnect Alpha Model avec `EMACrossAlpha` (fast=20, slow=50) et un rebalancement quotidien du portefeuille via `MultiStrategyPCM`.

Le modèle alpha génère des insights quand l'EMA rapide croise l'EMA lente pour chaque action, et le module de construction de portefeuille alloue le capital en conséquence.

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/EMA-Cross-Alpha"`
```bash
lean backtest --project .
```

**QC Cloud :** Ouvrir le projet 28885488 dans l'IDE QuantConnect et cliquer sur « Backtest ».

## Métriques de backtest (2015-2026)

| Métrique | Valeur |
|----------|--------|
| Sharpe Ratio | ~1,00 |
| Benchmark | SPY |
| Rebalance | Quotidien |
| Univers | 5 actions tech |

## Fichiers

- `main.py` - Point d'entrée de la stratégie (modèle alpha du framework)
- `alpha_models.py` - Implémentation de EMACrossAlpha
- `portfolio_construction.py` - Module MultiStrategyPCM
- `quantbook.ipynb` - Notebook de recherche

## Références

- Framework QC : pattern Alpha Model + Portfolio Construction
- Réf : Brock et al. (1992), moving average trading rules
