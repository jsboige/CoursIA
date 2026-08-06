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

## Métriques de backtest (2015-2024)

| Métrique | Valeur |
|----------|--------|
| Sharpe Ratio | -0.01 |
| CAGR | 2.799% |
| Max Drawdown | 14.000% |
| Net Profit | 31.824% |
| Total Orders | 314 |
| Benchmark | SPY |
| Rebalance | Quotidien |
| Univers | 5 actions tech |

> **Provenance** : backtest QC Cloud `8119728de11270cec45b8db81ed30a0b` (2026-08-05),
> projet 28885488, IBKR margin, 2516 jours tradeables (2015-2024). Re-exécuter via
> QC Cloud pour recalculer.
>
> **Lecture honnête** : un Sharpe de -0,01 est un edge statistiquement nul (PSR 0,006%),
> et un CAGR de 2,8 % est sous le risk-free — la stratégie **ne bat pas le benchmark**.
> C'est un contre-exemple pédagogique : un croisement EMA naïf (fast=20, slow=50) sur
> 5 grandes valeurs tech sous-performe le buy & hold de SPY sur 2015-2024. La valeur
> aveugle « ~1,00 » auparavant inscrite ici était fausse (deux ordres de grandeur).

## Fichiers

- `main.py` - Point d'entrée de la stratégie (modèle alpha du framework)
- `alpha_models.py` - Implémentation de EMACrossAlpha
- `portfolio_construction.py` - Module MultiStrategyPCM
- `quantbook.ipynb` - Notebook de recherche

## Références

- Framework QC : pattern Alpha Model + Portfolio Construction
- Réf : Brock et al. (1992), moving average trading rules
