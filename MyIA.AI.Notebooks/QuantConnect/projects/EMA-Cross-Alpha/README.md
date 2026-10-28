# EMA-Cross-Alpha

**Classe d'actifs :** Actions US (Grandes capitalisations tech)
**ID projet Cloud :** 28885488

## Description

Stratégie alpha de croisement EMA basée sur le framework, sur 5 grandes valeurs tech (AAPL, MSFT, GOOGL, AMZN, NVDA).
Utilise le framework QuantConnect Alpha Model avec `EMACrossAlpha` (fast=20, slow=50) et un rebalancement quotidien du portefeuille via `MultiStrategyPouchesPCM`.

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

## Non-régression du module partagé (#20188)

Depuis #21140, `main.py` importe `MultiStrategyPouchesPCM` de `SharedPCM/pouches_pcm.py` au lieu de la copie locale `portfolio_construction.py`. Deux backtests QC Cloud du 2026-10-26, aux paramètres par défaut et sur la fenêtre 2015-01-01 → 2024-12-31, vérifient que ce changement ne modifie aucun ordre :

- **A** : le code de `main` au commit `54f9b9eec1`, avec le module partagé ;
- **B** : les mêmes `main.py` et `alpha_models.py`, avec l'ancienne copie `portfolio_construction.py` prise au commit qui précède la migration (`fb3d05db0a^`). Le projet n'a qu'une poche. L'argument `additive=False`, que l'ancienne copie ne connaît pas, est retiré de l'appel : le mode non additif est le seul comportement de l'ancienne copie.

A et B portent la même instrumentation, qui ne passe aucun ordre. Elle relève la valeur du portefeuille chaque jour à minuit, période de chauffe comprise (60 séances). En fin de backtest, elle calcule une empreinte SHA-256 par année des ordres (identifiant, date, titre, quantité, statut, prix) et des valeurs relevées.

| | A (module partagé) | B (ancienne copie) |
|---|---|---|
| Ordres | 3 812 | 3 812 |
| Valeurs relevées | 3 739 | 3 739 |
| Dernière valeur relevée | 2 145 082,06 | 2 145 082,06 |
| Sharpe (QC) | 1,12 | 1,12 |
| CAGR | 35,691 % | 35,691 % |
| Pire baisse | 37,4 % | 37,4 % |

Les empreintes annuelles sont égales : 10 sur 10 pour les ordres, 11 sur 11 pour les valeurs. Les 27 statistiques de QC sont égales, rotation comprise. La migration ne change donc pas le comportement du projet. Traces hors dépôt : `QC-traces/20188-nr/`.

Ces chiffres diffèrent de ceux de la section « Métriques de backtest » ci-dessus. Cette section mesure le code du projet cloud 28885488, qui n'est pas celui du dépôt (vérifié le 2026-10-26) ; la re-mesure est suivie par #22654.

## Fichiers

- `main.py` - Point d'entrée de la stratégie (modèle alpha du framework)
- `alpha_models.py` - Implémentation de EMACrossAlpha
- `SharedPCM/pouches_pcm.py` (bibliothèque de projet QC) — `MultiStrategyPouchesPCM`, PCM par poches canonique importé par `main.py` (extraction #19821 brique 1, tranche dedup)
- `quantbook.ipynb` - Notebook de recherche

## Références

- Framework QC : pattern Alpha Model + Portfolio Construction
- Réf : Brock et al. (1992), moving average trading rules
