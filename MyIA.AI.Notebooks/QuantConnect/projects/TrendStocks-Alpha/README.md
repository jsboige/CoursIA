# TrendStocks-Alpha

**Asset class:** US Equities (Large-cap diversified)
**Cloud project ID:** 28885507

## Description

Framework-based trend-following alpha strategy on 15 large-cap stocks across sectors.
Uses `TrendStocksAlpha` with EMA(20/50) for signal and SMA(200) as trend confirmation.
Weekly rebalance via `MultiStrategyPouchesPCM`.

The strategy enters long positions when short-term EMA is above long-term EMA AND the price is above the 200-day SMA, confirming the secular uptrend.

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/TrendStocks-Alpha"`
```bash
lean backtest --project .
```

**QC Cloud:** Open project 28885507 in the QuantConnect IDE and click "Backtest".

## Backtest Metrics (2020-2025)

| Metric | Value |
|--------|-------|
| Sharpe Ratio | ~0.61 |
| Benchmark | SPY |
| Rebalance | Weekly |
| Universe | 15 large-cap stocks |

Source : reproduction QuantBook (`quantbook.ipynb`, Sharpe 0.609 sur 2020-2025). Run cloud de sweep enregistré : Sharpe 0.512, CAGR 15.73 %, MaxDD 39.6 % (`docs/qc/qc-strategies-status.md` l.262).

## Non-régression du module partagé (#20188)

Depuis #21140, `main.py` importe `MultiStrategyPouchesPCM` de `SharedPCM/pouches_pcm.py` au lieu de la copie locale `portfolio_construction.py`. Deux backtests QC Cloud du 2026-10-26, aux paramètres par défaut et sur la fenêtre 2015-01-01 → 2024-12-31, vérifient que ce changement ne modifie aucun ordre :

- **A** : le code de `main` au commit `54f9b9eec1`, avec le module partagé ;
- **B** : les mêmes `main.py` et `alpha_models.py`, avec l'ancienne copie `portfolio_construction.py` prise au commit qui précède la migration (`fb3d05db0a^`). Le projet n'a qu'une poche. L'argument `additive=False`, que l'ancienne copie ne connaît pas, est retiré de l'appel : le mode non additif est le seul comportement de l'ancienne copie.

A et B portent la même instrumentation, qui ne passe aucun ordre. Elle relève la valeur du portefeuille chaque jour à minuit, période de chauffe comprise (210 séances). En fin de backtest, elle calcule une empreinte SHA-256 par année des ordres (identifiant, date, titre, quantité, statut, prix) et des valeurs relevées.

| | A (module partagé) | B (ancienne copie) |
|---|---|---|
| Ordres | 4 883 | 4 883 |
| Valeurs relevées | 3 955 | 3 955 |
| Dernière valeur relevée | 661 576,85 | 661 576,85 |
| Sharpe (QC) | 0,842 | 0,842 |
| CAGR | 20,701 % | 20,701 % |
| Pire baisse | 33,7 % | 33,7 % |

Les empreintes annuelles sont égales : 10 sur 10 pour les ordres, 11 sur 11 pour les valeurs. Les 27 statistiques de QC sont égales, rotation comprise. La migration ne change donc pas le comportement du projet. Traces hors dépôt : `QC-traces/20188-nr/`.

La section « Backtest Metrics » ci-dessus porte sur 2020-2025 et sur d'autres runs : ses chiffres ne se comparent pas directement à ceux-ci. Le projet cloud 28885507 porte un code différent de celui du dépôt (vérifié le 2026-10-26) ; la re-mesure est suivie par #22654.

## Files

- `main.py` - Strategy entry point (framework alpha model)
- `alpha_models.py` - TrendStocksAlpha implementation
- `SharedPCM/pouches_pcm.py` (bibliothèque de projet QC) — `MultiStrategyPouchesPCM`, PCM par poches canonique importé par `main.py` (extraction #19821 brique 1, tranche dedup)
- `quantbook.ipynb` - Research notebook

## References

- QC Framework: Alpha Model + Portfolio Construction pattern
- Ref: Faber (2007), "A Quantitative Approach to Tactical Asset Allocation"
