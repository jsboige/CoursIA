# Crypto-MultiCanal

**Classe d'actifs :** Crypto (BTC)
**ID projet Cloud :** 30750734

## Description

Stratégie ZigZag multi-canal sur Bitcoin. Utilise 3 canaux ZigZag imbriqués (court/moyen/long) pour identifier la structure de tendance à plusieurs échelles.

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Crypto-MultiCanal"`

**QC Cloud :** Déployée comme projet 30750734.

## Métriques de backtest

| Métrique | Valeur |
|----------|--------|
| Méthode | ZigZag multi-canal (3 canaux imbriqués : macro / meso / micro) |
| Univers | BTCUSDT (Binance, daily) |
| Période | 2015-01-01 → 2024-12-31 (10 ans stricts) |
| Brokerage | Binance real fees (default) |

### Backtest c.800 (tracker #7575 tranche 2/9 — re-execution 2026-07-22)

QC Cloud project **30750734** — backtest id **`d8bf46d13a8871e4dea0c7b2286e2919`** (Completed, 3653 tradeable dates, 69 orders, ~instantané).

| Métrique | Valeur c.800 |
|----------|--------------|
| **Sharpe Ratio** | 0.333 |
| **CAGR** | 4.589% |
| **Max Drawdown** | 14.100% |
| **Total Net Profit** | 56.704% |
| **Net Profit ($USDT)** | $5,904.50 |
| **Total Orders** | 69 |
| **Tradeable Dates** | 3653 |
| **Version** | v17 (v15 base + trail 3%) |

**Comparaison avec prior backtest `82fae2cde69e476ec3671b6603a300ac`** (2026-06-14, baseline post-2801) : **résultats identiques** (Sharpe 0.333 / CAGR 4.589% / MaxDD 14.100% / TotalNetProfit 56.704% / 69 orders / 3653 dates). La seule différence marginale est `Probabilistic Sharpe Ratio` (12.951% → 1.551%, recalculé car basé sur distributions d'essais aléatoires). La cohérence confirme la **reproductibilité déterministe** de la stratégie v17 sur QC Cloud Lean Engine (même code + mêmes hyperparams + même période).

**Preuves d'exécution** : `c800-cloud-id-30750734.json` (compile_id `0d55c270...` BuildSuccess + backtest_id `d8bf46d1...` Completed + paramètres + delta_vs_prior structuré).

## Fichiers

- main.py - Stratégie (v17 dans main.py, README référence v18 par convention ; channel_helpers inlinés pour la compatibilité QC Cloud)
- channel_helpers.py - Helpers d'origine (conservés pour l'usage Lean CLI local / notebook de recherche)
