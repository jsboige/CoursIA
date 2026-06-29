# EMA-Cross-Crypto

**Classe d'actifs :** Crypto (BTC, ETH)
**ID projet Cloud :** Aucun (local uniquement)

## Description

Croisement dual EMA sur crypto. Prend position long quand EMA(20) > EMA(60) sur BTC/ETH.

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/EMA-Cross-Crypto"`
**QC Cloud :** Pas encore déployée. Copier les fichiers dans un nouveau projet QC Cloud pour l'exécuter.

## Métriques de backtest

| Métrique | Valeur |
|----------|--------|
| Méthode | Croisement EMA 20/60 |
| Univers | BTC, ETH |
| Rebalance | Quotidien |

## Fichiers

- main.py - Stratégie
