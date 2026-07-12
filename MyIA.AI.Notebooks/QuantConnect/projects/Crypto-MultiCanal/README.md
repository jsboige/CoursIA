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
| Méthode | ZigZag multi-canal |
| Univers | BTCUSD |
| Canaux | 3 (imbriqués) |

## Fichiers

- main.py - Stratégie (v18, channel_helpers inlinés pour la compatibilité QC Cloud)
- channel_helpers.py - Helpers d'origine (conservés pour l'usage Lean CLI local / notebook de recherche)
