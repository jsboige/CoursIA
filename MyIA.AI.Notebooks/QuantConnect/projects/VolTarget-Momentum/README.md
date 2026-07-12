# VolTarget-Momentum

**Classe d'actifs :** Multi-actifs (Actions, Obligations, Matières premières)

**Cloud project ID :** 30784745

## Description

Allocation basée sur un ranking de six actifs risqués (SPY, EFA, EEM, TLT, GLD, DBC) avec BND comme refuge défensif (safe harbor). La variante v5 best a atteint un Sharpe de 0.65 et un CAGR de 14.72 %. Utilise SMA200 plus des filtres de momentum 6 mois et 12 mois pour la sélection des actifs. Cible 15 % de volatilité annualisée en utilisant la volatilité réalisée sur 60 jours pour le dimensionnement des positions, avec levier contraint entre 0.3 et 1.5x. Rebalance mensuelle.

## Comment exécuter

### Lean CLI
```bash
lean backtest --algorithm VolTarget-Momentum/main.py
```

### QC Cloud
Ouvrir le projet cloud (ID : 30784745), compiler et lancer un backtest.

## Métriques de backtest

| Méthode | Rebalance | Paramètres clés |
|---------|-----------|-----------------|
| Vol-targeting basé sur ranking + momentum | Mensuelle | Vol target 15 %, vol réalisée 60 jours, levier 0.3-1.5x, SMA200 + momentum 6m/12m |

## Fichiers

| Fichier | Description |
|---------|-------------|
| `main.py` | Volatility targeting avec filtres momentum et allocation basée sur ranking sur 6 actifs risqués + 1 défensif |
| `config.json` | Configuration du projet (cloud-id, organization-id, language) |

## Références

- [Documentation QuantConnect](https://www.quantconnect.com/docs/)
