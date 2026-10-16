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

## Achats refusés et renvoi à la séance suivante

En résolution journalière, tous les ordres partent en `MarketOnClose` : soumis à 10:00 New York, remplis à la clôture. Lean contrôle le pouvoir d'achat d'un achat avant qu'aucune vente du même rééquilibrage ne soit remplie, et y impute la marge des achats déjà acceptés ce jour-là. Comme l'exposition monte jusqu'à 150 % (multiplicateur de volatilité plafonné à 1,5), des achats de rééquilibrage étaient refusés (statut `Invalid`) et jamais renvoyés : la ligne restait vide jusqu'au rééquilibrage suivant. Le 2015-09-01 et le 2018-11-01, l'achat de BND refusé (cible 100 %, régime `BEAR`) a laissé le portefeuille entièrement en liquidités pendant un mois.

`main.py` renvoie désormais un achat refusé à la séance suivante : `on_order_event` note le refus, un événement quotidien renvoie `set_holdings` vers la cible du dernier rééquilibrage, et chaque renvoi écrit une ligne `RETRY` au journal. Mesure avant/après sur QC Cloud, selon un protocole posé avant les runs (#20523) :

| Fenêtre | Achats refusés | Renvoyés et remplis | Sharpe | Rendement annuel composé | Pire baisse |
|---|---|---|---|---|---|
| 2015-01-01 -> 2025-01-01 (codée) | 11 avant, 13 après | 0 avant, 13 après | 0,470 -> 0,441 | 10,55 % -> 10,13 % | 21,1 % -> 20,8 % |
| 2025-01-01 -> 2026-07-10 (hors échantillon) | 1 avant, 1 après | 0 avant, 1 après | 1,051 -> 1,072 | 28,19 % -> 28,84 % | 10,2 % -> 10,1 % |

L'écart de métriques n'a pas de signe à retenir : il dépend de ce que fait le marché les mois où une ligne manquait, favorable sur la fenêtre codée, défavorable hors échantillon (la ligne GLD à 50 % restée vide en février 2025). Ce que le correctif apporte, c'est que le backtest mesure la stratégie décrite. Le jour du rééquilibrage, l'achat refusé l'est toujours : l'écart dure une séance au lieu d'un mois.

Les chiffres de la description (v5 : Sharpe 0,65, rendement annuel 14,72 %) viennent d'une mesure antérieure que le run avant correctif ne reproduit pas (Sharpe 0,470 sur la fenêtre codée) ; cet écart n'est pas instruit ici.

## Fichiers

| Fichier | Description |
|---------|-------------|
| `main.py` | Volatility targeting avec filtres momentum et allocation basée sur ranking sur 6 actifs risqués + 1 défensif |
| `config.json` | Configuration du projet (cloud-id, organization-id, language) |

## Références

- [Documentation QuantConnect](https://www.quantconnect.com/docs/)
