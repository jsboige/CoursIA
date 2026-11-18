# TrendStocksLite

**Asset class:** US Equities (15 stocks)
**Cloud project ID:** None (local only)
**Projets de la mesure #21594 :** `38163246` (code actuel, avec les modes de référence) · `38163245` (contrôle, code d'origine)

## Description

Simplified trend-following strategy on a 15-stock universe using SMA200 + EMA filter.
Weekly rebalance: goes long stocks above SMA200 with positive EMA slope, flat otherwise.
Lighter version of TrendStocks-Alpha (which uses 50 stocks + monthly rebalance).

## Paramètres

| Paramètre | Valeurs | Défaut | Rôle |
|---|---|---|---|
| `mode` | `strategy`, `spy`, `6040`, `ew15` | `strategy` | `strategy` garde la décision du code ; `spy` détient SPY à 100 % ; `6040` détient SPY à 60 % et BND à 40 % ; `ew15` détient les 15 titres de l'univers à poids égal. Les références sont rééquilibrées au début de chaque mois, une minute après l'ouverture |
| `start_date` | date `%Y%m%d` | 2015-01-01 | début de la fenêtre |
| `end_date` | date `%Y%m%d` | 2024-12-31 | fin de la fenêtre |

Les quatre modes tracent chaque jour la valeur du portefeuille à l'ouverture de SPY (graphique `shadow`, séries `e0` à `e4`). En mode référence, le rééquilibrage hebdomadaire de la stratégie ne fait rien. BND n'est abonné qu'en mode `6040`. Sans paramètre, la décision de la stratégie ne change pas : le contrôle ci-dessous le vérifie ordre par ordre.

## Verdict contre références détenues (#21594)

Le protocole a été écrit dans #21594 avant le premier backtest, sur le modèle de #21329. Les deux références du verdict, SPY détenu et le 60/40, tournent dans le même algorithme que la stratégie, sous le même modèle de courtage. Une troisième référence, les 15 titres de l'univers à poids égal (`ew15`), sert de diagnostic et ne compte pas dans le verdict.

Trois propriétés du code sont gardées telles quelles :

- chaque lundi, la stratégie répartit tout le portefeuille à poids égal entre les titres retenus. Un titre hors tendance ne laisse pas sa part en liquidités : elle va aux autres titres retenus, et un seul titre retenu porte tout le portefeuille. La stratégie ne passe en liquidités que si aucun titre n'est retenu ;
- le compte est déclaré sur marge. Les poids visés somment à 100 %, mais l'exposition observée dépasse légèrement 1 : au plus 1,042 sur la fenêtre codée (avril 2020), au-dessus de 1 sur 203 des 3 654 points quotidiens du graphique d'exposition de QC. Après la fenêtre codée, le maximum est de 1,023 (avril 2025), sur 14 points de 569 ;
- les ordres de la stratégie sont soumis à 10 h, heure de New York, 30 minutes après l'ouverture, sur les deux fenêtres. Aucun n'est passé à minuit.

Les séries comparées sont la valeur du portefeuille à chaque ouverture de SPY. Les tests passent par `Paradox46Benchmarks/significance.py`, avec un taux sans risque nul :

- écart de Sharpe de Ledoit-Wolf ;
- bootstrap stationnaire ;
- écart de moyennes de Newey-West.

Sur chaque fenêtre, la correction de Holm porte sur les six p-valeurs du verdict. Le diagnostic est une exécution séparée, avec sa propre correction de Holm sur trois p-valeurs.

Règle de verdict, écrite avant la mesure :

- `BEATS` : écart de Sharpe positif et significatif (Holm < 0,05, Ledoit-Wolf) contre les deux références ;
- `NO BEATS` : Sharpe de la stratégie inférieur à celui de SPY détenu ;
- `INCONCLUSIVE` : tous les autres cas.

**Contrôle d'innocuité : tenu.** En mode `strategy`, sur la fenêtre codée, le code instrumenté reproduit le backtest du code d'origine (`b78394a166cf681bc471760cc20f92b7`, projet 38163245) :

- 3 671 ordres sur 3 671, sans écart de date, de symbole ni de quantité ;
- 27 statistiques QC sur 27.

| Fenêtre | Séances | Sharpe stratégie (taux nul) | SPY détenu (taux nul) | 60/40 (taux nul) | p Holm (Ledoit-Wolf, SPY / 60/40) | Verdict |
|---|---|---|---|---|---|---|
| Codée, 2015-01-02 → 2024-12-31 | 2516 | 1,217 | 0,786 | 0,802 | 0,0276 / 0,0575 | **INCONCLUSIVE** |
| Hors échantillon, 2025-01-02 → 2026-07-22 | 388 | −0,120 | 1,063 | 1,180 | 0,71 / 0,71 | **NO BEATS** |

Statistiques QC (calculées par QC avec son propre taux sans risque). Leurs Sharpe ne se comparent pas à ceux de la table du dessus : QC retranche un taux sans risque non nul et part de ses propres séries quotidiennes, alors que le protocole prend un taux nul sur la valeur du portefeuille à l'ouverture. Le verdict se lit sur la table du dessus.

| Fenêtre | Mode | Sharpe QC (taux de QC, autre échelle) | CAGR | Pire baisse | Ordres | Backtest |
|---|---|---|---|---|---|---|
| Codée | stratégie | 0,943 | 22,66 % | 29,3 % | 3671 | `151248dbe1529177fd1a2905b8479330` |
| Codée | SPY détenu | 0,533 | 12,97 % | 33,7 % | 1 | `78eda14c58a44477faf101f87b4e11b4` |
| Codée | 60/40 | 0,441 | 8,41 % | 21,7 % | 201 | `e15ee3c4fb623a4af21043494272957b` |
| Codée | 15 titres à poids égal | 0,900 | 21,78 % | 33,7 % | 978 | `32df005386137a97519a88e574a18bb4` |
| Hors échantillon | stratégie | −0,404 | −2,95 % | 25,0 % | 548 | `ca04e64b6ba588be663a0c021979481d` |
| Hors échantillon | SPY détenu | 0,646 | 18,37 % | 18,7 % | 2 | `5a72e4abfca5c374c3fad6254b2a411f` |
| Hors échantillon | 60/40 | 0,546 | 12,68 % | 11,2 % | 30 | `2af5e094a8b6c49f8631395089d8b9f7` |
| Hors échantillon | 15 titres à poids égal | 0,825 | 18,87 % | 13,9 % | 189 | `b42acdc71f09577e33f1363ec348be8d` |

Le backtest hors échantillon a été demandé jusqu'au 2026-10-20, mais il s'arrête le 2026-07-22 : les nœuds QC utilisés coupent les backtests environ 90 jours avant la date du jour. Sur ses 388 séances, la fenêtre a peu de puissance. Aucun paramètre n'a été réglé sur cette période.

**Lecture.** Sur la fenêtre codée, la stratégie a le Sharpe ponctuel le plus élevé des trois portefeuilles du verdict. Contre SPY détenu, l'écart est significatif après correction (p de Holm 0,0276 pour Ledoit-Wolf, intervalle bootstrap à 95 % de +0,13 à +0,79). Contre le 60/40, il ne l'est pas tout à fait : la p de Holm de Ledoit-Wolf vaut 0,0575, juste au-dessus du seuil, alors que l'intervalle bootstrap (+0,08 à +0,81) exclut zéro. La règle demande un écart significatif contre les deux références : le verdict est `INCONCLUSIVE`, de justesse. Hors échantillon, le Sharpe de la stratégie devient négatif (−0,120) quand SPY détenu fait 1,063 : `NO BEATS`. Sur cette fenêtre courte, aucun écart n'est significatif.

**Diagnostic : la règle de tendance ne change presque rien au Sharpe des 15 titres.** Sur la fenêtre codée, les 15 titres détenus à poids égal ont un Sharpe à taux nul de 1,168, contre 1,217 pour la stratégie. L'écart (+0,048) n'est pas significatif : p de Holm 1,0 pour les trois tests, intervalle bootstrap de −0,21 à +0,33. Selon la règle écrite avant la mesure, la question reste ouverte : la règle de tendance n'ajoute rien de mesurable, sans retirer non plus. L'avance de la stratégie sur SPY détenu se retrouve dans son univers détenu tel quel (Sharpe 1,168 contre 0,786 ; cet écart-là n'a pas été testé). Cet univers a été choisi après coup parmi les grands gagnants de la décennie. Hors échantillon, la stratégie fait nettement moins bien que les mêmes titres détenus (−0,120 contre 1,357). La p brute de Ledoit-Wolf vaut 0,029, mais l'écart n'est plus significatif après correction (p de Holm 0,087).

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/TrendStocksLite"`
```bash
lean backtest --project .
```

**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.
**Mesure du 2026-10-20 (#21594) :** voir la section « Verdict contre références détenues ». Les paramètres `mode`, `start_date` et `end_date` se passent au backtest.

## Backtest Metrics

| Metric | Value |
|--------|-------|
| Universe | 15 US stocks |
| Rebalance | Weekly |
| Indicators | SMA200 + EMA slope |
| Leverage | Standard (equal weight) |

## Files

- `main.py` - Strategy (SMA200 trend + EMA filter, 15 stocks)
- `research.ipynb` - Universe selection and rebalance frequency analysis
