# VolTarget-Momentum

**Classe d'actifs :** Multi-actifs (Actions, Obligations, Matières premières)

**Cloud project ID :** 30784745

## Description

Allocation basée sur un ranking de six actifs risqués (SPY, EFA, EEM, TLT, GLD, DBC) avec BND comme refuge défensif (safe harbor). La docstring attribue à la v5 un Sharpe de 0,65 et un CAGR de 14,72 %, sur une fenêtre qu'elle ne dit pas ; mesurée contre deux références détenues, la stratégie est `NO BEATS` sur 2015-2024 et `INCONCLUSIVE` sur 2025-2026 (section « Verdict contre références détenues (#22923) »). Utilise SMA200 plus des filtres de momentum 6 mois et 12 mois pour la sélection des actifs. Cible 15 % de volatilité annualisée en utilisant la volatilité réalisée sur 60 jours pour le dimensionnement des positions, avec levier contraint entre 0.3 et 1.5x. Rebalance mensuelle.

## Comment exécuter

### Lean CLI
```bash
lean backtest --algorithm VolTarget-Momentum/main.py
```

### QC Cloud
Ouvrir le projet cloud (ID : 30784745), compiler et lancer un backtest.

Trois paramètres servent à la mesure #22923 : `mode` (`strategy` par défaut, `spy`, `6040`, `ew7`, `novt`), `start_date` et `end_date` (format `AAAA-MM-JJ`, par défaut les dates codées, 2015-01-01 et 2025-01-01).

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

## Verdict contre références détenues (#22923)

Le protocole a été écrit dans #22923 avant le premier backtest, sur le modèle de #21594, repris par #22828 et #22869. Les deux références du verdict, SPY détenu et le 60/40 (SPY 60 %, BND 40 %), tournent dans le même algorithme que la stratégie, sous le même modèle de courtage. Deux diagnostics ne comptent pas dans le verdict :

- `ew7`, les sept ETF du code à poids égal, rééquilibrés chaque mois : la sélection et la pondération ajoutent-elles quelque chose à la détention des sept ETF ?
- `novt`, la même règle avec un multiplicateur de volatilité fixé à 1 : la cible de volatilité ajoute-t-elle quelque chose ?

Le paramètre `mode` choisit le portefeuille. En mode `strategy`, la décision du code ne change pas. Les sept ETF sont déjà abonnés par le code, BND compris : aucun mode n'ajoute d'abonnement.

Propriétés du code, gardées telles quelles :

- **le multiplicateur de volatilité se calcule sur le portefeuille détenu, pas sur la cible**, et sans les covariances : la variance estimée est la somme des carrés des poids multipliés par la variance de chaque ETF sur 60 séances. Quand le portefeuille détenu est entièrement en BND, sa volatilité estimée est basse (3,2 % le 2015-02-02, 5,3 % le 2025-02-03) et le multiplicateur atteint sa borne de 1,5 : le premier rééquilibrage risqué de chaque fenêtre vise 150 % (SPY 50 % et TLT 100 % le 2015-02-02 ; DBC, EEM, EFA, GLD et SPY pour 150 % le 2025-02-03), et une partie des achats est refusée faute de marge, puis renvoyée à la séance suivante (#20523) ;
- **le compte est déclaré sur marge, et la stratégie emprunte la plupart du temps.** Sur le graphique `Exposure` de Lean (un point par jour), l'exposition brute, sans aucune position courte, dépasse 1 sur 2943 points sur 3654 (80,5 %) dans la fenêtre 1, avec un maximum de 1,566 le 2018-10-30, et sur 388 points sur 548 (70,8 %) dans la fenêtre 2, avec un maximum de 1,495 le 2025-12-03. Le Sharpe à taux nul ne compte pas le coût de cet emprunt. Le diagnostic `novt` reste proche de 1 : au plus 1,032 dans la fenêtre 1 (11,5 % des points au-dessus de 1, origine non recherchée), 0,998 dans la fenêtre 2 ;
- **la première décision de chaque fenêtre est entièrement en BND.** Le préchauffage de 280 jours calendaires compte 194 séances, et la moyenne de 200 séances n'est prête pour aucun ETF le premier jour : le code les écarte tous et place 100 % en BND (régime `BEAR` au journal, le 2015-01-02 comme le 2025-01-02). La stratégie n'entre sur les ETF risqués qu'au deuxième rééquilibrage mensuel, alors que les références sont investies dès la première séance ;
- les ordres de la stratégie sont soumis à 10 h, heure de New York, 30 minutes après l'ouverture, et remplis à la clôture du jour (`MarketOnClose`). Ceux des références partent à 9 h 31 et sont aussi remplis à la clôture. Le filtre de tendance lit la clôture de la veille.

Les fenêtres sont coupées au 1er janvier 2025, date de fin du code. La docstring classe six versions (« v6 : marginal ») sans dire sur quelle fenêtre : la fenêtre 1 recouvre, au moins en partie, l'échantillon sur lequel la v5 a été retenue ; la fenêtre 2 commence à la date de fin codée.

Les séries comparées sont la valeur du portefeuille à chaque ouverture de SPY. Les tests passent par `Paradox46Benchmarks/significance.py`, avec un taux sans risque nul :

- écart de Sharpe de Ledoit-Wolf ;
- bootstrap stationnaire ;
- écart de moyennes de Newey-West.

Sur chaque fenêtre, la correction de Holm porte sur les six p-valeurs du verdict. Les diagnostics sont une exécution séparée, avec leur propre correction de Holm sur six p-valeurs.

Règle de verdict, écrite avant la mesure :

- `BEATS` : écart de Sharpe positif et significatif (Holm < 0,05, Ledoit-Wolf) contre les deux références ;
- `NO BEATS` : Sharpe de la stratégie inférieur à celui de SPY détenu ;
- `INCONCLUSIVE` : tous les autres cas.

**Contrôle d'innocuité : tenu.** En mode `strategy`, sur la fenêtre codée (2015-01-01 → 2025-01-01), le code instrumenté (backtest `6144b57d3390d3b946e1e0e1877e1af2`, projet 38520062) reproduit le backtest du code d'origine (`d82bc1c1fe30846bf5f41b21948b0e07`, projet 38520056), lancé le même jour :

- 488 ordres sur 488, sans écart de date, de symbole ni de quantité ;
- 27 statistiques QC sur 27, et 8 statistiques d'exécution sur 8.

Ces statistiques sont celles de la colonne « après » de la mesure #20523 ci-dessus (Sharpe QC 0,441, CAGR 10,13 %, pire baisse 20,8 %). L'ancienne ligne du registre `docs/qc/qc-strategies-status.md` (Sharpe QC 0,500, CAGR 11,12 %, pire baisse 21,2 %, PSR 9,45 %) date d'avant #20523.

| Fenêtre | Séances | Sharpe stratégie (taux nul) | SPY détenu (taux nul) | 60/40 (taux nul) | p Holm (Ledoit-Wolf, SPY / 60/40) | Verdict |
|---|---|---|---|---|---|---|
| 1, 2015-01-02 → 2024-12-31 | 2516 | 0,713 | 0,786 | 0,802 | 1,0 / 1,0 | **NO BEATS** |
| 2, 2025-01-02 → 2026-07-01 | 374 | 1,508 | 1,080 | 1,224 | 1,0 / 1,0 | **INCONCLUSIVE** |

Statistiques QC (calculées par QC avec son propre taux sans risque). Leurs Sharpe ne se comparent pas à ceux de la table du dessus : QC retranche un taux sans risque non nul et part de ses propres séries quotidiennes, alors que le protocole prend un taux nul sur la valeur du portefeuille à l'ouverture. Le verdict se lit sur la table du dessus.

| Fenêtre | Mode | Sharpe QC (taux de QC, autre échelle) | CAGR | Pire baisse | Volatilité annuelle (QC) | Ordres | Backtest |
|---|---|---|---|---|---|---|---|
| 1 | stratégie | 0,441 | 10,13 % | 20,8 % | 12,6 % | 488 | `56646b0e63c81276b74d6d89c2007fdd` |
| 1 | SPY détenu | 0,533 | 12,97 % | 33,7 % | 14,6 % | 1 | `686a3baca1c4fe271d840e4740031c1f` |
| 1 | 60/40 | 0,442 | 8,41 % | 21,7 % | 9,0 % | 201 | `e267340331387e61d8c9bb1587f677fd` |
| 1 | 7 ETF à poids égal | 0,210 | 5,12 % | 19,3 % | 7,9 % | 534 | `30db40ef963550c03440fcd1a9ffaf78` |
| 1 | multiplicateur fixé à 1 | 0,372 | 7,75 % | 15,1 % | 9,7 % | 442 | `b98f9d2b7db1ad91d5855a7edc6d4dc9` |
| 2 | stratégie | 1,037 | 28,13 % | 10,1 % | 15,4 % | 91 | `d02adf2774364975e61413990edbbd96` |
| 2 | SPY détenu | 0,665 | 18,96 % | 18,7 % | 14,7 % | 2 | `7b557e7e152bb3fda75455447fdeeb96` |
| 2 | 60/40 | 0,590 | 13,37 % | 11,2 % | 9,1 % | 30 | `f2212fa820dad1637760f5000ce3ef56` |
| 2 | 7 ETF à poids égal | 1,127 | 20,34 % | 8,0 % | 8,8 % | 83 | `d2bb8dc6991fc742e41400e5987299b2` |
| 2 | multiplicateur fixé à 1 | 0,922 | 21,99 % | 9,3 % | 12,4 % | 71 | `592b179ab5e45225430cf52be0f2b391` |

Le backtest de la fenêtre 2 va jusqu'à sa date codée : sa dernière séance est le 2026-07-01, et la coupure d'environ 90 jours que les nœuds QC utilisés appliquent à la fin des backtests ne l'a pas atteint. Sur ses 374 séances, la fenêtre a peu de puissance. Ses deux références reproduisent celles des mesures #22828 et #22869 sur la même fenêtre, lancées dans d'autres algorithmes : mêmes Sharpe à taux nul (1,080 et 1,224) et mêmes statistiques QC.

**Lecture.** Sur la fenêtre 1, la stratégie a un Sharpe ponctuel inférieur à celui de SPY détenu (0,713 contre 0,786) et à celui du 60/40 (0,802) : selon la règle écrite avant la mesure, le verdict est `NO BEATS`. Aucun des six tests n'est significatif (p de Holm 1,0), et l'intervalle bootstrap à 95 % de l'écart contre SPY détenu va de −0,66 à +0,53. Sur la fenêtre 2, son Sharpe ponctuel dépasse celui des deux références (1,508 contre 1,080 et 1,224), sans aucun écart significatif (p de Holm 1,0, intervalle bootstrap de −1,41 à +2,02 contre SPY détenu) : le verdict est `INCONCLUSIVE`. Ce Sharpe de la fenêtre 2 est obtenu avec une exposition supérieure à 1 sur 70,8 % des points, sans coût d'emprunt.

**Diagnostic : la cible de volatilité agit surtout comme un levier ; l'apport de la sélection reste ouvert sur la fenêtre 1 et manque sur la fenêtre 2.**

| Fenêtre | Diagnostic | Sharpe du diagnostic (taux nul) | Écart stratégie − diagnostic | Intervalle bootstrap 95 % | p Holm (Ledoit-Wolf) | Corrélation | Lecture |
|---|---|---|---|---|---|---|---|
| 1 | 7 ETF à poids égal | 0,577 | +0,136 | −0,36 à +0,64 | 1,0 | 0,60 | question ouverte |
| 1 | multiplicateur fixé à 1 | 0,700 | +0,013 | −0,09 à +0,12 | 1,0 | 0,98 | question ouverte |
| 2 | 7 ETF à poids égal | 1,865 | −0,357 | −1,31 à +0,46 | 1,0 | 0,87 | rien de mesurable |
| 2 | multiplicateur fixé à 1 | 1,472 | +0,036 | −0,25 à +0,34 | 1,0 | 0,98 | question ouverte |

À taux nul et sans coût d'emprunt, un levier constant ne change pas le Sharpe. L'écart contre le multiplicateur fixé à 1 mesure donc ce que la cible de volatilité apporte au-delà du levier : +0,013 sur la fenêtre 1 et +0,036 sur la fenêtre 2, non significatifs, pour des séries corrélées à 0,98. Elle augmente le rendement (CAGR QC 10,13 % contre 7,75 % sur la fenêtre 1) en augmentant la volatilité (12,6 % contre 9,7 %) et en empruntant. Sur la fenêtre 1, la stratégie dépasse les sept ETF détenus à poids égal (0,713 contre 0,577) sans que l'écart soit significatif : la question reste ouverte. Sur la fenêtre 2, elle fait moins bien qu'eux (1,508 contre 1,865), sans écart significatif non plus.

**Prédictions écrites avant la mesure :**

- contrôle d'innocuité tenu : juste ;
- fenêtre 1, aucun écart significatif contre l'une ou l'autre référence, donc `INCONCLUSIVE` ou `NO BEATS` : juste (`NO BEATS`) ;
- diagnostic `ew7` sur la fenêtre 1, Sharpe de la stratégie supérieur sans écart significatif : juste ;
- diagnostic `novt` sur la fenêtre 1, écart non significatif : juste. Son signe, non prédit, est positif ;
- fenêtre 2 : pas de prédiction.

## Fichiers

| Fichier | Description |
|---------|-------------|
| `main.py` | Stratégie v5 (cible de volatilité, filtres de momentum, allocation par rang sur 6 actifs risqués et 1 défensif), avec le paramètre `mode`, les paramètres de fenêtre et la trace `shadow` de la mesure #22923 |
| `config.json` | Configuration du projet (cloud-id, organization-id, language) |

## Références

- [Documentation QuantConnect](https://www.quantconnect.com/docs/)
