# TrendWeather, univers ex ante (évaluation #19393)

Projet d'évaluation dérivé de [`Framework_Composite_TrendWeather`](../Framework_Composite_TrendWeather/), composite de l'Algorithm Framework de QuantConnect. La règle de verdict et la grille de paramètres ont été fixées dans l'[issue #19393](https://github.com/jsboige/CoursIA/issues/19393) avant le premier backtest.

## La règle d'origine

- **Poche tendance (75 %)** : 15 grandes capitalisations fixées dans le code (AAPL, MSFT, GOOGL, AMZN, NVDA, JPM, V, MA, UNH, JNJ, XOM, CVX, HD, PG, KO). Chaque mois, un titre est retenu si son cours dépasse sa SMA200 et si son EMA20 dépasse son EMA50. Les titres retenus sont pondérés par leur taux de variation sur 63 séances ; les autres reçoivent un signal plat.
- **Poche All Weather (25 %)** : SPY 30 %, IEF 30 %, GLD 30 %, XLP 10 %, fixe.
- **Construction** : chaque poche reçoit sa part du capital, les cibles s'additionnent, rééquilibrage tous les 31 jours, préchauffage de 270 séances.

## Pourquoi une variante

La liste des 15 titres a été écrite en mars 2026. Plusieurs d'entre eux comptent parmi les plus fortes hausses de la décennie (NVDA, AAPL, MSFT…) : sur toute fenêtre antérieure, la liste porte une information que l'algorithme ne pouvait pas avoir. La variante `pit` (*point in time*) remplace la liste par une règle **ex ante** : chaque mois, les `top_n` = 15 plus grandes capitalisations d'actions américaines, d'après les seules données fondamentales disponibles à cette date. La règle d'origine (`fixed`) est mesurée à côté : l'écart entre les deux chiffre ce que la liste apporte.

## Ce qui change ici

Le signal et la construction de portefeuille sont repris du projet d'origine. Les changements :

1. **Paramètres** (tableau ci-dessous). Avec `universe=fixed` et les autres valeurs par défaut, c'est la règle d'origine.
2. **Sélection `pit`** : au premier jour de chaque mois, l'univers retient les `top_n` plus grandes capitalisations parmi les actions qui ont des données fondamentales, cotent plus de 5 dollars et sont la ligne principale de leur société. Les certificats de dépôt (ADR) sont exclus.
3. **Sortie d'un titre** : un titre détenu qui n'est plus membre reçoit un signal plat ; il est vendu au rééquilibrage suivant.
4. **Titre entrant** : ses indicateurs sont initialisés sur son historique, pour qu'il soit évaluable dès son entrée.
5. Les titres sont suivis par leur identifiant QuantConnect (`Symbol`) et non plus par leur code : un changement de code en cours de fenêtre ne coupe plus le suivi.

Les ordres passent par le modèle de frais par défaut de Lean pour ce courtier, multiplié par `fee_mult`. Comme dans l'original, le compte est sur marge, mais les cibles somment à 100 % au plus : il n'y a pas de levier.

## Paramètres de backtest

| Paramètre | Défaut | Rôle |
|-----------|--------|------|
| `start`, `end` | aucun (obligatoires) | fenêtre, contrat du rejeu en ombre (#18923) |
| `universe` | `fixed` | `fixed` : les 15 titres du code d'origine ; `pit` : sélection mensuelle ex ante |
| `trend_alloc` | 0,75 | part du capital de la poche tendance (le reste va à All Weather) |
| `top_n` | 15 | nombre de titres sélectionnés en mode `pit` |
| `weighting` | `momentum` | `momentum` : poids proportionnels au taux de variation sur 63 séances ; `equal` : poids égaux |
| `fee_mult` | 1 | multiplicateur des frais (2 = frais doublés) |

## Sorties

Contrat du rejeu en ombre (`ML-Training-Pipeline/shadow/README.md`) : après chaque clôture, la valeur du portefeuille est écrite dans le graphique `shadow` (séries `e0` à `e4` à tour de rôle). S'y ajoutent les frais cumulés (`fees`, en fraction du capital de départ) et la rotation cumulée (`turnover`). Les mesures se calculent sur ces séries, pas sur les statistiques du rapport QuantConnect.

Le journal de l'algorithme écrit :

- `select <date> <codes>` à chaque sélection mensuelle (mode `pit`) ;
- `fill <date> <code> <quantité> @ <prix>` pour chaque exécution ;
- en fin de run, `end closes=<séances> invested=<séances investies> universe=<mode> final=<valeur>`.

## Résultats

Backtests QuantConnect du 2026-10-06, modèle de frais par défaut de Lean pour ce courtier. Mesures sur les séries du rejeu en ombre (Sharpe à taux sans risque nul), sauf mention « QC ». Références : SPY détenu et 60/40 SPY/IEF du projet [`FourSleeve774Benchmarks`](../FourSleeve774Benchmarks/) (#19139), mêmes séances (2 194 rendements, aucune séance manquante d'un côté ou de l'autre).

### Fenêtre principale, 2018-01-01 → 2026-09-25

| Run | Sharpe | CAGR | Pire baisse | Rotation / an | Frais / an | Ordres |
|-----|--------|------|-------------|---------------|------------|--------|
| **univers ex ante** (`universe=pit`) | **1,05** | 21,7 % | 24,3 % | 7,1 | 0,22 % | 1 727 |
| univers ex ante, frais doublés | 1,04 | 21,6 % | 24,4 % | 7,1 | 0,44 % | 1 729 |
| règle d'origine (`universe=fixed`) | 1,22 | 23,0 % | 27,6 % | 7,0 | 0,25 % | 1 679 |
| SPY détenu | 0,79 | 13,9 % | 33,6 % | 0,1 | 0,00 % | — |
| 60/40 SPY/IEF | 0,81 | 8,9 % | 21,2 % | 0,3 | 0,02 % | — |

Frais et rotation sont exprimés en fraction du capital de départ. Statistiques QC (Sharpe avec taux sans risque) : 0,77 et PSR 14,5 % pour l'univers ex ante, 0,91 et PSR 26,8 % pour la règle d'origine. Le run `fixed` n'enregistre pas la dernière séance (2026-09-25) : c'est un effet de bord de fin de fenêtre, et les comparaisons portent sur les séances communes.

### Verdict préinscrit : `NO BEATS`

Différence de Sharpe de l'univers ex ante contre chaque référence, par bootstrap circulaire par blocs de 21 séances (10 000 tirages, graine 18921, correction de Holm) :

| Référence | Différence | IC 95 % | p unilatérale | p Holm | Frais doublés | 2018-2020 | 2021-2023 | 2024 → 2026-09 |
|-----------|-----------:|---------|--------------:|-------:|--------------:|----------:|----------:|---------------:|
| SPY détenu | +0,26 | [−0,25 ; +0,72] | 0,15 | 0,31 | +0,26 | +0,47 | +0,55 | −0,38 |
| 60/40 SPY/IEF | +0,23 | [−0,30 ; +0,74] | 0,19 | 0,31 | +0,23 | +0,20 | +0,79 | −0,37 |

Les deux différences sont positives, mais aucune n'est significative : la règle préinscrite classe ce cas en `NO BEATS`. Le rendement est plus élevé que celui des références (21,7 % par an contre 13,9 % pour SPY), avec une volatilité plus forte (20,9 % par an contre 18,9 % pour SPY et 11,2 % pour le 60/40). Sur 2024 → 2026-09, la stratégie fait moins bien que les deux références. La grille de cinq points n'a pas été lancée, comme prévu : elle ne pouvait plus changer le verdict.

Corrélations hebdomadaires de l'univers ex ante sur la fenêtre principale : 0,67 avec SPY, 0,67 avec le 60/40, 0,68 avec `vt2` et 0,57 avec `aw` (paniers de comparaison de #18904), 0,68 avec la 774, 0,64 avec la [676](../MultiHorizonMomentum676/), 0,78 avec la règle d'origine.

### Ce que la liste fixe apporte

Écart de Sharpe `fixed` − `pit` sur la fenêtre principale, hors verdict : **+0,18** (IC 95 % [−0,21 ; +0,63], p unilatérale 0,18). Il est nul sur 2018-2020 (−0,03), de +0,15 sur 2021-2023, et de +0,55 sur 2024 → 2026-09.

Les positions fermées montrent d'où il vient. Dans la règle d'origine, NVDA porte 49 % du résultat des positions fermées de la poche tendance. Dans l'univers ex ante, ce titre n'entre parmi les 15 plus grandes capitalisations qu'en septembre 2020 : il y porte encore 31 % du résultat, sur une période plus courte. XOM pèse dans l'autre sens. La liste d'origine l'évalue sur toute la fenêtre : elle y gagne 32 000 dollars, dont 33 700 sur les positions fermées en 2021 et 2022, pendant la hausse de l'énergie. L'univers ex ante ne l'évalue que quand il figure parmi les 15 plus grandes capitalisations : il y perd 29 000 dollars, dont 26 600 sur les positions fermées en 2025 et 2026.

### Ce que les journaux et les ordres montrent

1. **Un résultat concentré.** Dans l'univers ex ante, 32 titres sont passés par la poche tendance. Cinq d'entre eux portent 85 % du résultat des positions fermées de cette poche : NVDA, TSLA, MU, FB (devenu META) et GOOGL. MU, acheté pour la première fois en mai 2026, rapporte à lui seul 50 600 dollars de mai à septembre 2026.
2. **BRK.A n'est jamais acheté.** La règle retient la ligne principale de chaque société, donc BRK.A pour Berkshire Hathaway. Il fait partie de la sélection dans chacun des 89 mois journalisés, mais une seule part vaut plus que la position qui lui revient : aucun ordre n'est passé, et son poids reste en liquidités. La règle détient donc de fait au plus 14 titres. L'effet sur le verdict n'est pas mesuré ; une variante qui retiendrait la catégorie d'actions la plus négociable de chaque société le mesurerait.
3. **Journal tronqué.** Le journal de QC est limité à 100 ko par backtest et par jour. Celui de l'univers ex ante s'arrête au 2025-05-01, et les runs suivants de la journée n'en ont pas. Les ordres (`/backtests/orders/read`) et les positions fermées des statistiques QC couvrent toute la fenêtre : les points 1 et 2 en viennent, sauf le décompte des mois de sélection.

### Écart avec les chiffres déjà publiés

Un cinquième run rejoue la règle d'origine (`universe=fixed`) sur la fenêtre du code d'origine, 2015-01-01 → 2025-12-31, pour comparer aux chiffres publiés dans le [catalogue](../README.md) et le [registre comparatif](../../../../docs/qc/qc-comparative-backtests.md). Statistiques QC dans les trois cas :

| Mesure | Catalogue | Registre comparatif | Ce run |
|--------|----------:|--------------------:|-------:|
| Sharpe | 1,155 | 1,14 | 1,15 |
| PSR | — | 77,9 % | 55,7 % |
| CAGR | 27,4 % | 27,1 % | 27,1 % |
| Pire baisse | 27,7 % | 27,7 % | 27,6 % |

Le Sharpe, le CAGR et la pire baisse se reproduisent à 0,01 près ; la PSR publiée ne se reproduit pas. Le chiffre publié était donc juste sur sa fenêtre, et la note de prudence du README d'origine, qui supposait un Sharpe effectif de 0,6 à 0,9, est réfutée sur ce point. Le défaut est ailleurs : la liste des 15 titres a été choisie en 2026, et elle porte sur toute fenêtre antérieure une information que l'algorithme ne pouvait pas avoir. Sur la fenêtre principale, la règle d'origine fait 0,91 (PSR 26,8 %) en statistiques QC, et l'univers ex ante 0,77 (PSR 14,5 %).

### Suivi en ombre

La variante `pit` est gelée à la date du verdict, avec ses paramètres par défaut. Elle est inscrite au registre du suivi en ombre (#18923) après merge, comme les autres stratégies évaluées.

Traces (plans, identifiants de backtest, journaux, ordres, `results.json`) : hors dépôt, dossier `QC-traces/19393-trendweather` du partage du cluster.
