# Trend Following — `TrendFollowingAQR` v7

**Classe d'actifs :** ETF multi-actifs (actions US/EU/EM, obligations, or, matières)
**Cloud project ID :** 28797562
**Période backtestée :** 2015-01-01 → 2024-12-31

## Description

Stratégie de **trend-following multi-actifs** (style Antonacci 2014 / AQR Trend Followinging) déployée comme `main.py`. L'algorithme combine un **double signal de momentum** et un **régime baissier de safe-haven** :

- **Filtre de tendance** : pour chaque actif risqué, on exige `prix > SMA(200)` (la tendance de fond est haussière).
- **Confirmation momentum** : le rendement glissant 6 mois (`ret_6m > 0`) doit confirmer.
- **Pondération par rang** : les actifs retenus sont classés par rendement 12 mois ; le poids est proportionnel au rang (l'actif le plus fort surperforme).
- **Régime baissier** : si `SPY < SMA(200)`, le portefeuille bascule — le risqué est plafonné à 50 % et les 50 % restants vont dans le safe-haven `BND` (obligations). En marché haussier, 100 % risqué.

**Univers** : `SPY, EFA, EEM, TLT, GLD, DBC` (risqué) + `BND` (safe-haven). Rebalancement **mensuel** (ouverture du premier jour ouvré, +30 min).

Mesurée contre deux références détenues, la stratégie est `NO BEATS` sur 2015-2024 et `INCONCLUSIVE` sur 2025-2026, et le régime baissier n'améliore pas son Sharpe de façon mesurable (section « Verdict contre références détenues (#22959) »). La docstring attribue à la v7 un Sharpe de 0,577 sans dire sur quelle fenêtre ; la fenêtre codée ne le reproduit ni en Sharpe QC (0,362) ni en Sharpe à taux nul (0,715), et cet écart n'est pas instruit ici.

## Backtest réel (QC Cloud, frais IBKR margin inclus)

| Métrique | Valeur |
|----------|--------|
| Sharpe ratio | **0.36** |
| CAGR | **7.29 %** |
| Drawdown max | **15.00 %** |
| Rendement total net | 102.3 % |
| PSR (Probabilistic Sharpe Ratio) | **0.676 %** |
| Ordres exécutés | 451 |
| Jours tradés | 2516 |

*Mesure du 2026-10-27 : backtest du code de `main`, inchangé, lancé sur QC Cloud comme contrôle de la mesure #22959 (fenêtre codée, paramètres par défaut). La mesure du 2026-08-06 donnait 454 ordres et un PSR de 0,659 % : les prix ajustés de QC changent d'une mesure à l'autre.*

### Lecture honnête — beta gérée, pas alpha

Le **PSR à 0,68 %** est sans ambiguïté : la probabilité que le ratio de Sharpe observé soit **statistiquement supérieur à zéro** est quasi nulle. Autrement dit, malgré un rendement absolu positif (CAGR 7.29 %) et un drawdown contenu (15 %), **cette stratégie ne démontre aucune compétence (skill) statistiquement significative**.

Ce résultat est **cohérent et pédagogiquement sain** : TrendFollowingAQR est une stratégie de **beta de marché géré**, pas d'alpha. Sur la décennie 2015-2024, elle rend moins que SPY détenu (CAGR QC 7,29 % contre 12,97 %), avec une pire baisse plus faible (15,0 % contre 33,7 %).

Cette section attribuait la pire baisse plus faible à la bascule vers `BND` en marché baissier, au premier trimestre 2020 et en 2022. La mesure #22959 ne le confirme qu'en partie. Dans l'année 2020 et dans l'année 2022, le régime réduit la baisse (10,9 % contre 13,9 % sans régime, puis 13,5 % contre 14,9 %), mais il coûte du rendement sur ces mêmes années (+21,6 % contre +24,6 %, puis un rendement à peu près nul contre +4,0 %). Sur la décennie, la pire baisse est la même avec ou sans régime (15,0 %, atteinte le 26 août 2015, hors de tout régime baissier), et le Sharpe à taux nul est voisin (0,715 contre 0,725, écart non significatif). La pire baisse plus faible que celle de SPY vient du reste de la règle, que la mesure ne sépare pas davantage : les sept ETF détenus à poids égal, sans filtre ni sélection, ont déjà une pire baisse de 19,3 %. Ces baisses sont calculées sur la valeur du portefeuille à l'ouverture de chaque séance, sans test.

**Conclusion honnête** : ne PAS présenter cette stratégie comme génératrice d'alpha. C'est un **exemple pédagogique de gestion de risque systématique** — un beta de marché diversifié et filtré par la tendance ; le régime baissier qu'elle porte n'a d'effet mesurable ni sur son Sharpe ni sur sa pire baisse de la décennie. Le rendement positif s'explique par l'exposition au marché (beta), pas par une capacité prédictive (le PSR le confirme). À rapprocher de l'Option-Wheel et de l'EMA-Cross-Stocks : même famille pédagogique de « stratégies qui rendent au marché, pas qui le battent ».

## Verdict contre références détenues (#22959)

Le protocole a été écrit dans #22959 avant le premier backtest, sur le modèle de #21594, repris par #22828, #22869 et #22923. Les deux références du verdict, SPY détenu et le 60/40 (SPY 60 %, BND 40 %), tournent dans le même algorithme que la stratégie, sous le même modèle de courtage. Deux diagnostics ne comptent pas dans le verdict :

- `ew7`, les sept ETF du code à poids égal, rééquilibrés chaque mois : la sélection et la pondération ajoutent-elles quelque chose à la détention des sept ETF ?
- `nobear`, la même règle avec le régime baissier désactivé (SPY n'est jamais déclaré sous sa moyenne de 200 séances) : le régime ajoute-t-il quelque chose ?

Le paramètre `mode` choisit le portefeuille. En mode `strategy`, la décision du code ne change pas. Les sept ETF sont déjà abonnés par le code, BND compris : aucun mode n'ajoute d'abonnement.

Propriétés du code, gardées telles quelles :

- **les poids visés somment à 1 et aucun n'est négatif**, mais le compte est déclaré sur marge et le code ne renvoie pas les achats refusés. Aucun ordre n'a été refusé (statut `Invalid`) sur les douze backtests ;
- **le préchauffage de 300 jours calendaires suffit à la moyenne de 200 séances** : la première décision de chaque fenêtre est déjà investie dans les ETF risqués (SPY 33,2 % et TLT 67,1 % le 2015-01-02 ; GLD 67,2 % et SPY 32,7 % le 2025-01-02, en part de la valeur du portefeuille après remplissage) ;
- les ordres de la stratégie sont soumis à 10 h, heure de New York, 30 minutes après l'ouverture, et remplis à la clôture du jour (`MarketOnClose`). Ceux des références partent à 9 h 31 et sont aussi remplis à la clôture. Le filtre de tendance et le régime lisent la clôture de la veille.

Les fenêtres sont coupées au 1er janvier 2025, date de fin du code. La docstring classe trois versions (« v8 : worse », « v9 : worse ») sans dire sur quelle fenêtre : la fenêtre 1 recouvre, au moins en partie, l'échantillon sur lequel la v7 a été retenue ; la fenêtre 2 commence à la date de fin codée.

Les séries comparées sont la valeur du portefeuille à chaque ouverture de SPY. Les tests passent par `Paradox46Benchmarks/significance.py`, avec un taux sans risque nul :

- écart de Sharpe de Ledoit-Wolf ;
- bootstrap stationnaire ;
- écart de moyennes de Newey-West.

Sur chaque fenêtre, la correction de Holm porte sur les six p-valeurs du verdict. Les diagnostics sont une exécution séparée, avec leur propre correction de Holm sur six p-valeurs.

Règle de verdict, écrite avant la mesure :

- `BEATS` : écart de Sharpe positif et significatif (Holm < 0,05, Ledoit-Wolf) contre les deux références ;
- `NO BEATS` : Sharpe de la stratégie inférieur à celui de SPY détenu ;
- `INCONCLUSIVE` : tous les autres cas.

**Contrôle d'innocuité : tenu.** En mode `strategy`, sur la fenêtre codée (2015-01-01 → 2024-12-31), le code instrumenté (backtest `dd791beaa55fadf85d3ce0f5cc60c6f2`, projet 38527905) reproduit le backtest du code d'origine (`82c5da38456d3b38d73366273434e027`, projet 38527898), lancé le même jour :

- 451 ordres sur 451, sans écart de date, de symbole ni de quantité ;
- 27 statistiques QC sur 27, et 8 statistiques d'exécution sur 8.

Ces statistiques sont celles du premier tableau de ce README. L'ancienne ligne du registre `docs/qc/qc-strategies-status.md` (Sharpe QC 0,407, CAGR 7,89 %, pire baisse 14,6 %, PSR 8,68 %) ne se reproduit pas sur ce code.

| Fenêtre | Séances | Sharpe stratégie (taux nul) | SPY détenu (taux nul) | 60/40 (taux nul) | p Holm (Ledoit-Wolf, SPY / 60/40) | Verdict |
|---|---|---|---|---|---|---|
| 1, 2015-01-02 → 2024-12-31 | 2516 | 0,715 | 0,786 | 0,802 | 1,0 / 1,0 | **NO BEATS** |
| 2, 2025-01-02 → 2026-07-01 | 374 | 1,593 | 1,080 | 1,224 | 1,0 / 1,0 | **INCONCLUSIVE** |

Statistiques QC (calculées par QC avec son propre taux sans risque). Leurs Sharpe ne se comparent pas à ceux de la table du dessus : QC retranche un taux sans risque non nul et part de ses propres séries quotidiennes, alors que le protocole prend un taux nul sur la valeur du portefeuille à l'ouverture. Le verdict se lit sur la table du dessus.

| Fenêtre | Mode | Sharpe QC (taux de QC, autre échelle) | CAGR | Pire baisse | Volatilité annuelle (QC) | Ordres | Backtest |
|---|---|---|---|---|---|---|---|
| 1 | stratégie | 0,362 | 7,29 % | 15,0 % | 8,9 % | 451 | `ca8435b0a9b7f5b12860dbf501cca1da` |
| 1 | SPY détenu | 0,533 | 12,97 % | 33,7 % | 14,6 % | 1 | `095212aecc61a05f39baae2d65434566` |
| 1 | 60/40 | 0,442 | 8,41 % | 21,7 % | 9,0 % | 201 | `44b67213258d1be9583cb7af800f43cb` |
| 1 | 7 ETF à poids égal | 0,210 | 5,12 % | 19,3 % | 7,9 % | 534 | `b84302a36c6f43073e3513f4d802cc2e` |
| 1 | régime désactivé | 0,394 | 8,07 % | 15,0 % | 9,7 % | 441 | `e69505da172f57cce8a16f1ea09be972` |
| 2 | stratégie | 0,982 | 21,50 % | 9,2 % | 11,2 % | 77 | `03fcbf4f885a5537f3857b3d671f2bf2` |
| 2 | SPY détenu | 0,665 | 18,96 % | 18,7 % | 14,7 % | 2 | `5d8d74a39c9e973ade3ae4e7cb53f346` |
| 2 | 60/40 | 0,590 | 13,37 % | 11,2 % | 9,1 % | 30 | `eaeb376257875af6cc32f61ade4cf3ba` |
| 2 | 7 ETF à poids égal | 1,127 | 20,34 % | 8,0 % | 8,8 % | 83 | `b40421ab3077010ebe23cbfdd72b8644` |
| 2 | régime désactivé | 1,084 | 25,26 % | 9,3 % | 12,6 % | 71 | `4442711057c51f88007b668de327aba4` |

Le backtest de la fenêtre 2 va jusqu'à sa date codée : sa dernière séance est le 2026-07-01, et la coupure d'environ 90 jours que les nœuds QC utilisés appliquent à la fin des backtests ne l'a pas atteint. Sur ses 374 séances, la fenêtre a peu de puissance. Ses deux références, et les sept ETF à poids égal sur les deux fenêtres, reproduisent ceux des mesures #22828, #22869 et #22923, lancés dans d'autres algorithmes : mêmes Sharpe à taux nul et mêmes statistiques QC.

**Lecture.** Sur la fenêtre 1, la stratégie a un Sharpe ponctuel inférieur à celui de SPY détenu (0,715 contre 0,786) et à celui du 60/40 (0,802) : selon la règle écrite avant la mesure, le verdict est `NO BEATS`. Aucun des six tests n'est significatif (p de Holm 0,94 pour l'écart de moyennes contre SPY détenu, 1,0 pour les cinq autres), et l'intervalle bootstrap à 95 % de l'écart de Sharpe contre SPY détenu va de −0,66 à +0,53. Sur la fenêtre 2, son Sharpe ponctuel dépasse celui des deux références (1,593 contre 1,080 et 1,224), sans aucun écart significatif (p de Holm 1,0, intervalle bootstrap de −1,26 à +2,20 contre SPY détenu) : le verdict est `INCONCLUSIVE`. La stratégie est peu corrélée à ses références (0,40 avec SPY détenu et 0,46 avec le 60/40 sur la fenêtre 1).

**Diagnostic : le régime baissier n'améliore pas le Sharpe de façon mesurable ; l'apport de la sélection reste ouvert sur la fenêtre 1 et manque sur la fenêtre 2.**

| Fenêtre | Diagnostic | Sharpe du diagnostic (taux nul) | Écart stratégie − diagnostic | Intervalle bootstrap 95 % | p Holm (Ledoit-Wolf) | Corrélation | Lecture |
|---|---|---|---|---|---|---|---|
| 1 | 7 ETF à poids égal | 0,577 | +0,138 | −0,32 à +0,62 | 1,0 | 0,66 | question ouverte |
| 1 | régime désactivé | 0,725 | −0,010 | −0,10 à +0,08 | 1,0 | 0,97 | rien de mesurable |
| 2 | 7 ETF à poids égal | 1,865 | −0,272 | −1,13 à +0,67 | 1,0 | 0,87 | rien de mesurable |
| 2 | régime désactivé | 1,636 | −0,043 | −0,32 à +0,32 | 1,0 | 0,97 | rien de mesurable |

Sur les deux fenêtres, la règle sans régime baissier a un Sharpe à taux nul un peu supérieur à celui de la stratégie, pour des séries corrélées à 0,97. Sur la valeur à l'ouverture, la pire baisse est la même avec ou sans régime sur la fenêtre 1 (15,0 %, atteinte le 2015-08-26) et voisine sur la fenêtre 2 (9,2 % contre 9,3 %, atteinte le 2026-03-27). Le régime réduit la baisse dans l'année 2020 et dans l'année 2022, au prix d'un rendement plus faible sur ces mêmes années (section « Lecture honnête »). Sur la fenêtre 1, la stratégie dépasse les sept ETF détenus à poids égal (0,715 contre 0,577) sans que l'écart soit significatif : la question reste ouverte. Sur la fenêtre 2, elle fait moins bien qu'eux (1,593 contre 1,865), sans écart significatif non plus.

**Prédictions écrites avant la mesure :**

- contrôle d'innocuité tenu : juste ;
- fenêtre 1, aucun écart significatif contre l'une ou l'autre référence, donc `INCONCLUSIVE` ou `NO BEATS` : juste (`NO BEATS`) ;
- diagnostic `ew7` sur la fenêtre 1, Sharpe de la stratégie supérieur sans écart significatif : juste ;
- diagnostic `nobear` sur la fenêtre 1, écart non significatif : juste. Son signe, non prédit, est négatif ;
- diagnostic `nobear` sur la fenêtre 1, pire baisse QC de la stratégie inférieure à celle de la règle sans régime : faux, les deux sont à 15,0 % ;
- fenêtre 2 : pas de prédiction.

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Trend-Following"`
**QC Cloud :** Déployé comme projet 28797562 (paramètre optionnel `brokerage` : `ibkr` défaut avec frais réels, `none` pour frais nuls — utile pour isoler l'effet des frais).

Trois paramètres servent à la mesure #22959 : `mode` (`strategy` par défaut, `spy`, `6040`, `ew7`, `nobear`), `start_date` et `end_date` (format `AAAA-MM-JJ`, par défaut les dates codées, 2015-01-01 et 2024-12-31).

## Architecture

- **`main.py`** — Algorithme déployé (`TrendFollowingAQR` v7). Auto-contenu : univers fixe 6+1 ETF, double signal SMA(200)+momentum 6m/12m, régime baissier safe-haven, rebalancement mensuel. C'est le fichier backtesté ci-dessus.
- `alpha.py`, `macd_oracle.py`, `rsi_oracle.py`, `bollinger_oracle.py`, `trendCalculator.py` — **Fichiers orphelins** (architecture multi-oracles d'une version antérieure, non importés par `main.py` actuel). Conservés tels quels ; nettoyable dans une PR dédiée.
- `quantbook.ipynb` — Recherche (analyse des signaux).
- `config.json`, `trend_following_analysis.png` — Config et figure d'analyse.

## Concepts enseignés

- **Double momentum** (Antonacci) : filtre de tendance `SMA(200)` + confirmation momentum `6m`.
- **Pondération par rang** (rank-based) plutôt que par pondération naive égale.
- **Régime de marché / safe-haven switch** : détection baissière (`SPY < SMA(200)`) → réallocation défensive vers obligations.
- **Backtesting avec frais réels** (IBKR margin) vs frais nuls — isoler l'impact des coûts de transaction.
- **Probabilistic Sharpe Ratio (PSR)** : distinguer un rendement positif d'une compétence statistiquement significative (leçon clé : CAGR 7.29 % ≠ skill si PSR ≈ 0).
