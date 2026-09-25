# Markov-Regime-Detection

**Classe d'actifs :** Actions/ETF américains (SPY, TLT, GLD)
**ID projet Cloud :** `36387308`

## Description

Détection de régime markovien avec `MarkovRegression` de statsmodels. Identifie 2 régimes (haussier/baissier) sur les rendements de SPY, arbitre mensuellement entre SPY (régime calme) et TLT (régime agité), avec une couche GLD constante de 10 %.

**Consolidé depuis ML-HMM-Regime** (copie quasi-identique avec même nom de classe, même `k_regimes=2`, même logique d'allocation).

## Overlay Fear & Greed (v1.2, #15534)

Le projet consolide l'article de recherche QuantConnect [#19465](https://www.quantconnect.com/research/19465/filtering-trades-with-the-fear-and-greed-index/) sous forme d'un **overlay optionnel**, activé par le paramètre `use_feargreed` (défaut `0` = comportement v1.1 strictement inchangé).

**Source primaire** : Huang, Jiang, Tu & Zhou (2015), « Investor Sentiment Aligned: A Powerful Predictor of Stock Returns », *Review of Financial Studies* 28(3), 791-837 — l'indice de sentiment aligné comme prédicteur puissant des rendements. L'article QuantConnect reste le point d'entrée opérationnel, cette référence est la source académique primaire.

**Mécanisme** : le même outil que le régime principal (`MarkovRegression`, `k_regimes=2`) est ajusté sur l'historique glissant de l'indice Fear & Greed, et l'exposition SPY est **réduite de moitié** quand le régime SPY demande du risque mais que le régime de l'indice est dans son état « greedy » (le reste demeure en cash — jamais en TLT, qui mélangerait deux signaux de régime). Le régime « greedy » est identifié par sa **moyenne ajustée** plus élevée, jamais par un numéro de régime codé en dur, pour qu'un renumérotage entre ajustements ne puisse pas inverser silencieusement le filtre.

**Dataset** : `FearGreedIndex`, exposé par le wildcard `AlgorithmImports` (aucun import explicite), ticker `"FG"`. Sonde de disponibilité mesurée sur QC Cloud le 2026-09-11 : ≥ 2500 lignes quotidiennes livrées jusqu'à déc. 2025, couverture depuis juillet 2014, non gated.

**Seeds** : le balayage de seeds de l'article (30-50) n'a pas d'objet ici — l'article tirait des trades aléatoires, alors que cette stratégie est un arbitrage mensuel déterministe dont l'ajustement `MarkovRegression` ne dépend d'aucune graine. La robustesse est donc testée par **sous-périodes de marché** à la place.

## Comment lancer

**QC Cloud :** projet `36387308` (public). Paramètres de la stratégie v1.2 : `use_feargreed` (0/1), `start_year`/`end_year`, `lookback_years` (défaut 3).
Paramètres des bras v1.3 : `arm` (`markov` par défaut, `article`, `fixed`, `static`, `spy`), `seed` (défaut 0), `start_date`/`end_date` (défaut : fenêtre de l'article), `static_gld` (défaut 0,545), `history_lookback` (défaut 50 semaines), `drawdown_lookback` (défaut 20 semaines).
**Mesures v1.3 :** `python bench_drawdown_hmm.py fetch|stats|markdown` (identifiants QC lus dans les variables d'environnement `QC_API_USER_ID` et `QC_API_ACCESS_TOKEN`).
**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Markov-Regime-Detection"`

## Métriques de backtest

Mesurées le 2026-09-11 sur QC Cloud, frais Interactive Brokers conservés dans les deux bras (contrairement à l'article, qui les supprimait par `ConstantFeeModel(0)`), réajustement mensuel. Le bras A est la baseline (`use_feargreed=0`), le bras B la variante (`use_feargreed=1`) ; chaque fenêtre est un run indépendant (pas une tranche du run complet), le réchauffement de 3 ans et l'état de régime n'étant pas reportés d'une fenêtre à l'autre.

| Fenêtre | Bras | Sharpe | CAGR | MaxDD | Profit net | Profit net ($) | PSR | Ordres |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| 2015-2026 | A — baseline | 0.290 | 7.182 % | 23.700 % | 114.572 % | 74 574.09 | 0.197 % | 103 |
| 2015-2026 | B — variante | 0.019 | 3.318 % | 26.300 % | 43.243 % | 23 093.34 | 0.004 % | 105 |
| IS 2015-2020 | A — baseline | 0.229 | 4.735 % | 16.700 % | 26.038 % | 14 496.06 | 1.859 % | 44 |
| IS 2015-2020 | B — variante | 0.051 | 2.653 % | 14.500 % | 13.996 % | 7 532.51 | 0.526 % | 45 |
| OOS 2021-2026 | A — baseline | 0.297 | 8.991 % | 23.700 % | 53.825 % | 26 626.13 | 2.596 % | 41 |
| OOS 2021-2026 | B — variante | −0.123 | 3.278 % | 22.500 % | 17.510 % | 2 344.36 | 0.121 % | 42 |

**Verdict : NO BEATS sur les trois fenêtres.** L'overlay dégrade le Sharpe (jusqu'à le rendre négatif en OOS), le CAGR et le profit net partout. La seule métrique où B fait mieux est le MaxDD en IS (14.500 % contre 16.700 %), conséquence mécanique d'une exposition réduite de moitié et non d'un meilleur signal. Le nombre d'ordres est quasi identique dans chaque fenêtre (103/105, 44/45, 41/42), ce qui est le comportement attendu d'un overlay qui ne modifie que le **poids** d'exposition et jamais la fréquence de décision — le turnover n'étant pas exposé par l'outil de lecture (qc-mcp-lite mappe six statistiques), le nombre d'ordres en est le proxy déclaré.

## Couverture or par régime de drawdown (v1.3, #17589)

Le projet consolide l'article de recherche QuantConnect [#18811](https://www.quantconnect.com/research/18811/optimizing-a-gold-spy-portfolio-using-hidden-markov-models-for-market-downtime/) (Louis Szeto) sous forme de **bras optionnels**, sélectionnés par le paramètre `arm`. La valeur par défaut `arm=markov` exécute la stratégie v1.2 sans aucun changement : la branche v1.3 quitte `initialize` avant la configuration v1.2, et le diff de `main.py` ne contient que des insertions.

**Mécanisme de l'article** : chaque début de semaine, un `GMMHMM` (hmmlearn) à 2 états, 3 composantes de mélange par état et covariance `tied` est ajusté sur deux entrées tirées de 50 semaines de clôtures de SPY : le drawdown glissant sur 20 semaines et sa différence première. Le poids de GLD vaut la probabilité que la semaine suivante soit dans l'état « high », et SPY reçoit le complément. Compte de 1 M$, données minute, frais par défaut de la plateforme (modèle Interactive Brokers), conservés dans tous les bras.

**Sources primaires** :

- Rabiner, L. R. (1989). *A tutorial on hidden Markov models and selected applications in speech recognition*. Proceedings of the IEEE 77(2), 257-286 : modèle de Markov caché, algorithme forward-backward.
- McLachlan, G. J. & Peel, D. (2000). *Finite Mixture Models*. Wiley : mélanges gaussiens finis, cités par l'article pour approcher une loi non gaussienne.
- Balkema, A. A. & de Haan, L. (1974). *Residual life time at great age*. Annals of Probability 2(5), 792-804 ; Pickands, J. (1975). *Statistical inference using extreme order statistics*. Annals of Statistics 3(1), 119-131. Le théorème de Pickands-Balkema-de Haan justifie une loi de Pareto généralisée pour les dépassements de seuil, donc une queue non gaussienne pour les drawdowns. Il justifie la forme de la loi, pas l'allocation SPY/GLD, qui reste la contribution propre de l'article.
- Ledoit, O. & Wolf, M. (2008). *Robust performance hypothesis testing with the Sharpe ratio*. Journal of Empirical Finance 15(5), 850-859 : test d'écart de ratios de Sharpe robuste à l'autocorrélation (HAC), utilisé pour les comparaisons ci-dessous.

**Quatre bras**, pour isoler ce que chaque élément apporte :

| `arm` | Ce qu'il mesure |
|---|---|
| `article` | port fidèle, étiquetage des états compris |
| `fixed` | même modèle et même sizing ; l'état « high » est celui dont le drawdown moyen, pondéré par les poids de mélange, est le plus bas (le plus profond) |
| `static` | poids GLD constant (`static_gld`) sur le même calendrier hebdomadaire. Deux témoins : 0,545, le poids GLD moyen réalisé par le bras `article`, et 0,450, celui du bras `fixed` (moyennes sur 5 graines, fenêtre complète). À exposition moyenne égale, le témoin sépare le *timing* d'une simple allocation à l'or |
| `spy` | SPY en buy-and-hold, même compte et même calendrier |

Les bras HMM tournent sur les graines 0, 1, 7, 42 et 99 (`seed`, qui remplace le `random_state=0` de l'article ; la graine 0 est l'article).

**Étiquetage des états dans le code de l'article** : `high_regime = 1 if model.means_[0][1][0] < model.means_[1][1][0] else 0`. `means_` a la forme `(états, composantes, variables)` : la comparaison lit la **composante de mélange d'index 1** de chaque état, dont l'ordre est arbitraire à chaque ajustement, et retient l'état dont la moyenne est la plus **haute**. Comme un drawdown est négatif ou nul, cet état est celui du drawdown le **plus faible**. Le bras `fixed` corrige les deux points ; `main.py` compte à chaque ajustement si les deux étiquettes coïncident (statistique d'exécution `Label agreement`).

### Protocole de mesure

- **Reproduction** : avec ses paramètres par défaut (fenêtre de l'article, du 2019-01-03 au 2025-01-01), le bras `article` rend un Sharpe QC de 0,824, pour 0,823 publié dans l'article.
- **Fenêtre étendue** : chaque bras tourne ensuite du 2008-01-01 au 2026-09-01. La fenêtre de l'article en devient une sous-période (in-sample, puisque c'est sur elle que la méthode a été présentée), encadrée de deux périodes hors échantillon : 2008-2018, qui couvre la crise de 2008, et 2025-2026.
- **Rendements mensuels** : `main.py` trace chaque mois le rendement du portefeuille, de SPY et de GLD, ainsi que l'exposition nette et le poids GLD moyens ; `bench_drawdown_hmm.py fetch` les relit depuis la plateforme. LEAN ne rémunère pas le cash : le rendement en excès vaut `R − exposition nette × rf`, avec rf le taux du bon du Trésor à 3 mois (série FRED TB3MS).
- **Tests** : écart de Sharpe annualisé contre SPY et contre le témoin statique de la même famille, test HAC de Ledoit-Wolf par graine ; alpha CAPM avec erreurs-types de Newey-West ; cinq tranches chronologiques de même longueur (walk-forward descriptif : le modèle est réajusté chaque semaine sur une fenêtre glissante, aucun paramètre n'est calibré sur la période testée).
- **Règle de verdict** : BEATS exige un écart moyen positif supérieur à deux écarts-types inter-graines **et** des écarts significatifs à 5 % ; NO BEATS quand l'écart est négatif ou nul sur les graines ; INCONCLUSIVE sinon.

### Résultats

Statistiques de la plateforme, un backtest par ligne :

| Backtest QC | paramètres | Sharpe | CAGR | MaxDD | ordres | frais |
|---|---|---:|---:|---:|---:|---:|
| `repro_article_s0` | arm=article, seed=0 | 0.824 | 19.751% | 27.100% | 414 | $4118.01 |
| `spy` | arm=spy, end_date=2026-09-01, start_date=2008-01-01 | 0.451 | 11.418% | 51.300% | 3 | $51.55 |
| `article_s0` | arm=article, end_date=2026-09-01, seed=0, start_date=2008-01-01 | 0.42 | 10.392% | 44.900% | 1297 | $17972.98 |
| `article_s1` | arm=article, end_date=2026-09-01, seed=1, start_date=2008-01-01 | 0.405 | 10.147% | 47.700% | 1281 | $14108.70 |
| `article_s7` | arm=article, end_date=2026-09-01, seed=7, start_date=2008-01-01 | 0.351 | 8.594% | 35.200% | 1749 | $27101.77 |
| `article_s42` | arm=article, end_date=2026-09-01, seed=42, start_date=2008-01-01 | 0.441 | 10.593% | 30.000% | 1651 | $34640.75 |
| `article_s99` | arm=article, end_date=2026-09-01, seed=99, start_date=2008-01-01 | 0.379 | 9.701% | 47.700% | 1109 | $10440.29 |
| `fixed_s0` | arm=fixed, end_date=2026-09-01, seed=0, start_date=2008-01-01 | 0.491 | 10.637% | 48.700% | 1284 | $18882.27 |
| `fixed_s1` | arm=fixed, end_date=2026-09-01, seed=1, start_date=2008-01-01 | 0.466 | 10.253% | 37.600% | 1268 | $20639.31 |
| `fixed_s7` | arm=fixed, end_date=2026-09-01, seed=7, start_date=2008-01-01 | 0.45 | 9.931% | 46.600% | 1748 | $28059.23 |
| `fixed_s42` | arm=fixed, end_date=2026-09-01, seed=42, start_date=2008-01-01 | 0.434 | 9.690% | 45.500% | 1645 | $25270.37 |
| `fixed_s99` | arm=fixed, end_date=2026-09-01, seed=99, start_date=2008-01-01 | 0.483 | 10.670% | 38.400% | 1100 | $15354.37 |
| `static_article` | arm=static, end_date=2026-09-01, start_date=2008-01-01, static_gld=0.545 | 0.535 | 10.666% | 32.100% | 1456 | $1562.34 |
| `static_fixed` | arm=static, end_date=2026-09-01, start_date=2008-01-01, static_gld=0.45 | 0.545 | 10.937% | 34.100% | 1457 | $1563.25 |

Sharpe en excès annualisé, calculé sur les rendements mensuels ; écarts moyens sur les 5 graines, ± écart-type inter-graines, et nombre de graines dont l'écart est positif et significatif à 5 % :

| Fenêtre | mois | corr. SPY/GLD | spy | static 0,545 | static 0,450 | article (moy. 5 graines) | fixed (moy. 5 graines) | Δ article − spy (moy. ± σ graines) | Δ article − static 0,545 (moy. ± σ) | Δ fixed − static 0,450 (moy. ± σ) |
|---|---:|---:|---:|---:|---:|---:|---:|---|---|---|
| 2008-01 → 2026-08 (tout) | 224 | 0,08 | 0,69 | 0,79 | 0,82 | 0,61 | 0,66 | −0,08 ± 0,04 (0/5 p<0,05) | −0,18 ± 0,04 (0/5 p<0,05) | −0,16 ± 0,03 (0/5 p<0,05) |
| 2008-01 → 2018-12 (hors échantillon, avant l'article) | 132 | 0,01 | 0,53 | 0,51 | 0,56 | 0,29 | 0,52 | −0,24 ± 0,09 (0/5 p<0,05) | −0,22 ± 0,09 (0/5 p<0,05) | −0,03 ± 0,08 (0/5 p<0,05) |
| 2019-01 → 2024-12 (fenêtre de l'article, in-sample) | 72 | 0,23 | 0,86 | 1,02 | 1,02 | 0,98 | 0,70 | 0,12 ± 0,21 (0/5 p<0,05) | −0,04 ± 0,21 (0/5 p<0,05) | −0,33 ± 0,12 (0/5 p<0,05) |
| 2025-01 → 2026-08 (hors échantillon, après l'article) | 20 | 0,03 | 1,10 | 1,69 | 1,73 | 1,36 | 1,63 | 0,27 ± 0,27 (0/5 p<0,05) | −0,34 ± 0,27 (0/5 p<0,05) | −0,11 ± 0,39 (0/5 p<0,05) |

Cinq tranches chronologiques de même longueur (Sharpe en excès, moyenne des 5 graines pour les bras HMM) :

| Tranche | spy | static 0,545 | static 0,450 | article | fixed |
|---|---:|---:|---:|---:|---:|
| 2008-01 → 2011-09 | −0,11 | 0,61 | 0,48 | 0,33 | 0,60 |
| 2011-10 → 2015-06 | 1,80 | 0,38 | 0,65 | 0,46 | 0,29 |
| 2015-07 → 2019-03 | 0,85 | 0,69 | 0,81 | 0,24 | 0,72 |
| 2019-04 → 2022-12 | 0,54 | 0,73 | 0,71 | 0,78 | 0,36 |
| 2023-01 → 2026-08 | 1,32 | 1,64 | 1,70 | 1,34 | 1,61 |

Exposition et alpha CAPM sur la fenêtre complète :

| Bras (fenêtre complète) | poids GLD moyen | CAGR | MaxDD mensuel | alpha CAPM annualisé (t NW) | bêta SPY |
|---|---:|---:|---:|---:|---:|
| `article_s0` | 0,56 | 10,6 % | 39,1 % | 3,2 % (1,09) | 0,64 |
| `article_s1` | 0,54 | 10,3 % | 42,3 % | 2,7 % (0,96) | 0,67 |
| `article_s42` | 0,54 | 10,8 % | 22,3 % | 4,0 % (1,32) | 0,57 |
| `article_s7` | 0,54 | 8,8 % | 26,4 % | 3,0 % (1,17) | 0,48 |
| `article_s99` | 0,55 | 9,9 % | 45,5 % | 2,7 % (0,92) | 0,62 |
| `fixed_s0` | 0,44 | 10,7 % | 42,1 % | 5,2 % (1,68) | 0,44 |
| `fixed_s1` | 0,46 | 10,3 % | 33,5 % | 5,1 % (1,74) | 0,41 |
| `fixed_s42` | 0,46 | 9,7 % | 37,9 % | 3,7 % (1,28) | 0,50 |
| `fixed_s7` | 0,45 | 10,0 % | 43,3 % | 3,9 % (1,34) | 0,50 |
| `fixed_s99` | 0,45 | 10,7 % | 34,4 % | 5,0 % (1,52) | 0,46 |
| `spy` | 0,00 | 11,5 % | 46,1 % | 0,2 % (1,05) | 0,99 |
| `static_article` | 0,54 | 10,8 % | 24,7 % | 4,4 % (2,14) | 0,50 |
| `static_fixed` | 0,45 | 11,0 % | 25,8 % | 3,7 % (2,17) | 0,58 |

Diagnostics du modèle de régime (identiques pour `article` et `fixed`, qui ajustent le même modèle avec la même graine) :

| Graine | ajustements | échecs avalés | étiquette de l'article = état à drawdown profond |
|---|---:|---:|---:|
| 0 | 970 | 4 | 6,7 % |
| 1 | 973 | 1 | 5,1 % |
| 7 | 972 | 2 | 20,1 % |
| 42 | 956 | 18 | 13,8 % |
| 99 | 967 | 7 | 1,2 % |

**Verdicts** :

- **Fenêtre complète (2008-2026) : NO BEATS**, contre SPY comme contre l'or statique. Les dix backtests HMM ont un Sharpe en excès inférieur à celui de leur témoin statique : de −0,13 à −0,22 pour `article`, de −0,12 à −0,19 pour `fixed`. Aucun écart individuel n'est significatif à 5 % (p de 0,07 à 0,43), mais le signe ne dépend d'aucune graine. Contre SPY, les écarts sont négatifs ou nuls (−0,08 ± 0,04 et −0,03 ± 0,03).
- **Fenêtre de l'article (2019-2024) : INCONCLUSIVE** contre SPY pour `article` (+0,12 ± 0,21, de −0,23 à +0,29 selon la graine, aucune significative) : l'écart publié se reproduit avec la graine de l'article mais ne résiste pas au changement de graine. Contre le témoin statique, l'écart moyen est de −0,04 : sur sa propre fenêtre, l'avantage de la stratégie tient à la part d'or, pas au timing.
- **Hors échantillon avant l'article (2008-2018) : NO BEATS** (`article` −0,24 ± 0,09 contre SPY, écart négatif sur les cinq graines).
- **Hors échantillon après l'article (2025-2026, 20 mois) : INCONCLUSIVE** contre SPY (+0,27 ± 0,27 pour `article`, +0,54 ± 0,39 pour `fixed`, aucune graine significative sur une période aussi courte), et négatif contre le témoin statique (−0,34 et −0,11 en moyenne).

**Ce que mesure l'étiquetage de l'article** : l'étiquette de l'article ne désigne l'état à drawdown profond que dans 1,2 % à 20,1 % des ajustements selon la graine. Dans la grande majorité des semaines, le poids de GLD est donc la probabilité de l'état à drawdown **faible** : la stratégie achète de l'or en marché calme, à l'opposé de l'intention décrite. Corriger l'étiquette (`fixed`) améliore le Sharpe en excès de la fenêtre complète (0,66 contre 0,61 en moyenne) sans rattraper le témoin statique.

**D'où vient le rendement** : l'alpha CAPM des bras HMM (de 2,7 % à 5,2 % par an, t de Newey-West inférieur à 1,8) est du même ordre que celui des deux témoins statiques (4,4 % et 3,7 %, les seuls avec t > 2). C'est la détention d'or, peu corrélée à SPY sur la période (corrélation mensuelle 0,08), qui porte la performance. Le timing, lui, coûte : des poids presque binaires d'une semaine à l'autre augmentent le MaxDD mensuel (de 22 % à 45 % contre 25 % à 26 % pour les témoins) et multiplient les frais (de 10 k$ à 35 k$ contre 1,6 k$ pour l'or statique). Le bêta SPY plus faible du bras `fixed` (0,41 à 0,50 contre 0,58 pour son témoin) est l'effet attendu d'un repli vers l'or pendant les drawdowns, mais il ne compense pas la volatilité ajoutée.

**Limites** : les tests d'écart portent sur des rendements mensuels (224 mois) ; au plus 18 ajustements par backtest échouent et sont avalés comme dans l'article, qui garde alors les positions de la semaine précédente (colonne « échecs avalés »).

## Fichiers

- `main.py` - Stratégie (v1.3 : régime markovien + overlay Fear & Greed optionnel + bras de couverture or par régime de drawdown)
- `bench_drawdown_hmm.py` - Relecture des backtests v1.3, statistiques et tableaux de cette page
- `measures/` - Identifiants des backtests, statistiques QC, rendements mensuels et synthèse des tests
- `README.en.md` - Version anglaise
