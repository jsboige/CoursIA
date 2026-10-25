# ML-XGBoost — Gradient Boosting sur grandes capitalisations US (régresseur de rendement)

**Classe d'actifs :** Actions US grandes capitalisations (15 titres)
**Cloud project ID :** 29434753
**Période backtestée :** 2015-01-01 → 2024-12-31

## Description

Stratégie de **régression par Gradient Boosting** (sklearn `GradientBoostingRegressor`) sur 15 grandes capitalisations US liquides. **Différence majeure vs ML-RandomForest et ML-SVM** : le modèle prédit le **rendement futur à 10 jours** (valeur continue, régression), pas le **signe** du rendement (classification). Utilise 23 features techniques (RSI, bandes de Bollinger, MACD, stochastique, ATR, momentum, volatilité, volume, ratios prix/SMA).

Entraînement bimensuel (un lundi sur deux, alterné avec le rebalancement). Le modèle est **pooled** (un seul régresseur entraîné sur les 15 tickers réunis), 9 positions max, allocation 90 %.

**Note d'honnêteté sur le nom** : malgré le nom du répertoire « ML-XGBoost », le code déployé utilise `sklearn.ensemble.GradientBoostingRegressor` (J. Friedman, 2001), **pas** la bibliothèque `xgboost` (Chen & Guestrin, 2016). Les deux implémentent le gradient boosting mais diffèrent (gestion des valeurs manquantes, objectif régularisé, vitesse). La référence Friedman 2001 citée plus bas correspond bien à l'implémentation réelle.

**Version anglaise préservée** : [README.en.md](README.en.md).

## Configuration déployée (v2, `main.py` Cloud 29434753)

| Composant | Paramètre | Rôle |
|-----------|-----------|------|
| Univers | AAPL, MSFT, GOOGL, AMZN, NVDA, META, TSLA, JPM, V, WMT, DIS, NFLX, PYPL, ADBE, CRM | 15 large-caps (7 Mag7 + 8 tech/média) |
| Features | 23 (RSI, BB, MACD, stoch, ATR, mom, vol, volume, prix/SMA) | Signal technique |
| Modèle | `GradientBoostingRegressor` (sklearn, **pas** lib xgboost) | Régression du rendement 10j |
| Cible | rendement futur 10 jours (continu) | Régression (vs classification RF/SVM) |
| `n_estimators` | 100 | Nombre d'arbres |
| `max_depth` | 5 | Profondeur |
| `learning_rate` | 0.03 | Pas de boosting (conservatif vs v1 0.05) |
| `subsample` | 0.8 | Stochastic gradient boosting |
| `min_samples_leaf` | 10 | Régularisation |
| Lookback | 90 jours | Fenêtre d'entraînement (vs 120 RF/SVM) |
| Seuil | **0.001** | Rendement prédit min (0,1 %) pour ouvrir |
| Positions max | 9 @ 10 % | 90 % alloué, équipondéré |
| Rebalance | Bimensuel | Lundis pairs (trade) / impairs (train) |
| Graine | `random_state=42` | **Single seed** (cf. lecture honnête) |

## Backtest réel (QC Cloud, frais IBKR inclus)

> **Chiffres non reproduits.** Le backtest de contrôle de #21894, lancé avec le code du dépôt sur la même fenêtre 2015-2024, donne 0,752 / 18,70 % / 40,6 % de drawdown, avec 2009 ordres sur 2516 jours tradés. Voir « Écart avec la baseline ci-dessus », dans la section « Mesure contre des références détenues (#21894) ».

| Métrique | Valeur |
|----------|--------|
| Sharpe ratio | **0.787** |
| CAGR | **19.49 %** |
| Drawdown max | **35.90 %** |
| Rendement total net | 494.3 % (+497 083 $ sur 100 k $) |
| PSR (Probabilistic Sharpe Ratio) | **15.40 %** |
| Ordres exécutés | 1994 |
| Jours tradés | 2516 |

*Backtest frais via QC Cloud project 29434753 (compile `BuildSuccess`, 2026-08-06). Le README anglais documentait Sharpe 0.566 / CAGR 14.8 % / MaxDD 38.6 % (v2 docstring) ; une passe intermédiaire (PR #8049) mesurait Sharpe 0.787 / CAGR 19.5 % / MaxDD 35.9 %. Le backtest frais ci-dessus **confirme #8049 au dixième près** (0.787 / 19.49 % / 35.90 %) : la valeur docstring 0.566 était périmée, #8049 est la vérité reproductible.*

### Lecture honnête — régresseur déguisé en classifieur, beta Mag7+tech, nom trompeur

1. **Nom vs implémentation** : le projet s'appelle « ML-XGBoost » mais utilise `sklearn.ensemble.GradientBoostingRegressor` (Friedman 2001), **pas** la lib `xgboost` (Chen & Guestrin 2016). La référence Friedman citée est correcte pour le code réel, mais le nom induit en erreur sur le moteur employé. À lire comme un **cas d'école de doc-honesty** : le nom d'un artefact peut diverger de son implémentation.

2. **Régresseur utilisé comme classifieur (le point le plus important)** : le modèle prédit un **rendement continu** à 10 jours, mais le code de rebalancement fait `set_holdings(symbol, position_size)` avec une `position_size` **fixe** (~10 %). Autrement dit, la **magnitude** prédite est ignorée — seul le **rang** compte (top-9 dont le rendement prédit > seuil). Un régresseur utilisé pour **trier puis équipondérer** est, en effet, un **classifieur déguisé** : la sophistication de la régression continue est largement gaspillée par un sizing indifférent à la prédiction.

3. **Seuil 0.001 = quasi full-exposure** : un seuil de 0,1 % sur un rendement prédit à 10 jours est **extrêmement bas** (les actions US ont une dérive annuelle de ~10 %, soit ~0,4 % par 10 jours en moyenne). Conséquence : le portefeuille est **presque toujours pleinement investi** dans les 9 meilleures prédictions dès qu'au moins 9 tickers ont une prédiction positive. Ce n'est pas de la sélectivité, c'est du **timing de l'exposition** — la stratégie est structurellement **long market**. La mesure de #21894, plus bas, en confirme une partie : la stratégie détient au moins un titre sur 96,4 % des séances de la fenêtre codée ; le nombre de titres détenus n'est pas mesuré.

4. **Univers Mag7 + tech-heavy (§C point 5)** : 7 des 15 tickers (AAPL, MSFT, GOOGL, AMZN, NVDA, META, TSLA) sont des Mag7, et les 8 autres (JPM, V, WMT, DIS, NFLX, PYPL, ADBE, CRM) sont majoritairement tech/média. La règle `pr-review-discipline.md` §C interdit les Mag7 en training set pour les claims d'alpha. Comme ML-RandomForest, l'essentiel du CAGR est du **beta Mag7+tech** sur le bull run 2015-2024, pas de la capacité prédictive du gradient boosting. La mesure de #21894, plus bas, le confirme : les quinze titres détenus à poids égaux font mieux que la stratégie sur les deux fenêtres mesurées, sans écart significatif.

5. **Single seed (`random_state=42`)** : aucune robustesse multi-seed. §C exige ≥4 seeds (0/1/7/42/99) avec edge ≥ 2σ cross-seed pour tout claim « BEATS ». **PSR 15.40 %** < 50 % : le Sharpe observé n'est pas statistiquement supérieur à zéro au seuil conventionnel — le rendement est compatible avec du bruit de chance sur une seule réalisation.

6. **Triptyque ML pédagogique** : ML-XGBoost complète le triptyque avec [ML-RandomForest](../ML-RandomForest/README.md) (classifieur, sur-ajustement, Mag7) et [ML-SVM](../ML-SVM/README.md) (classifieur linéaire, sous-ajustement, ETF). Trois familles ML, trois modes d'échec différents : RF mémorise la tendance (over-fit), SVM ne la capture pas (under-fit), GBoost prédit bien mais n'utilise que le rang et reste long market. **Aucun des trois n'est de l'alpha** — la valeur est dans la **comparaison des architectures** (classification vs régression, bagging vs boosting vs marge) et de leurs **pièges respectifs**.

**Conclusion honnête** : ne PAS présenter ML-XGBoost comme une stratégie « boosting qui bat le marché ». C'est un **régresseur de rendement utilisé en classement**, sur un **univers Mag7+tech** en **bull market**, avec un **seuil qui maintient une exposition quasi totale**. Sa valeur pédagogique est triple : (a) la **doc-honesty** (nom XGBoost vs sklearn GBR), (b) la **régression-vs-classification** et le gaspillage du signal continu par un sizing fixe, (c) le **capstone du triptyque ML** qui isole l'effet du choix d'architecture (bagging/boosting/marge) à univers et pipeline constants.

## Mesure contre des références détenues (#21894)

`main.py` est mesuré contre deux références détenues : SPY détenu et le 60/40 (SPY 60 %, BND 40 %). Les paramètres qui le permettent sont décrits plus bas, dans « Paramètres de `main.py` ». Le protocole est écrit dans #21894 avant le premier backtest. Chaque backtest tourne sur les nœuds QC. Les tests viennent de `Paradox46Benchmarks/significance.py`, à taux sans risque nul : écart de Sharpe de Ledoit-Wolf, bootstrap stationnaire et écart de moyennes de Newey-West.

- **Verdict.** Il compare la stratégie à SPY détenu et au 60/40, avec une correction de Holm sur six p-valeurs. `BEATS` exige un écart de Sharpe positif et une p de Holm (Ledoit-Wolf) inférieure à 0,05 contre les deux références. `NO BEATS` signifie un Sharpe inférieur à celui de SPY détenu. Tous les autres cas sont `INCONCLUSIVE`.
- **Diagnostic.** `ew15`, les quinze titres de l'univers à un quinzième chacun, passe dans une exécution séparée, avec Holm sur trois p-valeurs. Il retire le modèle et garde l'univers : il demande si la sélection fait mieux que les quinze titres détenus. Il ne change pas le verdict.

**Contrôle d'innocuité : tenu.** En mode `strategy`, sur la fenêtre codée, le code instrumenté reproduit le backtest du `main.py` d'origine : les mêmes 2009 ordres (date, symbole, quantité, aucun écart) et les mêmes 27 statistiques QC. Les 2009 ordres sont exécutés, aucun n'est refusé ; il en va de même dans les autres backtests de la stratégie et d'`ew15`. Le premier ordre date du 2015-01-12, le lundi qui suit le premier entraînement.

**Fenêtres.**

- **Fenêtre codée.** La stratégie n'a pas de préchauffage : son premier entraînement a lieu au premier lundi de 2015 et ses premiers ordres au lundi suivant. Ces séances passées en liquidités sont comprises dans la mesure.
- **Après la fenêtre codée.** Les backtests partent du 2024-11-01. Les traces des quatre modes sont coupées à la première séance de 2025, pour une mesure sur des portefeuilles déjà investis. La fenêtre s'arrête au 2026-07-23 : les nœuds QC ont coupé le backtest demandé jusqu'au 2026-10-21, et la fin a été lue sur la trace.

Sharpe annualisé de la trace `shadow`, taux sans risque nul. L'écart est celui de la stratégie moins la référence.

| Fenêtre | Séances | Stratégie | SPY détenu (écart, p LW, p Holm) | 60/40 (écart, p LW, p Holm) | Verdict |
|---|---|---|---|---|---|
| 2015-01-02 → 2024-12-31 | 2516 | 1,010 | 0,786 (+0,224 ; 0,249 ; 0,995) | 0,802 (+0,208 ; 0,317 ; 0,995) | `INCONCLUSIVE` |
| 2025-01-02 → 2026-07-23 | 389 | −0,239 | 1,047 (−1,286 ; 0,036 ; 0,170) | 1,157 (−1,396 ; 0,034 ; 0,170) | `NO BEATS` |

Sur la fenêtre codée, une p du verdict passe sous 0,05 après Holm : celle de l'écart de moyennes contre le 60/40 (p brute 0,0049, p de Holm 0,030). La stratégie gagne en moyenne 0,041 % de plus par séance que le 60/40. Contre SPY détenu, le même test donne une p brute de 0,150 et une p de Holm de 0,752. Après la fenêtre codée, les deux p brutes de Ledoit-Wolf passent sous 0,05 (0,036 contre SPY détenu, 0,034 contre le 60/40), et les intervalles à 95 % du bootstrap excluent zéro ; après Holm, aucune p du verdict ne passe sous 0,05, la plus petite étant 0,123 (écart de moyennes contre SPY détenu).

Diagnostic contre `ew15`, même convention.

| Fenêtre | Stratégie | `ew15` | Corrélation journalière | Écart | p LW | p Holm (3 tests) |
|---|---|---|---|---|---|---|
| 2015-01-02 → 2024-12-31 | 1,010 | 1,181 | 0,869 | −0,171 | 0,280 | 0,464 |
| 2025-01-02 → 2026-07-23 | −0,239 | 0,224 | 0,859 | −0,463 | 0,335 | 1,0 |

Sur la fenêtre codée, l'écart de moyennes contre `ew15` a une p brute de 0,019 : les quinze titres détenus gagnent en moyenne 0,034 % de plus par séance que la stratégie. Après Holm sur les trois tests du diagnostic, cette p vaut 0,058, juste au-dessus de 0,05.

Volatilité annualisée, rendement annualisé et drawdown maximal des mêmes traces :

| Mode | Fenêtre | Volatilité | Rendement annualisé | Drawdown max |
|---|---|---|---|---|
| stratégie | 2015-2024 | 18,9 % | 18,8 % | 40,6 % |
| SPY détenu | 2015-2024 | 17,6 % | 13,0 % | 33,7 % |
| 60/40 | 2015-2024 | 10,9 % | 8,5 % | 21,7 % |
| `ew15` | 2015-2024 | 23,4 % | 28,2 % | 43,5 % |
| stratégie | 2025-01 → 2026-07-23 | 15,5 % | −4,8 % | 20,1 % |
| SPY détenu | 2025-01 → 2026-07-23 | 17,6 % | 18,4 % | 18,7 % |
| 60/40 | 2025-01 → 2026-07-23 | 10,8 % | 12,7 % | 11,2 % |
| `ew15` | 2025-01 → 2026-07-23 | 21,0 % | 2,5 % | 24,1 % |

Statistiques QC des mêmes backtests. Le Sharpe QC déduit un taux sans risque, celui de la trace non : les deux tableaux ne se comparent pas colonne à colonne. Pour la seconde fenêtre, les statistiques QC portent sur tout le backtest, du 2024-11-01 au 2026-07-23.

| Mode | Backtest | Sharpe QC | CAGR | Drawdown max | Ordres |
|---|---|---|---|---|---|
| stratégie | 2015-2024 | 0,752 | 18,70 % | 40,6 % | 2009 |
| SPY détenu | 2015-2024 | 0,533 | 12,97 % | 33,7 % | 1 |
| 60/40 | 2015-2024 | 0,442 | 8,41 % | 21,7 % | 201 |
| `ew15` | 2015-2024 | 0,962 | 28,01 % | 43,5 % | 1060 |
| stratégie | 2024-11 → 2026-07-23 | −0,341 | −1,33 % | 20,1 % | 342 |
| SPY détenu | 2024-11 → 2026-07-23 | 0,606 | 17,41 % | 18,7 % | 1 |
| 60/40 | 2024-11 → 2026-07-23 | 0,479 | 11,79 % | 11,2 % | 31 |
| `ew15` | 2024-11 → 2026-07-23 | 0,132 | 7,18 % | 24,5 % | 206 |

**Lecture.** Sur la fenêtre codée, la stratégie rend 18,8 % par an contre 13,0 % pour SPY détenu, avec une volatilité à peine plus forte (18,9 % contre 17,6 %) et un drawdown plus profond (40,6 % contre 33,7 %). Par unité de risque, à taux nul, son Sharpe dépasse ceux de SPY détenu et du 60/40, sans écart significatif. Son rendement moyen dépasse significativement celui du 60/40, mais avec presque deux fois sa volatilité : un rendement plus haut n'est pas un Sharpe plus haut, et le verdict porte sur le Sharpe. Ces écarts héritent aussi de l'univers choisi après coup, décrit plus bas.

**Après la fenêtre codée, la stratégie perd de l'argent.** Du 2025-01-02 au 2026-07-23, elle rend −4,8 % par an quand SPY détenu rend 18,4 % et le 60/40 12,7 %. Son Sharpe est sous celui de SPY détenu : le verdict est `NO BEATS`. Les écarts sont grands (−1,29 et −1,40 de Sharpe), mais 389 séances ne suffisent pas à les rendre significatifs après correction pour six tests. L'univers lui-même a peu rendu sur cette fenêtre (`ew15` : 2,5 % par an) : une partie de l'échec tient aux quinze titres choisis, une autre à la sélection, qui fait moins bien qu'eux sans écart significatif (p de Holm 1,0).

**Le modèle ne fait pas mieux que son univers.** Sur la fenêtre codée, les quinze titres détenus à poids égaux rendent 28,2 % par an contre 18,8 % pour la stratégie, avec plus de volatilité (23,4 % contre 18,9 %) et un drawdown un peu plus profond (43,5 % contre 40,6 %). Leur Sharpe est plus haut (1,181 contre 1,010), sans écart significatif (p de Holm 0,464) ; la corrélation journalière est de 0,869. Après la fenêtre codée, `ew15` reste devant (0,224 contre −0,239). Sur les deux fenêtres, rien ne dit que la sélection apporte quelque chose par rapport à l'univers dans lequel elle choisit. C'est la mesure de la phrase du point 4 ci-dessus : le rendement de la stratégie vient de son univers, et le modèle en retire une partie plutôt qu'il n'en ajoute.

**Exposition.** La trace de la stratégie ne bouge pas d'une séance à l'autre sur 90 des 2515 rendements de la fenêtre codée (3,6 %) et sur 27 des 388 de la seconde (7,0 %), signe qu'elle ne détient alors aucun titre. Le reste du temps, elle détient au moins un titre. C'est la mesure de la phrase du point 3 ci-dessus : la stratégie est presque toujours investie. Le nombre de titres détenus, de un à neuf, n'est pas mesuré ici.

**La convention de Sharpe change un classement.** Sous la convention QC, SPY détenu passe devant le 60/40 (0,533 contre 0,442) ; à taux nul, c'est l'inverse (0,786 contre 0,802). Le 60/40 est moins volatil (10,9 % contre 17,6 % par an sur les traces) : la même déduction du taux sans risque pèse plus sur son Sharpe. La place de la stratégie ne change pas : sur la fenêtre codée, elle est devant les deux références sous les deux conventions.

**Écart avec la baseline ci-dessus.** La table de backtest en tête de ce README donne 0,787 de Sharpe, 19,49 % par an, 35,9 % de drawdown, un PSR de 15,40 % et 1994 ordres. Le contrôle de cette mesure, lancé le 2026-10-21 avec le code du dépôt sur la même fenêtre, donne 0,752, 18,70 %, 40,6 %, 12,89 % et 2009 ordres. Le code de la stratégie n'a pas changé entre le 2026-06-11 et #21487, qui a doublé la fenêtre demandée à `history()` dans `train_models` ; le code d'avant #21487, rejoué le même jour, redonne exactement le contrôle : #21487 n'explique pas l'écart. La mesure publiée a été lancée le 2026-07-22, et la source envoyée ce jour-là n'est pas épinglée. Ses ordres, relus sur QC, ont la même sélection que le contrôle le premier jour de trading (2015-01-12, huit titres), avec des quantités qui diffèrent d'une action sur deux d'entre eux ; les rééquilibrages suivants gardent les mêmes titres et les mêmes sens, à une action près, jusqu'au 2015-05-18, où les sélections se séparent. Sur l'ensemble, 195 ordres seulement sont communs aux deux backtests. Le code étant le même, la cause la plus probable est un réajustement des prix historiques par QC entre juillet et octobre : les prix sont ajustés des dividendes, et chaque nouveau dividende les réécrit. Les quantités en dépendent, ainsi que quatre des 23 indicateurs, exprimés en unités de prix (`atr`, `macd`, `macd_signal`, `macd_hist`) ; une petite différence suffit à changer un classement de prédictions, et les trajectoires divergent ensuite. C'est une hypothèse : elle n'est pas vérifiée. La table d'en-tête reste en place, mais ses chiffres ne se reproduisent pas, et la mesure de cette section repose sur le contrôle d'octobre.

**Propriétés du code, gardées telles quelles dans cette mesure.**

- **Univers choisi après coup.** Les quinze titres sont pour la plupart des gagnants connus aujourd'hui. Le verdict contre SPY détenu et le 60/40 hérite de ce biais en faveur de la stratégie. `ew15` partage le même univers : le diagnostic ne voit pas ce biais, il isole la sélection.
- **Données d'entraînement.** `calculate_features` remplace les valeurs manquantes et infinies par zéro avant l'ajout de la cible. Les premières séances de chaque fenêtre de 90 entrent donc dans l'entraînement avec des indicateurs nuls : la moyenne à 50 séances n'existe qu'à partir de la 50ᵉ. Les dix dernières séances n'ont pas de cible et sont écartées par `dropna()`.
- **Une seule graine.** `random_state=42` fixe aussi le sous-échantillonnage. La mesure porte sur cette graine.
- **Taille des positions.** Chaque titre retenu reçoit 10 %, quel que soit le nombre de titres retenus : moins de neuf titres au-dessus du seuil laissent plus de liquidités. Cette part variable de liquidités entre dans le Sharpe.
- **Compte.** Il est déclaré sur marge ; les poids visés somment au plus à 90 %, sans emprunt voulu.

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/ML-XGBoost"`
**QC Cloud :** Déployé comme project 29434753.

### Paramètres de `main.py` (#21894)

Sans paramètre, `main.py` exécute la stratégie sur sa fenêtre codée (2015-01-01 → 2024-12-31). Trois paramètres de backtest servent à la mesurer contre des références détenues, sans toucher à sa décision :

- `mode` : `strategy` (défaut), `spy` (SPY détenu), `6040` (SPY 60 %, BND 40 %) ou `ew15` (les quinze titres de l'univers, un quinzième chacun). Les trois références se rééquilibrent le premier jour de cotation de chaque mois, une minute après l'ouverture ; le lundi de la stratégie (entraînement ou rééquilibrage) n'y fait rien. SPY est abonné dans tous les modes, comme dans le code d'origine qui s'en sert pour planifier ; BND ne l'est qu'en mode `6040` ;
- `start_date` et `end_date` (format `%Y%m%d`) : remplacent les bornes de la fenêtre.

Chaque mode trace aussi `shadow` : la valeur du portefeuille à l'ouverture de chaque séance de SPY, répartie sur les séries e0 à e4 (contrat #18923). Les trois références ont un préchauffage de 60 séances, qui donne un prix à chaque titre abonné, sans ordre ni trace. Le mode `strategy` n'en a pas, comme le code d'origine : LEAN déclenche les événements planifiés pendant un préchauffage, et l'alternance de ses lundis pourrait changer.

## Fichiers

- `main.py` — Stratégie `MLXGBoostAlgorithm` v2 (`GradientBoostingRegressor`).
- `research.ipynb` — Recherche (sweep H1-H5 sur les hyperparamètres + importance des features).
- `assets/readme/*.png` — Figures du sweep (H1 learning rate, H2 n_estimators, H3 threshold, H4 max positions, H5 subsample, synthèse importance).

## Concepts enseignés

- **Régression vs classification** : prédire le rendement (continu) vs le signe (binaire). ML-XGBoost est le seul régresseur du triptyque ML — mais n'utilise que le rang de la prédiction, neutralisant l'avantage du signal continu.
- **Gradient boosting (Friedman 2001)** : additive modelling par stages, chaque arbre corrige les résidus du précédent. `subsample=0.8` = stochastic gradient boosting (introduit du hasard pour la robustesse). Distinct du **bagging** de Random Forest (arbres indépendants).
- **Doc-honesty (nom vs implémentation)** : « XGBoost » le nom ≠ `xgboost` la lib. Le code utilise `sklearn.GradientBoostingRegressor`. Toujours vérifier l'implémentation réelle, pas le label.
- **Seuil et exposition** : un seuil de décision très bas (0.001) sur une prédiction à dérive positive = exposition quasi totale = stratégie long market, pas de la sélectivité.
- **Probabilistic Sharpe Ratio (PSR)** : un Sharpe de 0.787 sur single-seed et univers Mag7 n'est pas statistiquement significatif (PSR 15.4 %).
- **Single seed vs multi-seed** : `random_state=42` seul ne prouve pas la robustesse — §C exige ≥4 seeds + edge 2σ.
- **Triptyque ML** : RF (bagging, over-fit) / SVM (marge, under-fit) / GBoost (boosting, régresseur-en-classement) — comparer isole l'effet de l'architecture à pipeline constant.

## Références

- Friedman (2001), *Greedy Function Approximation: A Gradient Boosting Machine* — **implémentation réelle** (sklearn GBR).
- Chen & Guestrin (2016), *XGBoost: A Scalable Tree Boosting System* — la lib dont le projet porte le nom sans l'utiliser.
- *Hands-On AI Trading* (Jared Broad), Section 06.
- Triptyque : [ML-RandomForest](../ML-RandomForest/README.md) (bagging, sur-ajustement, Mag7) · [ML-SVM](../ML-SVM/README.md) (marge linéaire, sous-ajustement, ETF).
