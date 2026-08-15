# ML-XGBoost — Gradient Boosting sur grandes capitalisations US (régresseur de rendement)

**Classe d'actifs :** Actions US grandes capitalisations (15 titres)
**Cloud project ID :** 29434753
**Période backtestée :** 2015-01-01 → 2024-12-31

## Description

Stratégie de **régression par Gradient Boosting** (sklearn `GradientBoostingRegressor`) sur 15 grandes capitalisations US liquides. **Différence majeure vs ML-RandomForest et ML-SVM** : le modèle prédit le **rendement futur à 10 jours** (valeur continue, régression), pas le **signe** du rendement (classification). Utilise 22 features techniques (RSI, bandes de Bollinger, MACD, stochastique, ATR, momentum, volatilité, volume, ratios prix/SMA).

Entraînement bimensuel (un lundi sur deux, alterné avec le rebalancement). Le modèle est **pooled** (un seul régresseur entraîné sur les 15 tickers réunis), 9 positions max, allocation 90 %.

**Note d'honnêteté sur le nom** : malgré le nom du répertoire « ML-XGBoost », le code déployé utilise `sklearn.ensemble.GradientBoostingRegressor` (J. Friedman, 2001), **pas** la bibliothèque `xgboost` (Chen & Guestrin, 2016). Les deux implémentent le gradient boosting mais diffèrent (gestion des valeurs manquantes, objectif régularisé, vitesse). La référence Friedman 2001 citée plus bas correspond bien à l'implémentation réelle.

**Version anglaise préservée** : [README.en.md](README.en.md).

## Configuration déployée (v2, `main.py` Cloud 29434753)

| Composant | Paramètre | Rôle |
|-----------|-----------|------|
| Univers | AAPL, MSFT, GOOGL, AMZN, NVDA, META, TSLA, JPM, V, WMT, DIS, NFLX, PYPL, ADBE, CRM | 15 large-caps (7 Mag7 + 8 tech/média) |
| Features | 22 (RSI, BB, MACD, stoch, ATR, mom, vol, volume, prix/SMA) | Signal technique |
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

3. **Seuil 0.001 = quasi full-exposure** : un seuil de 0,1 % sur un rendement prédit à 10 jours est **extrêmement bas** (les actions US ont une dérive annuelle de ~10 %, soit ~0,4 % par 10 jours en moyenne). Conséquence : le portefeuille est **presque toujours pleinement investi** dans les 9 meilleures prédictions dès qu'au moins 9 tickers ont une prédiction positive. Ce n'est pas de la sélectivité, c'est du **timing de l'exposition** — la stratégie est structurellement **long market**.

4. **Univers Mag7 + tech-heavy (§C point 5)** : 7 des 15 tickers (AAPL, MSFT, GOOGL, AMZN, NVDA, META, TSLA) sont des Mag7, et les 8 autres (JPM, V, WMT, DIS, NFLX, PYPL, ADBE, CRM) sont majoritairement tech/média. La règle `pr-review-discipline.md` §C interdit les Mag7 en training set pour les claims d'alpha. Comme ML-RandomForest, l'essentiel du CAGR est du **beta Mag7+tech** sur le bull run 2015-2024, pas de la capacité prédictive du gradient boosting.

5. **Single seed (`random_state=42`)** : aucune robustesse multi-seed. §C exige ≥4 seeds (0/1/7/42/99) avec edge ≥ 2σ cross-seed pour tout claim « BEATS ». **PSR 15.40 %** < 50 % : le Sharpe observé n'est pas statistiquement supérieur à zéro au seuil conventionnel — le rendement est compatible avec du bruit de chance sur une seule réalisation.

6. **Triptyque ML pédagogique** : ML-XGBoost complète le triptyque avec [ML-RandomForest](../ML-RandomForest/README.md) (classifieur, sur-ajustement, Mag7) et [ML-SVM](../ML-SVM/README.md) (classifieur linéaire, sous-ajustement, ETF). Trois familles ML, trois modes d'échec différents : RF mémorise la tendance (over-fit), SVM ne la capture pas (under-fit), GBoost prédit bien mais n'utilise que le rang et reste long market. **Aucun des trois n'est de l'alpha** — la valeur est dans la **comparaison des architectures** (classification vs régression, bagging vs boosting vs marge) et de leurs **pièges respectifs**.

**Conclusion honnête** : ne PAS présenter ML-XGBoost comme une stratégie « boosting qui bat le marché ». C'est un **régresseur de rendement utilisé en classement**, sur un **univers Mag7+tech** en **bull market**, avec un **seuil qui maintient une exposition quasi totale**. Sa valeur pédagogique est triple : (a) la **doc-honesty** (nom XGBoost vs sklearn GBR), (b) la **régression-vs-classification** et le gaspillage du signal continu par un sizing fixe, (c) le **capstone du triptyque ML** qui isole l'effet du choix d'architecture (bagging/boosting/marge) à univers et pipeline constants.

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/ML-XGBoost"`
**QC Cloud :** Déployé comme project 29434753.

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
