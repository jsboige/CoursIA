# ML-XGBoost

**Asset class:** US Equities (Large-cap liquid)
**Cloud project ID:** 29434753

## Description

Gradient Boosting (sklearn `GradientBoostingRegressor`) strategy on 15 liquid US stocks.
Uses 22 comprehensive features including RSI, Bollinger Bands, MACD, Stochastic oscillator, ATR, momentum, volatility, volume ratios, and price/SMAs.

Alternating Monday pattern: odd Mondays for training, even Mondays for rebalance. 90% allocation across up to 9 positions with prediction threshold 0.001.

## Figures du notebook de recherche

Le notebook [`research.ipynb`](research.ipynb) teste cinq hypothèses sur les hyperparamètres du gradient boosting — learning rate, nombre d'estimateurs, seuil de prédiction, nombre maximum de positions et subsample ratio — puis synthétise l'importance des features. Provenance détaillée : [`MANIFEST.md`](assets/readme/MANIFEST.md).

Plutôt qu'une mosaïque-bloc en tête de README, chaque figure est présentée **dans le contexte narratif de l'hypothèse qu'elle teste** — une figure par sweep, le paragraphe qui interprète le résultat adjacent. Doctrine **#5780** : pas de galerie générique, l'image **accompagne** la prose.

### H1 — Learning rate (`xgb-h1-learningrate.png`)

Le notebook teste 3 valeurs de `learning_rate` (0.01 / 0.03 / 0.1) sur l'ensemble du ré-entraînement bihebdomadaire. C'est l'hyperparamètre de shrinkage qui pondère la contribution de chaque arbre séquentiel dans le gradient boosting : trop bas, le modèle sous-apprend ; trop haut, il sur-apprend et diverge.

<p align="center"><img src="assets/readme/xgb-h1-learningrate.png" alt="H1 learning rate — sweep 3 lr (0.01/0.03/0.1) 2018-2026, courbes superposées, S=0.538/0.564/0.57, écart max 0.03 ; SPY B&H S=0.778 capital 2.9× nettement au-dessus" width="840"/><br/><em>H1 — sweep learning_rate QUASI-NUL : 3 lr convergent (S=0.538/0.564/0.57, écart max 0.03), courbes superposées sur la majeure partie de la période ; SPY B&H (rouge, S=0.778) termine à 2.9× vs ~2.1× pour XGBoost — underperformance systématique de -25% en capital.</em></p>

**Verdict — sweep QUASI-NUL**. L'écart Sharpe max entre les 3 configurations n'est que de 0.03, et les courbes sont visuellement superposées sur la majeure partie de 2018-2026. Le `learning_rate` n'a **aucun effet discriminant** sur la performance long-terme de XGBoost dans cette configuration. **Mais** les trois configs sont nettement sous SPY Buy-Hold : capital final ~2.1× vs 2.9× pour le benchmark, soit -25% en capital. Le sweep confirme que le learning_rate n'est pas le levier à actionner ; le problème est plus structurel.

### H2 — Nombre d'estimateurs (`xgb-h2-nestimators.png`)

Le notebook teste 3 valeurs de `n_estimators` (50 / 100 / 200), c'est-à-dire le nombre d'arbres séquentiels entraînés par le gradient boosting. Plus d'arbres = plus de capacité d'apprentissage, mais aussi plus de risque de sur-apprentissage si le shrinkage n'est pas adapté.

<p align="center"><img src="assets/readme/xgb-h2-nestimators.png" alt="H2 n_estimators — sweep 3 n_est (50/100/200) 2018-2026, courbes superposées à 2-3 px près, S=0.568/0.564/0.6, écart max 0.04 ; n_est=200 marginal winner fin 2025-26 ; SPY B&H au-dessus" width="840"/><br/><em>H2 — sweep n_estimators QUASI-NUL : 3 n_est (50/100/200) → S=0.568/0.564/0.6, écart max 0.04, courbes superposées à 2-3 pixels près sur 2018-2026. Le verdict n_est=200 winner (S=0.6) n'apparaît qu'en zoom fin 2025-26.</em></p>

**Verdict — sweep QUASI-NUL**. L'écart Sharpe max est de 0.04 entre les 3 configurations, et les courbes sont **superposées à 2-3 pixels près** sur la quasi-totalité de la période. Le verdict marginal « n_est=200 winner » (S=0.6) n'émerge qu'en toute fin 2025-26, un boost tardif qui pourrait être du bruit. **SPY B&H reste toujours au-dessus** (~2.1× vs 2.9×). Le `n_estimators` est aussi inopérant sur la performance long-terme. Comme H1, ce n'est pas le levier pertinent.

### H3 — Seuil de prédiction (`xgb-h3-threshold.png`)

Le notebook teste 3 valeurs de `threshold` (0.0 / 0.001 / 0.01), c'est-à-dire le seuil minimal en dessous duquel une prédiction de retour est ignorée (position = cash). C'est un filtre de confiance sur le signal ML.

<p align="center"><img src="assets/readme/xgb-h3-threshold.png" alt="H3 threshold — sweep 3 threshold (0.0/0.001/0.01) 2018-2026, threshold=0.0 winner S=0.591 DD=-36.93% ; threshold=0.001 default S=0.564 ; threshold=0.01 perdant S=0.534 DD=-32.35% ; range 0.06 sweep DISCRIMINANT MODESTE ; SPY B&H au-dessus" width="840"/><br/><em>H3 — sweep prediction_threshold DISCRIMINANT MODESTE : 3 threshold (0.0/0.001/0.01) → S=0.591/0.564/0.534, range 0.06. threshold=0.0 winner (sweet spot à zéro — pas de filtre = MIEUX). threshold=0.01 perdant (S=0.534, DD=-32.35% le moins creux).</em></p>

**Verdict — sweep DISCRIMINANT MODESTE**. Range Sharpe 0.534-0.591 (écart 0.06), le verdict contre-intuitif émerge : **threshold=0.0 winner**. Supprimer le filtre de seuil — c'est-à-dire prendre position dès que la prédiction existe, sans condition de magnitude minimale — **améliore** légèrement la performance. Cela suggère que le signal XGBoost est bruité mais pas biaisé, et qu'un seuil positif filtre plus de bonnes prédictions que de mauvaises. **Mais toutes les configs restent sous SPY B&H** (~2.2× vs 2.9×). Pour le live, retenir `threshold=0.0` ; pour les configs futures, explorer un seuil négatif (autoriser le « anti-signal »).

### H4 — Nombre maximum de positions (`xgb-h4-maxpositions.png`)

Le notebook teste 3 valeurs de `max_pos` (3 / 7 / 12), c'est-à-dire le nombre maximum de positions simultanées dans le portefeuille à chaque rebalance. Plus de positions = plus de diversification, mais aussi plus de dilution du signal.

<p align="center"><img src="assets/readme/xgb-h4-maxpositions.png" alt="H4 max positions — sweep 3 max_pos (3/7/12) 2018-2026, max_pos=12 winner S=0.585 DD=-30.62% (le moins creux) ; max_pos=7 default S=0.568 DD=-41.29% ; max_pos=3 perdant S=0.508 DD=-48.84% ; range 0.08 sweep DISCRIMINANT MODESTE le plus grand des sweeps XGBoost" width="840"/><br/><em>H4 — sweep max_positions DISCRIMINANT MODESTE (le plus grand des sweeps XGBoost) : 3 max_pos (3/7/12) → S=0.508/0.568/0.585, range 0.08. max_pos=12 winner en capital + DD=-30.62% (le moins creux des 3). max_pos=3 perdant avec DD=-48.84% mi-2022.</em></p>

**Verdict — sweep DISCRIMINANT MODESTE** (range 0.08, le plus grand des sweeps XGBoost). Le verdict attendu se confirme : **max_pos=12 winner** en capital final ET en drawdown (-30.62%, le moins creux des 3 configs). Plus de diversification améliore à la fois le rendement et la résilience. Le perdant est `max_pos=3` (S=0.508, DD=-48.84%) avec un creux sévère mi-2022. **Mais toutes les configs restent sous SPY B&H** (~2.3× vs 2.9×). Pour le live, retenir `max_pos=12` (ou plus, à tester hors-scope) ; le coût opérationnel d'une diversification plus large est à mettre en balance avec le gain marginal.

### H5 — Subsample ratio (`xgb-h5-subsample.png`)

Le notebook teste 3 valeurs de `subsample` (0.6 / 0.8 / 1.0), c'est-à-dire la fraction d'échantillons tirés aléatoirement pour entraîner chaque arbre séquentiel. C'est l'analogue du bagging pour le gradient boosting : introduire du bruit dans les données pour réduire la variance.

<p align="center"><img src="assets/readme/xgb-h5-subsample.png" alt="H5 subsample — sweep 3 subsample (0.6/0.8/1.0) 2018-2026, subsample=1.0 winner S=0.593 DD=-39.58% (pas de subsampling = MIEUX) ; subsample=0.8 default S=0.564 DD=-37.29% ; subsample=0.6 perdant S=0.527 DD=-35.55% ; range 0.07 sweep DISCRIMINANT MODESTE" width="840"/><br/><em>H5 — sweep subsample DISCRIMINANT MODESTE : 3 subsample (0.6/0.8/1.0) → S=0.527/0.564/0.593, range 0.07. subsample=1.0 winner (pas de subsampling = MIEUX). subsample=0.6 perdant. Verdict contre-intuitif : pour XGBoost sur 15 tickers, le bagging n'apporte rien.</em></p>

**Verdict — sweep DISCRIMINANT MODESTE** (range 0.07). Le verdict contre-intuitif émerge : **subsample=1.0 winner** (pas de subsampling = MIEUX). Pour XGBoost sur ces 15 tickers, le bagging (sous-échantillonnage stochastique) **n'apporte rien** — supprimer le bruit stochastique améliore la performance. Hypothèse : avec un univers restreint (15 tickers) et un signal déjà peu discriminant (cf H1+H2 sweeps nuls), le sous-échantillonnage retire des informations utiles sans réduire la variance de manière significative. **Mais toutes les configs restent sous SPY B&H** (~2.2× vs 2.9×). Pour le live, retenir `subsample=1.0` ; le subsampling est une technique conçue pour des univers plus larges.

### Synthèse — Importance des features (`xgb-synthese.png`)

Le notebook entraîne le modèle GradientBoosting final sur l'ensemble de la période et extrait l'importance moyenne de chacune des 22 features sur tous les entraînements. C'est la **cartographie de ce que XGBoost a appris à utiliser** — pas ce qu'il aurait dû utiliser (overlap partiel).

<p align="center"><img src="assets/readme/xgb-synthese.png" alt="Feature Importance XGBoost — bar chart horizontal 22 features triées desc, vol_20 winner ~0.122 (inversion vs RandomForest où vol_20 perdant) ; atr ~0.095 / macd_signal ~0.088 / atr_ratio ~0.085 (cluster volatilité+momentum top-4) ; bb_position perdant ~0.018 (2ᵉ inversion vs RandomForest où winner)" width="840"/><br/><em>Synthèse — Feature Importance GradientBoosting (moyenne sur tous les entraînements, 22 features). vol_20 winner (~0.122, inversion spectaculaire vs ML-RandomForest où vol_20 perdant). bb_position perdant (~0.018, 2ᵉ inversion). Cluster volatilité+momentum en top-4 (atr ~0.095, macd_signal ~0.088, atr_ratio ~0.085). volume_ratio+volume_change quasi-nuls.</em></p>

**Verdict — INVERSION SPECTACULAIRE vs ML-RandomForest** :
- **vol_20** passe de **perdant** dans RandomForest (mrf 0.076) à **winner** dans XGBoost (~0.122) — XGBoost exploite fortement la volatilité 20j, alors que RandomForest la sous-utilisait.
- **bb_position** passe de **winner** dans RandomForest (~0.103) à **perdant** dans XGBoost (~0.018) — momentum/position Bollinger est marginal pour XGBoost, alors que c'était le signal dominant pour RandomForest.
- **volume_ratio + volume_change** quasi-nuls dans les deux cas — l'information de volume n'est pas exploitable par ces deux modèles sur cet univers.

**Hypothèse** : XGBoost gère mieux les features de **volatilité** (vol_20, atr, atr_ratio) via ses tree splits séquentiels avec shrinkage, alors que RandomForest distribue l'importance entre features de **momentum** (bb_position) et volume plus均匀ément. Pour XGBoost, **les features de VOLATILITÉ dominent**, momentum marginal.

**Découverte majeure — XGBoost sous-performe SPY B&H systématiquement** : contrairement à ML-RandomForest où 4 winners sur 5 battent SPY (S=0.778), **ML-XGBoost sous-performe SPY Buy-Hold sur TOUS les sweeps** (S range 0.508-0.593, capital final ~2.1-2.3× vs 2.9× pour SPY). La stratégie XGBoost ML est **négativement valorisée** par rapport au benchmark sur 2018-2026. **L'algo ML XGBoost ne bat pas le simple buy-and-hold** sur la période.

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/ML-XGBoost"`
```bash
lean backtest --project .
```

**QC Cloud:** Open project 29434753 in the QuantConnect IDE and click "Backtest".

## Backtest Metrics (2015-2026)

| Metric | Value |
|--------|-------|
| Sharpe Ratio | 0.566 |
| CAGR | 14.8% |
| Max Drawdown | 38.6% |
| Rebalance | Biweekly |
| Max Positions | 9 |

## Files

- `main.py` - Strategy (v2, GradientBoostingRegressor)
- `research.ipynb` - Feature importance and hyperparameter tuning

## References

- Friedman (2001), "Greedy Function Approximation: A Gradient Boosting Machine"
- Hands-On AI Trading, Section 06