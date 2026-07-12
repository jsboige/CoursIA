# ML-RandomForest

**Asset class:** US Equities (Large-cap)
**Cloud project ID:** 29434751

## Description

Random Forest (sklearn `RandomForestClassifier`) strategy on 10 large-cap US stocks.
Uses 12 technical features (RSI, Bollinger Bands, MACD, momentum, volatility, volume, price ratios) to predict 10-day forward returns.

Monthly model training with biweekly rebalance (every other Monday). Prediction threshold of 0.54 with max 5 concurrent positions at 18% weight each.

## Figures du notebook de recherche

Le notebook [`research.ipynb`](research.ipynb) teste cinq hypothèses sur les hyperparamètres du Random Forest — nombre d'estimateurs, profondeur maximale, seuil de prédiction, taille de l'univers et fréquence d'entraînement — puis synthétise l'importance des features. Provenance détaillée : [`MANIFEST.md`](assets/readme/MANIFEST.md).

**H1 — Nombre d'estimateurs.** Combien d'arbres (*n_estimators*) suffit-il d'agréger pour stabiliser la prédiction ? Trop peu d'arbres, la forêt reste bruitée ; au-delà d'un certain seuil, le gain marginal s'amenuise et l'on paie un coût de calcul croissant pour un plateau de performance.

<p align="center">
  <img src="assets/readme/mrf-h1-nestimators.png" alt="H1 nombre d'estimateurs" width="460"/><br>
  <em>H1 — performance et stabilité vs nombre d'estimateurs.</em>
</p>

**H2 — Profondeur maximale.** Jusqu'où laisser chaque arbre croître (*max_depth*) : une profondeur faible sous-ajuste (arbres trop simples pour capturer la structure), une profondeur élevée sur-ajuste (mémorisation du bruit d'entraînement). Le bon régime sépare le signal du bruit.

<p align="center">
  <img src="assets/readme/mrf-h2-maxdepth.png" alt="H2 profondeur maximale" width="460"/><br>
  <em>H2 — compromis biais/variance vs profondeur des arbres.</em>
</p>

**H3 — Seuil de prédiction.** Une position ne s'ouvre que si la probabilité prédite de rendement 10 jours dépasse un seuil (calibré à 0.54 en production). Un seuil bas multiplie les trades (bruit, coûts), un seuil haut restreint l'univers (concentration) — la courbe trace ce compromis sélectivité/fréquence.

<p align="center">
  <img src="assets/readme/mrf-h3-threshold.png" alt="H3 seuil de prédiction" width="460"/><br>
  <em>H3 — performance et nombre de trades vs seuil de décision.</em>
</p>

**H4 — Taille de l'univers.** Élargir l'univers au-delà des 10 large-caps de référence : plus de candidats diversifie et multiplie les opportunités, mais peut aussi diluer le signal sous un bruit croissant. La courbe montre où s'arrête le bénéfice de la diversification.

<p align="center">
  <img src="assets/readme/mrf-h4-universe.png" alt="H4 taille de l'univers" width="460"/><br>
  <em>H4 — performance vs taille de l'univers d'actifs.</em>
</p>

**H5 — Fréquence d'entraînement.** Le modèle est ré-entraîné mensuellement par défaut. Une cadence plus courte capite un régime changeant mais sur des fenêtres plus bruitées ; plus longue, elle lisse le signal au risque de rater les ruptures de marché.

<p align="center">
  <img src="assets/readme/mrf-h5-trainfreq.png" alt="H5 fréquence d'entraînement" width="460"/><br>
  <em>H5 — performance vs fréquence de ré-entraînement.</em>
</p>

**Synthèse — importance des features.** Parmi les 12 *features* techniques (RSI, Bollinger, MACD, momentum, volatilité, volume, ratios de prix), lesquelles pilotent réellement la prédiction ? Le classement par importance (*impurity-based*) révèle la hiérarchie effective — un diagnostic de parcimonie : peut-on dropper les features peu contributives sans dégrader le modèle ?

<p align="center">
  <img src="assets/readme/mrf-synthese.png" alt="Synthèse importance des features" width="460"/><br>
  <em>Synthèse — classement des features par importance.</em>
</p>

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/ML-RandomForest"`
```bash
lean backtest --project .
```

**QC Cloud:** Open project 29434751 in the QuantConnect IDE and click "Backtest".

## Backtest Metrics (2015-2026)

| Metric | Value |
|--------|-------|
| Sharpe Ratio | 0.68 |
| CAGR | 20.1% |
| Max Drawdown | 36.4% |
| Rebalance | Biweekly |

## Files

- `main.py` - Strategy (v3, RandomForestClassifier)
- `research.ipynb` - Feature engineering and hyperparameter research

## References

- Breiman (2001), "Random Forests"
- Hands-On AI Trading, Section 06 Example
