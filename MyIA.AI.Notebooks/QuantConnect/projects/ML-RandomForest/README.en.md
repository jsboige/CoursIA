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
  <img src="assets/readme/mrf-h1-nestimators.png" alt="Dual-panel « H1: Number of Estimators » sur 2018-2026 base 1 : panel haut equity cumulée (n_est=50 S=0,841 DD=-35,29% bleu fin ~3,8× plus noisy ; n_est=100 S=0,794 DD=-36,13% orange fin ~3,4× — production baseline sweet-spot rendement/stabilité ; n_est=200 S=0,656 DD=-41,07% vert fin ~2,7× surperforme 2022-2023 puis sous-performe post-2024 ; SPY B&H S=0,778 DD=-33,72% rouge pointillé fin ~2,9×). Panel bas drawdowns superposés -35% min 2022-2023 bear market (toutes stratégies corrélées bear 2022). H1 verdict : n_est=100 = sweet-spot opérationnel (n_est=50 winner numérique 0,841 vs 0,794 mais plus volatile)." width="460"/><br>
  <em>H1 — performance et stabilité vs nombre d'estimateurs.</em>
</p>

**H2 — Profondeur maximale.** Jusqu'où laisser chaque arbre croître (*max_depth*) : une profondeur faible sous-ajuste (arbres trop simples pour capturer la structure), une profondeur élevée sur-ajuste (mémorisation du bruit d'entraînement). Le bon régime sépare le signal du bruit.

<p align="center">
  <img src="assets/readme/mrf-h2-maxdepth.png" alt="Dual-panel « H2: Max Depth » sur 2018-2026 base 1 : panel haut equity cumulée (depth=10 S=1,064 DD=-36,03% vert fin ~6,1× — OPTIMAL, BAT TOUTES LES STRATÉGIES y compris SPY B&H de +40% cumulés ; depth=5 S=0,794 DD=-36,13% orange fin ~3,5× baseline production ; SPY B&H S=0,778 DD=-33,72% rouge pointillé fin ~2,9× ; depth=3 S=0,645 DD=-42,8% bleu fin ~2,7× sous-ajuste). Panel bas drawdowns -42% depth=3 plus profond (sur-ajuste inverse). H2 verdict INFIRMÉ sur sous-ajustement : depth=10 surperforme B&H = effet rare." width="460"/><br>
  <em>H2 — compromis biais/variance vs profondeur des arbres.</em>
</p>

**H3 — Seuil de prédiction.** Une position ne s'ouvre que si la probabilité prédite de rendement 10 jours dépasse un seuil (calibré à 0.54 en production). Un seuil bas multiplie les trades (bruit, coûts), un seuil haut restreint l'univers (concentration) — la courbe trace ce compromis sélectivité/fréquence.

<p align="center">
  <img src="assets/readme/mrf-h3-threshold.png" alt="Dual-panel « H3: Prediction Threshold » sur 2018-2026 base 1 : panel haut equity cumulée (threshold=0.5 S=0,83 DD=-41,51% bleu fin ~3,6× ; threshold=0.54 S=0,794 DD=-36,13% orange fin ~4,1× — production sweet-spot optimal ; threshold=0.58 S=0,69 DD=-26,28% vert fin ~2,6× trop sélectif limite upside ; SPY B&H S=0,778 DD=-33,72% rouge pointillé fin ~2,9×). Panel bas drawdowns -41% threshold=0.5 plus profond (trop de trades). H3 verdict : threshold=0.54 sweet-spot sélectivité/couverture (threshold=0.58 réduit DD -36→-26 % mais limite upside)." width="460"/><br>
  <em>H3 — performance et nombre de trades vs seuil de décision.</em>
</p>

**H4 — Taille de l'univers.** Élargir l'univers au-delà des 10 large-caps de référence : plus de candidats diversifie et multiplie les opportunités, mais peut aussi diluer le signal sous un bruit croissant. La courbe montre où s'arrête le bénéfice de la diversification.

<p align="center">
  <img src="assets/readme/mrf-h4-universe.png" alt="Dual-panel « H4: Universe Size » sur 2018-2026 base 1 : panel haut equity cumulée (Universe 5 S=1,118 DD=-35,0% bleu fin ~6,7× — OPTIMAL MASSIF post-2024 winner absolu upside +60% vs B&H ; Universe 10 S=0,794 DD=-36,13% orange baseline production ; Universe 15 S=0,84 DD=-29,21% vert fin ~3,8× sweet-spot downside DD -29% meilleur que baseline ; SPY B&H S=0,778 DD=-33,72% rouge pointillé fin ~2,9×). Panel bas drawdowns superposés. H4 INVERSION anti-sur-vente : Universe=5 winner upside (signal concentré sur 5 titres), Universe=15 sweet-spot downside — l'intuition diversification ne s'applique PAS ici." width="460"/><br>
  <em>H4 — performance vs taille de l'univers d'actifs.</em>
</p>

**H5 — Fréquence d'entraînement.** Le modèle est ré-entraîné mensuellement par défaut. Une cadence plus courte capite un régime changeant mais sur des fenêtres plus bruitées ; plus longue, elle lisse le signal au risque de rater les ruptures de marché.

<p align="center">
  <img src="assets/readme/mrf-h5-trainfreq.png" alt="Dual-panel « H5: Rebalancing Frequency » sur 2018-2026 base 1 : panel haut equity cumulée (Weekly rebal S=0,495 DD=-40,74% bleu fin ~2,0× sur-ajuste bruit ; Biweekly rebal S=0,794 DD=-36,13% orange fin ~3,5× baseline production ; Monthly rebal S=0,919 DD=-30,35% vert fin ~4,7× — OPTIMAL +15% Sharpe vs biweekly, DD meilleur ; SPY B&H S=0,778 DD=-33,72% rouge pointillé fin ~2,9×). Panel bas drawdowns -40% Weekly plus profond. H5 verdict : mensuel sweet-spot (réduit sur-ajustement sans lisser les ruptures)." width="460"/><br>
  <em>H5 — performance vs fréquence de ré-entraînement.</em>
</p>

**Synthèse — importance des features.** Parmi les 12 *features* techniques (RSI, Bollinger, MACD, momentum, volatilité, volume, ratios de prix), lesquelles pilotent réellement la prédiction ? Le classement par importance (*impurity-based*) révèle la hiérarchie effective — un diagnostic de parcimonie : peut-on dropper les features peu contributives sans dégrader le modèle ?

<p align="center">
  <img src="assets/readme/mrf-synthese.png" alt="Horizontal barplot « Feature Importance (RandomForest, moyenne sur tous les entraînements) » : 12 features classées par ordre décroissant — bb_position 0,103 (top 1 Bollinger band position) / mom_10 0,099 (momentum 10j top 2) / macd_hist 0,095 (MACD histogram top 3) / mom_5 0,092 / rsi 0,088 / mom_20 0,083 / price_sma20 0,081 / sma_ratio_5_20 0,076 / vol_20 0,075 / price_sma50 0,074 / sma_ratio_20_50 0,068 / volume_ratio 0,003 (BOTTOM marginal quasi-nul). Hiérarchie : momentum court terme (5/10/20j) + Bollinger + MACD dominent ; volume_ratio candidat drop parcimonie (réduit overfitting + accélère training sans dégrader)." width="460"/><br>
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
