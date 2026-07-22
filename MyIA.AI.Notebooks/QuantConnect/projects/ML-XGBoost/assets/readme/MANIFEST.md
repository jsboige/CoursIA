# Manifeste des figures — ML-XGBoost

**Migration c.786 (2026-07-22, doctrine #5780 amendée par PR #7771)** : passe du format **vague-1 détaillé** (`### filename.png — Title` avec em-dash + titre collé, descendants `### H1 — Learning rate` etc.) au format **canonique post-#7771** (`## filename.png` + champ `**Description visuelle** :` obligatoire adjacent par figure). **Tells visuels c.778-L1/L2/L3 vérifiés firsthand** (MiniMax M3 + PIL RGB stats 100×50) : 6/6 figures = **matplotlib-blanc discriminator** (L778-L2, mean RGB dominant 228-246, bg blanc 67-82% — palette matplotlib `tab:blue`/`tab:orange`/`tab:green`/`tab:red` + barres `steelblue` standard, signature d'un `plt.subplots()` + `ax.barh()` hors `seaborn-darkgrid`). **Detector `scripts/notebook_tools/detect_manifest_field.py --check`** : exit 0 obligatoire avant merge (6/6 figures déclarent `Description visuelle`). **Out-of-scope c.787+** : 5 autres MANIFESTs QC project restants après c.783 LSH / c.784 Probas / c.785 ML-Training-Pipeline / c.786 ML-XGBoost = AllWeather (6 fig), EMA-Cross-Crypto (5 fig), EMA-Cross-Index (6 fig), ForexCarry (7 fig), ML-RandomForest (6 fig).

> **Audit vision fondateur c.453 (MiniMax M3, 2026-07-15)** — 0/6 alt-texts ACCURATE ; 6 corrections content-driven. Tous les alt-texts d'origine étaient **TITLES-driven** (énuméraient la méthode sans rendre compte des valeurs Sharpe/MaxDD ni du verdict winner/perdant/SPY B&H sous-perf systématique). **Sous-pattern c.453 = DOUBLE-NATURE** : H1+H2 sweeps **QUASI-NULS** (écart Sharpe 0.03-0.04, paramètres inopérants) + H3+H4+H5 sweeps **DISCRIMINANTS MODESTES** (range 0.06-0.08). **Découverte majeure** : XGBoost **sous-performe SPY B&H sur TOUS les sweeps** (S range 0.508-0.593 vs SPY S=0.778), contrairement à ML-RandomForest c.452 où 4/5 winners battent SPY. **Feature importance inversée vs ML-RandomForest** : vol_20 winner ici (vs perdant dans RandomForest), bb_position perdant ici (vs winner dans RandomForest). Cf [c.453 PR body](../../../../../../../scratchpad/xgb-pr-body.md) pour le diagnostic complet G.1 + 6 attributions cell×output confirmées.

Provenance de chaque figure (convention d'indexation **all-cells** du module `extract_readme_figures.py` : `cellule` = indice de cellule dans le notebook, `output` = indice de sortie de cette cellule). Sources vérifiées sur `origin/main`, extraites de [`research.ipynb`](../../research.ipynb) (notebook de recherche local).

| Figure | Fichier | Dimensions | Poids | Source (cellule · output) | Sujet (audit c.453) |
|--------|---------|------------|-------|---------------------------|---------------------|
| H1 — Learning rate | `xgb-h1-learningrate.png` | 1000×712 | 185 Ko | cellule 11 · output 4 | **Sweep QUASI-NUL** : 3 lr (0.01/0.03/0.1) → S=0.538/0.564/0.57, écart max 0.03, courbes superposées ; SPY B&H (S=0.778) nettement au-dessus 2.9× vs ~2.1× |
| H2 — N estimateurs | `xgb-h2-nestimators.png` | 1389×989 | 197 Ko | cellule 14 · output 4 | **Sweep QUASI-NUL** : 3 n_est (50/100/200) → S=0.568/0.564/0.6, écart max 0.04, n_est=200 marginal winner fin 2025 ; SPY B&H toujours au-dessus |
| H3 — Seuil | `xgb-h3-threshold.png` | 1000×712 | 182 Ko | cellule 17 · output 4 | **Sweep DISCRIMINANT MODESTE** : 3 threshold (0.0/0.001/0.01) → S=0.591/0.564/0.534, threshold=0.0 winner |
| H4 — Max positions | `xgb-h4-maxpositions.png` | 900×640 | 174 Ko | cellule 20 · output 4 | **Sweep DISCRIMINANT MODESTE** : 3 max_pos (3/7/12) → S=0.508/0.568/0.585, max_pos=12 winner + DD=-30.62% moins creux |
| H5 — Subsample | `xgb-h5-subsample.png` | 1000×712 | 191 Ko | cellule 23 · output 4 | **Sweep DISCRIMINANT MODESTE** : 3 subsample (0.6/0.8/1.0) → S=0.527/0.564/0.593, subsample=1.0 winner (pas de subsampling = MIEUX) |
| Synthèse | `xgb-synthese.png` | 989×790 | 43 Ko | cellule 26 · output 0 | **Feature Importance INVERSION vs ML-RandomForest** : 22 features, **vol_20 winner ~0.122** (vs perdant 0.076 dans RandomForest), bb_position perdant ~0.018 (vs winner dans RandomForest), volume_ratio+volume_change quasi-nuls |

**Total** : 6 figures, 974 Ko. **Politique** (#5654) : ≤200 Ko/fichier, downscale ≤1200 px max. H1/H3/H4/H5 (220–243 Ko natifs, denses) downscaled à 900–1000 px ; H2 passe natif après optimisation PNG (216 → 197 Ko). Arc : cinq hypothèses d'hyperparamètres XGBoost (learning rate, n estimateurs, seuil, max positions, subsample) → synthèse par importance des features.

---

## Verdicts détaillés par figure

## xgb-h1-learningrate.png

- **Description visuelle** : Figure 1000×712 (185 Ko) **dual-panel matplotlib-blanc** (L778-L2 tell RGB dominant `(245, 246, 246)` vérifié firsthand MiniMax M3 + PIL, bg blanc 78% palette `tab:blue`/`tab:orange`/`tab:green`/`tab:red` standard matplotlib) :
  - **Panneau haut « H1: Learning Rate »** : 3 courbes equity 2018-2026 superposées (courbes 2-3 pixels près) avec palette tab10 matplotlib standard :
    - `lr=0.01` bleu tab: S=0.538, DD=-37.78% — config conservatrice
    - `lr=0.03` orange tab: S=0.564, DD=-37.29% — current default
    - `lr=0.1` vert tab: S=0.57, DD=-35.81% — config agressive
    - SPY Buy-Hold rouge tab (référence externe) : S=0.778, DD=-33.72%, capital 1.0 → 2.9
  - **Panneau bas « Drawdowns »** : 3 aires bleues/orange/vert + aire rose SPY, mêmes teintes que le panneau equity ; DD range visible -20% à -45%, creux mi-2022 visible sur toutes les configs (cohérent bear market 2022).
  - Légende unique panneau haut (4 entrées : 3 XGBoost + SPY), axes annotés Year/Portfolio Value (haut) et Year/Drawdown (bas), grille légère grise.
- **Haut** « H1: Learning Rate » 2018-2026, 3 courbes XGBoost :
  - `lr=0.01` bleu : S=0.538, DD=-37.78%
  - `lr=0.03` orange : S=0.564, DD=-37.29% (current, default)
  - `lr=0.1` vert : S=0.57, DD=-35.81%
  - **SPY Buy-Hold** rouge (référence externe) : S=0.778, DD=-33.72%, capital 1.0 → 2.9
- **Bas** « Drawdowns » 2018-2026, 3 aires bleues/orange/vert + aire rose SPY
- **Verdict** : **sweep QUASI-NUL** — écart Sharpe max 0.03 entre les 3 configs, courbes superposées sur la majeure partie de la période. Le learning_rate n'a **aucun effet discriminant** sur la perf long-terme XGBoost. **MAIS** les 3 configs XGBoost sont **nettement sous SPY B&H** (capital final ~2.1× vs 2.9×, Sharpe -25%). Verdict implicite : la stratégie XGBoost ML est **sous-performante vs benchmark**.

## xgb-h2-nestimators.png

- **Description visuelle** : Figure 1389×989 (197 Ko) **dual-panel matplotlib-blanc** (L778-L2 tell RGB dominant `(245, 245, 246)` vérifié firsthand MiniMax M3 + PIL, bg blanc 73%, palette `tab:blue`/`tab:orange`/`tab:green`/`tab:red` standard matplotlib — figure la plus dense en raison de sa résolution native 1389×989) :
  - **Panneau haut « H2: N Estimators »** : 3 courbes equity 2018-2026 superposées à 2-3 pixels près (cf verdict sweep QUASI-NUL), boost tardif visible fin 2025-26 pour n_est=200 :
    - `n_est=50` bleu tab: S=0.568, DD=-40.96% — config sous-apprenante
    - `n_est=100` orange tab: S=0.564, DD=-37.29% — current default
    - `n_est=200` vert tab: S=0.6, DD=-34.85% — marginal winner fin 2025-26
    - SPY Buy-Hold rouge tab : S=0.778, DD=-33.72%, capital 1.0 → 2.9
  - **Panneau bas « Drawdowns »** : 3 aires bleues/orange/vert + aire rose SPY, mêmes teintes ; DD range visible -20% à -50%, n_est=50 bleu présente DD plus sévère mi-2022 (~-41%).
  - Légende unique panneau haut (4 entrées), axes annotés Year/Portfolio Value + Year/Drawdown, grille légère grise.
- **Haut** « H2: N Estimators » 2018-2026, 3 courbes XGBoost :
  - `n_est=50` bleu : S=0.568, DD=-40.96%
  - `n_est=100` orange : S=0.564, DD=-37.29% (current, default)
  - `n_est=200` vert : S=0.6, DD=-34.85% (marginal winner fin 2025-26)
  - **SPY Buy-Hold** rouge : S=0.778, DD=-33.72%, capital 1.0 → 2.9
- **Bas** « Drawdowns » 2018-2026
- **Verdict** : **sweep QUASI-NUL** — écart Sharpe max 0.04 entre les 3 configs, courbes **superposées à 2-3 pixels près** sur 2018-2026. Le verdict « n_est=200 winner S=0.6 » n'apparaît qu'en zoom sur fin 2025-26 (boost tardif). **SPY B&H toujours au-dessus** (capital final ~2.1× vs 2.9×). Verdict implicite : n_estimators est aussi inopérant sur la perf long-terme.

## xgb-h3-threshold.png

- **Description visuelle** : Figure 1000×712 (182 Ko) **dual-panel matplotlib-blanc** (L778-L2 tell RGB dominant `(238, 244, 240)` vérifié firsthand MiniMax M3 + PIL, bg blanc 70%, palette `tab:blue`/`tab:orange`/`tab:green`/`tab:red` standard matplotlib) :
  - **Panneau haut « H3: Prediction Threshold »** : 3 courbes equity 2018-2026, sweep **DISCRIMINANT MODESTE** visible fin 2024-25 — threshold=0.0 BLEU se détache marginalement :
    - `threshold=0.0` bleu tab: S=0.591, DD=-36.93% — **winner**, sweet spot (aucun filter = MIEUX)
    - `threshold=0.001` orange tab: S=0.564, DD=-37.29% — current default
    - `threshold=0.01` vert tab: S=0.534, DD=-32.35% — perdant, Sharpe le plus bas
    - SPY Buy-Hold rouge tab : S=0.778, DD=-33.72%, capital 1.0 → 2.9
  - **Panneau bas « Drawdowns »** : 3 aires bleues/orange/vert + aire rose SPY, mêmes teintes ; DD range visible -20% à -45%.
  - Légende unique panneau haut (4 entrées), axes annotés, grille légère grise.
- **Haut** « H3: Prediction Threshold » 2018-2026, 3 courbes XGBoost :
  - `threshold=0.0` bleu : S=0.591, DD=-36.93% (**winner**, sweet spot à 0 — aucune filter = MIEUX)
  - `threshold=0.001` orange : S=0.564, DD=-37.29% (current, default)
  - `threshold=0.01` vert : S=0.534, DD=-32.35% (perdant, Sharpe le plus bas)
- **Bas** « Drawdowns » 2018-2026
- **Verdict** : **sweep DISCRIMINANT MODESTE** — range Sharpe 0.534-0.591 (écart 0.06). threshold=0.0 winner légèrement visible fin 2024-25. **Verdict contre-intuitif** : supprimer le filtre de seuil (threshold=0) **améliore** légèrement la perf XGBoost. Mais **toutes configs encore sous SPY B&H** (~2.2× vs 2.9×).

## xgb-h4-maxpositions.png

- **Description visuelle** : Figure 900×640 (174 Ko) **dual-panel matplotlib-blanc** (L778-L2 tell RGB dominant `(228, 234, 233)` vérifié firsthand MiniMax M3 + PIL, bg blanc 67% — figure la plus dense en raison de sa résolution 900×640, sweep **DISCRIMINANT MODESTE** le plus discriminant visible via les courbes drawdowns), palette `tab:blue`/`tab:orange`/`tab:green`/`tab:red` standard matplotlib :
  - **Panneau haut « H4: Max Positions »** : 3 courbes equity 2018-2026, sweep **DISCRIMINANT MODESTE** le plus discriminant (range Sharpe 0.08), max_pos=12 VERT winner visible :
    - `max_pos=3` bleu tab: S=0.508, DD=-48.84% — perdant, DD sévère mi-2022 -49%
    - `max_pos=7` orange tab: S=0.568, DD=-41.29% — current default
    - `max_pos=12` vert tab: S=0.585, DD=-30.62% — **winner** + diversification → DD moins creux
    - SPY Buy-Hold rouge tab : S=0.778, DD=-33.72%, capital 1.0 → 2.9
  - **Panneau bas « Drawdowns »** : 3 aires bleues/orange/vert + aire rose SPY, max_pos=12 vert présente DD moins sévère visible (creux -30% vs -49% max_pos=3), différenciation la plus visible parmi les 5 sweeps.
  - Légende unique panneau haut (4 entrées), axes annotés, grille légère grise.
- **Haut** « H4: Max Positions » 2018-2026, 3 courbes XGBoost :
  - `max_pos=3` bleu : S=0.508, DD=-48.84% (perdant, DD sévère mi-2022 -49%)
  - `max_pos=7` orange : S=0.568, DD=-41.29% (current, default)
  - `max_pos=12` vert : S=0.585, DD=-30.62% (**winner**, + diversification → DD moins creux)
- **Bas** « Drawdowns » 2018-2026 — on voit clairement max_pos=12 vert avec drawdown moins sévère
- **Verdict** : **sweep DISCRIMINANT MODESTE** — range Sharpe 0.508-0.585 (écart 0.08, le plus grand des sweeps XGBoost). max_pos=12 winner en capital final + drawdown -30.62% (le moins creux des 3). **Verdict attendu** : plus de diversification améliore la perf. **Mais toutes configs sous SPY B&H** (~2.3× vs 2.9×).

## xgb-h5-subsample.png

- **Description visuelle** : Figure 1000×712 (191 Ko) **dual-panel matplotlib-blanc** (L778-L2 tell RGB dominant `(246, 246, 245)` vérifié firsthand MiniMax M3 + PIL, bg blanc 82% — figure la plus claire du lot, palette `tab:blue`/`tab:orange`/`tab:green`/`tab:red` standard matplotlib) :
  - **Panneau haut « H5: Subsample Ratio »** : 3 courbes equity 2018-2026, sweep **DISCRIMINANT MODESTE** visible fin 2024-25, subsample=1.0 VERT winner :
    - `subsample=0.6` bleu tab: S=0.527, DD=-35.55% — perdant
    - `subsample=0.8` orange tab: S=0.564, DD=-37.29% — current default
    - `subsample=1.0` vert tab: S=0.593, DD=-39.58% — **winner** (pas de subsampling = MIEUX)
    - SPY Buy-Hold rouge tab : S=0.778, DD=-33.72%, capital 1.0 → 2.9
  - **Panneau bas « Drawdowns »** : 3 aires bleues/orange/vert + aire rose SPY, mêmes teintes ; DD range visible -20% à -45%.
  - Légende unique panneau haut (4 entrées), axes annotés, grille légère grise.
- **Haut** « H5: Subsample Ratio » 2018-2026, 3 courbes XGBoost :
  - `subsample=0.6` bleu : S=0.527, DD=-35.55% (perdant)
  - `subsample=0.8` orange : S=0.564, DD=-37.29% (current, default)
  - `subsample=1.0` vert : S=0.593, DD=-39.58% (**winner**, pas de subsampling = MIEUX)
- **Bas** « Drawdowns » 2018-2026
- **Verdict** : **sweep DISCRIMINANT MODESTE** — range Sharpe 0.527-0.593 (écart 0.07). subsample=1.0 winner. **Verdict contre-intuitif** : supprimer le subsampling (utiliser 100% des données par arbre) **améliore** la perf — pour XGBoost sur ces 15 tickers, le bagging n'apporte rien. **Mais toutes configs sous SPY B&H** (~2.2× vs 2.9×).

## xgb-synthese.png

- **Description visuelle** : Figure 989×790 (43 Ko) **mono-panel matplotlib-blanc bar-chart** (L778-L2 tell RGB dominant `(246, 246, 246)` vérifié firsthand MiniMax M3 + PIL, bg blanc 80%, barres `steelblue` `#4682B4` standard matplotlib `ax.barh()`) :
  - **Bar chart horizontal** « Feature Importance (GradientBoosting, moyenne sur tous les entrainements) », 22 barres bleues triées desc, axe X = importance [0.00 → 0.12], axe Y = nom feature (texte noir), sans légende (auto-suffisant via titre) :
    - **vol_20 ~0.122** winner (vs perdant 0.076 dans ML-RandomForest = **INVERSION**)
    - **atr ~0.095** / **macd_signal ~0.088** / **atr_ratio ~0.085** (cluster volatilité+momentum top-4)
    - **sma_ratio_10_50 ~0.078** / **price_sma50 ~0.055**
    - **vol_5 ~0.053** / **bb_width ~0.052** / **macd ~0.053** / **macd_hist ~0.048** / **mom_20 ~0.038**
    - **sma_ratio_5_20 ~0.034** / **mom_10 ~0.030** / **rsi ~0.026** / **price_sma20 ~0.025** / **mom_5 ~0.024**
    - **price_sma5 ~0.023** / **stoch_d ~0.020** / **bb_position ~0.018** (vs winner 0.103 dans ML-RandomForest = **2ᵉ inversion**)
    - **returns ~0.014** / **stoch_k ~0.010**
    - **volume_ratio ~0.000** quasi-nul
    - **volume_change ~0.000** quasi-nul
  - Pas de légende (chart self-explanatory via titres axes + nom features), grille verticale légère grise, espacement régulier entre barres.
- **Bar chart horizontal** « Feature Importance (GradientBoosting, moyenne sur tous les entrainements) », 22 barres bleues triées desc :
  - **vol_20 ~0.122** winner (vs perdant 0.076 dans ML-RandomForest = **inversion spectaculaire**)
  - **atr ~0.095** / **macd_signal ~0.088** / **atr_ratio ~0.085** (cluster volatilité+momentum top-4)
  - **sma_ratio_10_50 ~0.078** / **price_sma50 ~0.055**
  - **vol_5 ~0.053** / **bb_width ~0.052** / **macd ~0.053** / **macd_hist ~0.048** / **mom_20 ~0.038**
  - **sma_ratio_5_20 ~0.034** / **mom_10 ~0.030** / **rsi ~0.026** / **price_sma20 ~0.025** / **mom_5 ~0.024**
  - **price_sma5 ~0.023** / **stoch_d ~0.020** / **bb_position ~0.018** (vs winner 0.103 dans ML-RandomForest = **2ᵉ inversion**)
  - **returns ~0.014** / **stoch_k ~0.010**
  - **volume_ratio ~0.000** quasi-nul
  - **volume_change ~0.000** quasi-nul
- **Verdict** : **INVERSION SPECTACULAIRE vs ML-RandomForest** :
  - vol_20 passe de perdant (mrf) à **winner** (xgb) — XGBoost exploite fortement la volatilité 20j
  - bb_position passe de winner (mrf) à perdant (xgb) — momentum/position Bollinger marginal pour XGBoost
  - volume_ratio quasi-nul dans les 2 cas
  - **Hypothèse** : XGBoost gère mieux les features de **volatilité** (vol_20, atr, atr_ratio) via ses tree splits séquentiels avec shrinkage, alors que RandomForest distribue l'importance entre features de **momentum** (bb_position) et volume均等ément. Pour XGBoost : **les features de VOLATILITÉ dominent**, momentum marginal.

---

## Découverte majeure c.453 — XGBoost sous-performe SPY B&H systématiquement

**Contrairement à ML-RandomForest c.452 où 4 winners sur 5 battent SPY**, **ML-XGBoost c.453 sous-performe SPY Buy-Hold sur TOUS les sweeps** :

| Sweep | Sharpe XGBoost range | Sharpe SPY | Capital XGBoost | Capital SPY |
|---|---|---|---|---|
| H1 learning_rate | 0.538-0.57 | 0.778 | ~2.1× | 2.9× |
| H2 n_estimators | 0.564-0.6 | 0.778 | ~2.1× | 2.9× |
| H3 threshold | 0.534-0.591 | 0.778 | ~2.2× | 2.9× |
| H4 max_positions | 0.508-0.585 | 0.778 | ~2.3× | 2.9× |
| H5 subsample | 0.527-0.593 | 0.778 | ~2.2× | 2.9× |

**Conclusion** : la stratégie XGBoost ML est **NÉGATIVEMENT valorisée** par rapport au benchmark SPY B&H sur 2018-2026. **L'algo ML XGBoost ne bat pas le simple buy-and-hold** sur la période. C'est un signal FORT contre le déploiement live de XGBoost sans amélioration substantielle (vs ML-RandomForest qui gagne 2-3× SPY avec hyperparamètres optimaux).

**Hypothèses d'amélioration** (hors scope cette PR, à investiguer en suivi) :
1. Combiner XGBoost + RandomForest (ensemble methods, déjà vu `ML-Ensemble` project)
2. Ajouter features de régime VIX comme dans `LongShortHarvest-QC` c.451
3. Filtrer les jours VIX>25 (cf c.451 finding : Stress S=-0.2 négatif)
4. Backtester sur une période plus longue (2008-2026) pour vérifier la robustesse

## Comparaison c.453 ML-XGBoost vs c.452 ML-RandomForest

| Métrique | ML-RandomForest c.452 | ML-XGBoost c.453 |
|---|---|---|
| Sharpe winners | 0.841-1.118 (range 0.28) | 0.508-0.593 (range 0.085) |
| vs SPY (S=0.778) | 4/5 winners BATTENT SPY | **0/15 configs BATTENT SPY** |
| MaxDD winners | -30% à -41% | -30% à -49% |
| Sweeps DISCRIMINANTS | 5/5 (range 0.6 Sharpe) | 3/5 modestes (H3+H4+H5 range 0.07) + 2/5 NULS (H1+H2 range 0.03) |
| Feature #1 | bb_position (momentum, ~0.103) | **vol_20 (volatilité, ~0.122)** ← inversion |
| Feature dernière significative | volume_ratio (~0.002) | **bb_position (~0.018)** ← inversion |
| Verdict global | **Stratégie VIABLE**, 3 hyperparamètres à activer (depth=10, Universe 5, Monthly rebal) → ~3× SPY | **Stratégie NON VIABLE vs SPY**, à reconsidérer ou améliorer fondamentalement |

## Cumul EPIC #5780 vague QC

| Cycle | PR | Projet | Figures | Sous-pattern dominant |
|-------|----|---------|---------|----------------------|
| c.438 | #6541 | DualMomentum | 4 | systemic 4:4 |
| c.447 | #6655 | AllWeather | 6 | systemic 5:1 |
| c.448 | #6656 | EMA-Cross-Crypto | 5 | doctrinal 5:5 + dual-panel |
| c.449 | #6661 | EMA-Cross-Index | 6 | doctrinal 6:6 + dual/triple-panel |
| c.450 | #6668 | ForexCarry | 6 | doctrinal 6:6 + 2 ATTRIB inversées |
| c.451 | #6671 | LongShortHarvest-QC | 6 | doctrinal 6:6 + 3 sweeps NULS (sous-pattern d) |
| c.452 | #6674 | ML-RandomForest | 6 | doctrinal 6:6 + 5 sweeps DISCRIMINANTS (sous-pattern e) |
| **c.453** | **this PR** | **ML-XGBoost** | **6** | **doctrinal 6:6 + 2 sweeps NULS + 3 sweeps DISCRIMINANTS modestes + inversion feature importance + sous-perf SPY systématique** |

**13/16 projets QC couverts**. Reste : RiskParity (6) = ~6 figures restantes, ~1 PR.

## Sous-pattern émergent c.453 — DOUBLE-NATURE NULS+DISCRIMINANTS

Les 5 sweeps de ML-XGBoost montrent une **double nature** unique parmi les 8 projets QC audités :
- **H1 (learning_rate) + H2 (n_estimators)** = sweeps **QUASI-NULS** (range Sharpe 0.03-0.04) → analogie c.451 LongShortHarvest-QC
- **H3 (threshold) + H4 (max_positions) + H5 (subsample)** = sweeps **DISCRIMINANTS MODESTES** (range Sharpe 0.06-0.08) → analogie c.452 RandomForest (mais avec amplitudes 5-10× plus faibles)

Le pipeline `extract_readme_figures.py` ne capture **aucune de ces deux nuances** : il génère dans tous les cas un alt-text générique « Courbes par sweep » qui omet à la fois la mention sweep nul vs discriminant, ET l'écart d'amplitude (modeste vs discriminant).

**Cause racinaire confirmée** : alt-texts générés par **auto-extraction à partir des commentaires de cellule** (e.g. `# H1: Learning rate` → alt-text « Learning rate (hypothèse 1) »), sans lecture visuelle du PNG. Aucun des 6 alt-texts ne contient de valeur Sharpe, MaxDD, verdict winner/perdant, ni verdict SPY B&H sous-perf systématique. Corrigé c.453 par audit visuel MiniMax M3 + vérification croisée du code source des cellules.

## Preuves vérifiables (G.1 firsthand)

- 6/6 PNG ouverts via `Read` (vision MiniMax M3), analysés et décrits dans ce MANIFEST enrichi
- 6/6 attributions cell×output confirmées via `python json.load(research.ipynb)` + matching `set_title()` :
  - `xgb-h1-learningrate.png` → cell[11] out[4] ✓ (`plot_equity_curves(h1_results, title='H1: Learning Rate')`)
  - `xgb-h2-nestimators.png` → cell[14] out[4] ✓ (`plot_equity_curves(h2_results, title='H2: N Estimators')`)
  - `xgb-h3-threshold.png` → cell[17] out[4] ✓ (`plot_equity_curves(h3_results, title='H3: Prediction Threshold')`)
  - `xgb-h4-maxpositions.png` → cell[20] out[4] ✓ (`plot_equity_curves(h4_results, title='H4: Max Positions')`)
  - `xgb-h5-subsample.png` → cell[23] out[4] ✓ (`plot_equity_curves(h5_results, title='H5: Subsample Ratio')`)
  - `xgb-synthese.png` → cell[26] out[0] ✓ (`ax.set_title('Feature Importance (GradientBoosting, moyenne sur tous les entrainements)', fontsize=13)`)

## Hygiene PR (catalog-pr-hygiene)

- **R1** : 1 fichier modifié (`MANIFEST.md`), 0 marqueur `CATALOG-STATUS` touché ✓
- **R2** : rebase frais sur `origin/main` @ `a909142e6` ✓
- **R3** : 1 sujet = audit MANIFEST ML-XGBoost (atomique) ✓
- **R4** : `See #5780` (contribution partielle à l'epic, ne ferme pas) ✓
