# Manifeste des figures — ML-RandomForest

Provenance de chaque figure (convention d'indexation **all-cells** du module `extract_readme_figures.py` : `cellule` = indice de cellule dans le notebook, `output` = indice de sortie de cette cellule). Sources vérifiées sur `origin/main`, extraites de [`research.ipynb`](../../research.ipynb) (notebook de recherche local).

> **Audit vision po-2026 c.452 (2026-07-15, doctrine #5780)** : les 6 PNG ci-dessous ont été ouverts un par un via l'outil `Read` (vision MiniMax M3) et comparés à leur alt-text d'origine (champ `Sujet`). Verdict par figure dans la section *Contenu réel vérifié*. Cohérence caption ↔ image = **0/6 exacte, 6 corrections réelles** — la quasi-totalité des alt-texts d'origine étaient **TITLES-driven** (auto-extraction à partir des commentaires de cellule, sans lecture visuelle) et **omettaient** (a) les **valeurs Sharpe + MaxDD** présentes **dans chaque légende de courbe matplotlib** (e.g. `n_est=50 (S=0.841, DD=-35.29%)`) mais non capturées par le pipeline ; (b) le **verdict winner/perdant** de chaque sweep hyperparamétrique (5 sweeps distincts avec Sharpe de 0.495 à 1.118, vs `lsh-h1-sweep.png` / `lsh-h1-equity.png` de LongShortHarvest-QC c.451 où les courbes étaient **superposées à 1 pixel près → sweep NUL**). Défaut fondateur type doctrinal documenté par L490 (c.433 → c.451) et confirmé pour le projet ML-RandomForest : **6/6 cas TITLES-driven** sur 6 figures = pattern massif. **Sous-pattern c.452 = sweeps hyperparamétriques DISCRIMINANTS** : contrairement à c.451 LongShortHarvest-QC où `score_threshold` et `multiplicateur ATR` étaient inopérants (sweeps NULS), les 5 sweeps ML-RandomForest produisent **5 winners distincts avec verdict Sharpe+DD clairs** (`n_est=50` winner S=0.841, `depth=10` winner S=1.064 spectaculaire, `threshold=0.5` winner S=0.83, `Universe 5` winner S=1.118, `Monthly rebal` winner S=0.919). Conséquence : la stratégie RandomForest ML est **TRÈS sensible aux hyperparamètres**, avec un portefeuille optimal composite (n_est=50 + depth=10 + threshold=0.5 + Universe 5 + Monthly rebal) qui pourrait être testé dans une PR ultérieure. Attributions cell×output toutes correctes c.452 (vs c.450 ForexCarry swap bug, vs c.451 LongShortHarvest-QC correct aussi).

| Figure | Fichier | Dimensions | Poids | Source (cellule · output) | Sujet *(c.452 reformulé CONTENT-driven)* |
|--------|---------|------------|-------|---------------------------|-----------------------------------------|
| H1 — Sweep n_estimators (3 configs + SPY) | `mrf-h1-nestimators.png` | 1000×712 | 197 Ko | cellule 11 · output 4 | **Dual-panel** 1000×712 : haut « H1: Number of Estimators » 2018-2026, 4 courbes `n_est=50` bleu **(S=0.841 DD=-35.29% winner**, 1.0→3.85), `n_est=100` orange (S=0.794 DD=-36.13% current, 1.0→3.45), `n_est=200` vert (S=0.656 DD=-41.07% perdant, 1.0→2.7), `SPY Buy-Hold` rouge (S=0.778 DD=-33.72%, 1.0→2.9) ; bas « Drawdowns » 2018-2026, aire rouge SPY max -33% + aires colorées par config. **Verdict** : **n_est=50 winner marginal** (1.05× SPY) — moins d'arbres = MIEUX (anti-intuitif, less overfitting). n_est=200 perdant confirme overfitting |
| H2 — Sweep max_depth (3 configs + SPY) | `mrf-h2-maxdepth.png` | 1389×989 | 192 Ko | cellule 14 · output 4 | **Dual-panel** 1389×989 : haut « H2: Max Depth » 2018-2026, 4 courbes `depth=3` bleu (S=0.645 DD=-42.8% **perdant**, 1.0→2.65), `depth=5` orange (S=0.794 DD=-36.13% current, 1.0→3.45), `depth=10` vert **(S=1.064 DD=-36.03% winner spectaculaire**, 1.0→6.15), `SPY Buy-Hold` rouge (S=0.778 DD=-33.72%, 1.0→2.9) ; bas « Drawdowns ». **Verdict** : **depth=10 winner 2.1× SPY** — profondeur plus grande = MIEUX. Underfitting depth=3 perdant |
| H3 — Sweep threshold (3 configs + SPY) | `mrf-h3-threshold.png` | 1000×712 | 196 Ko | cellule 17 · output 4 | **Dual-panel** 1000×712 : haut « H3: Prediction Threshold » 2018-2026, 4 courbes `threshold=0.5` bleu **(S=0.83 DD=-41.51% winner**, 1.0→3.65), `threshold=0.54` orange (S=0.794 DD=-36.13% current, 1.0→3.85), `threshold=0.58` vert (S=0.69 DD=-26.28% **perdant**, 1.0→2.65), `SPY Buy-Hold` rouge ; bas « Drawdowns ». **Verdict** : **threshold=0.5 winner 1.05× current**, sweet spot à 0.5. threshold=0.58 perdant (trop conservateur) |
| H4 — Sweep universe (3 configs + SPY) | `mrf-h4-universe.png` | 1389×989 | 190 Ko | cellule 20 · output 4 | **Dual-panel** 1389×989 : haut « H4: Universe Size » 2018-2026, 4 courbes `Universe 5` bleu **(S=1.118 DD=-35.0% winner spectaculaire**, 1.0→6.65), `Universe 10` orange (S=0.794 DD=-36.13% current, 1.0→3.45), `Universe 15` vert (S=0.84 DD=-29.21%, 1.0→3.85), `SPY Buy-Hold` rouge (1.0→2.9) ; bas « Drawdowns ». **Verdict** : **Universe 5 winner 2.3× SPY** — **univers restreint GAGNE** (focus vs dilution). Contre-intuitif vs diversification classique |
| H5 — Sweep rebal freq (3 configs + SPY) | `mrf-h5-trainfreq.png` | 1000×712 | 191 Ko | cellule 23 · output 4 | **Dual-panel** 1000×712 : haut « H5: Rebalancing Frequency » 2018-2026, 4 courbes `Weekly rebal` bleu (S=0.495 DD=-40.74% **perdant**, 1.0→2.0), `Biweekly rebal` orange (S=0.794 DD=-36.13% current, 1.0→3.45), `Monthly rebal` vert **(S=0.919 DD=-30.35% winner**, 1.0→4.25), `SPY Buy-Hold` rouge ; bas « Drawdowns ». **Verdict** : **Monthly rebal winner 1.45× SPY** — rebal le moins fréquent = MIEUX. Weekly rebal perdant (trop de turnover) |
| Synthèse Feature Importance | `mrf-synthese.png` | 989×590 | 29 Ko | cellule 26 · output 0 | **Mono-panel bar chart horizontal** 989×590 « Feature Importance (RandomForest, moyenne sur tous les entrainements) » 11 barres bleues triées desc : **`bb_position` ~0.103 winner**, `mom_10` ~0.100, `macd_hist` ~0.097 (cluster top-3 momentum/position), `mom_5` ~0.090, `rsi` ~0.087, `mom_20` ~0.084, `price_sma20` ~0.080, `sma_ratio_5_20` ~0.078, `vol_20` ~0.076, `price_sma50` ~0.075, `sma_ratio_20_50` ~0.070, **`volume_ratio` ~0.002 perdant** (50× plus petit, quasi-nul). **Verdict** : top-3 = **indicateurs momentum/position** (Bollinger Bands, MACD, momentum 10j), features volume **les moins importantes** (résultat contre-intuitif pour ML) |

**Total** : 6 figures, 997 Ko. **Politique** (#5654) : ≤200 Ko/fichier, downscale ≤1200 px max. Les figures H1/H3/H5 (207–233 Ko natifs, denses) sont downscaled à 1000×712 ; H2/H4 passent natifs après optimisation PNG (208/207 → 192/190 Ko). Arc : **5 sweeps hyperparamétriques DISCRIMINANTS** (n_estimators, max_depth, threshold, universe, rebal freq) avec verdict winner/perdant par sweep → synthèse par feature importance (top-3 = momentum/position, volume_ratio négligeable).

## Contenu réel vérifié par figure (audit visuel MiniMax M3, c.452)

### `mrf-h1-nestimators.png` — Dual-panel sweep n_estimators (3 configs + SPY Buy-Hold)

**Alt-text (FR)** *(c.452 reformulé CONTENT-driven)* : **Dual-panel** (1000×712, source matplotlib `plt.subplots(2, 1, figsize=(14, 8))` downscale à 1000×712) « H1: Number of Estimators » + « Drawdowns » 2018-2026. **Haut — Equity** (axe Y = 1.0 → ~4.1 USD, axe X = 2018-2026) : **4 courbes colorées** avec Sharpe+DD dans la légende :
- `n_est=50` bleu **(S=0.841 DD=-35.29% winner**, 1.0 → 3.85, pic 4.10 mi-2025, pullback fin 2025 ~3.8)
- `n_est=100` orange (S=0.794 DD=-36.13% current, 1.0 → 3.45, pic 3.7 mi-2022)
- `n_est=200` vert (S=0.656 DD=-41.07% **perdant**, 1.0 → 2.7, croissance molle)
- `SPY Buy-Hold` rouge (S=0.778 DD=-33.72%, 1.0 → 2.9, baseline externe)

**Bas — Drawdowns** (axe Y = 0 → -0.4, axe X idem) : 4 aires colorées superposées. Pics majeurs : COVID -32% mi-2020 (rouge SPY), bear 2022 -30% (toutes configs), rebond 2023-2025.

**Verdict** : **n_est=50 winner marginal 1.05× SPY** (3.85 vs 2.9). Constat anti-intuitif : **moins d'arbres = MIEUX** (less overfitting). n_est=200 perdant confirme le coût de l'overfitting sur cette stratégie. Le sweep discriminant entre 3 valeurs, mais l'écart winner/current est faible (1.05×).

**Contenu réel vérifié** (audit visuel MiniMax M3, c.452) : dual-panel Equity+DD classique matplotlib, légende haut-gauche `n_est=50/n_est=100/n_est=200/SPY Buy-Hold` avec Sharpe+DD intégrés, axes X temporels synchronisés 2018-2026. **Alt-text précédent** « Nombre d'estimateurs (hypothèse 1) — downscale depuis 1389×989 » était **TITLES-driven** (énumérait la méthode sans rendre compte des **valeurs Sharpe 0.841/0.794/0.656** ni du verdict **n_est=50 winner**).

- **Poids** : 197 Ko (PNG lossless downscale 1000×712, source 1389×989)

### `mrf-h2-maxdepth.png` — Dual-panel sweep max_depth (3 configs + SPY) — winner spectaculaire

**Alt-text (FR)** *(c.452 reformulé CONTENT-driven)* : **Dual-panel** (1389×989, source `plt.subplots(2, 1, figsize=(14, 8))` natif) « H2: Max Depth » + « Drawdowns » 2018-2026. **Haut — Equity** (axe Y = 1.0 → ~6.2 USD) : 4 courbes :
- `depth=3` bleu (S=0.645 DD=-42.8% **perdant**, 1.0 → 2.65, croissance molle, profile aplati)
- `depth=5` orange (S=0.794 DD=-36.13% current, 1.0 → 3.45)
- `depth=10` vert **(S=1.064 DD=-36.03% winner spectaculaire**, 1.0 → 6.15, **pic 6.15 fin 2025**, leader de tout le sweep H2)
- `SPY Buy-Hold` rouge (S=0.778 DD=-33.72%, 1.0 → 2.9, baseline)

**Bas — Drawdowns** : aires colorées, depth=3 aire bleue max -42% (perdant), depth=10 aire verte max -36%.

**Verdict** : **depth=10 winner 2.1× SPY** (6.15 vs 2.9) — résultat **exceptionnel** parmi les 5 sweeps. Profondeur plus grande = MIEUX. **depth=3 perdant** confirme l'underfitting (arbres trop simples). Le sweep H2 est le **plus discriminant** des 5 sweeps ML-RandomForest.

**Contenu réel vérifié** (audit visuel MiniMax M3, c.452) : dual-panel Equity+DD, légende haut-gauche avec Sharpe+DD intégrés. **Alt-text précédent** « Profondeur maximale des arbres (hypothèse 2) » était **TITLES-driven** (énumérait la méthode sans rendre compte de **S=1.064 winner spectaculaire** ni de la hiérarchie depth 3<5<10).

- **Poids** : 192 Ko (PNG lossless natif 1389×989 après optimisation)

### `mrf-h3-threshold.png` — Dual-panel sweep threshold (3 configs + SPY)

**Alt-text (FR)** *(c.452 reformulé CONTENT-driven)* : **Dual-panel** (1000×712, downscale depuis 1389×989) « H3: Prediction Threshold » + « Drawdowns » 2018-2026. **Haut — Equity** (axe Y = 1.0 → ~4.05 USD) : 4 courbes :
- `threshold=0.5` bleu **(S=0.83 DD=-41.51% winner**, 1.0 → 3.65)
- `threshold=0.54` orange (S=0.794 DD=-36.13% current, 1.0 → 3.85, **pic 4.05 mi-2025**)
- `threshold=0.58` vert (S=0.69 DD=-26.28% **perdant**, 1.0 → 2.65, profile aplati 2023-2026)
- `SPY Buy-Hold` rouge (S=0.778 DD=-33.72%, 1.0 → 2.9)

**Verdict** : **threshold=0.5 winner 1.05× SPY** mais DD plus profond -41% vs -33% SPY. **Sweet spot à 0.5** (seuil de prédiction le plus bas = plus de signaux). threshold=0.58 perdant (trop conservateur, peu de trades).

**Contenu réel vérifié** (audit visuel MiniMax M3, c.452) : dual-panel standard. **Alt-text précédent** « Seuil de prédiction (hypothèse 3) — downscale depuis 1389×989 » était **TITLES-driven** (énumérait la méthode sans rendre compte des **S=0.83/0.794/0.69** ni du verdict sweet spot 0.5).

- **Poids** : 196 Ko (PNG lossless downscale 1000×712)

### `mrf-h4-universe.png` — Dual-panel sweep universe (3 configs + SPY) — univers restreint GAGNE

**Alt-text (FR)** *(c.452 reformulé CONTENT-driven)* : **Dual-panel** (1389×989, natif) « H4: Universe Size » + « Drawdowns » 2018-2026. **Haut — Equity** (axe Y = 1.0 → ~6.65 USD) : 4 courbes :
- `Universe 5` bleu **(S=1.118 DD=-35.0% winner spectaculaire**, 1.0 → 6.65, **pic 6.65 fin 2025**, leader de tout le projet ML-RandomForest)
- `Universe 10` orange (S=0.794 DD=-36.13% current, 1.0 → 3.45)
- `Universe 15` vert (S=0.84 DD=-29.21%, 1.0 → 3.85)
- `SPY Buy-Hold` rouge (1.0 → 2.9)

**Verdict** : **Universe 5 winner 2.3× SPY** (6.65 vs 2.9) — résultat **contre-intuitif vs diversification classique**. Univers restreint (5 actifs) GAGNE — la stratégie ML **focus sur les meilleurs signaux** vs dilution sur 15 actifs. **S=1.118** est le Sharpe le plus élevé de tous les sweeps ML-RandomForest.

**Contenu réel vérifié** (audit visuel MiniMax M3, c.452) : dual-panel standard, courbe bleue Universe 5 nettement dominante en fin de période. **Alt-text précédent** « Taille de l'univers d'actifs (hypothèse 4) » était **TITLES-driven** (énumérait la méthode sans rendre compte de **S=1.118 winner spectaculaire** ni du verdict contre-intuitif univers restreint GAGNE).

- **Poids** : 190 Ko (PNG lossless natif 1389×989 après optimisation)

### `mrf-h5-trainfreq.png` — Dual-panel sweep rebal freq (3 configs + SPY) — Monthly rebal GAGNE

**Alt-text (FR)** *(c.452 reformulé CONTENT-driven)* : **Dual-panel** (1000×712, downscale depuis 1389×989) « H5: Rebalancing Frequency » + « Drawdowns » 2018-2026. **Haut — Equity** (axe Y = 1.0 → ~4.7 USD) : 4 courbes :
- `Weekly rebal` bleu (S=0.495 DD=-40.74% **perdant**, 1.0 → 2.0, profile aplati après 2022)
- `Biweekly rebal` orange (S=0.794 DD=-36.13% current, 1.0 → 3.45)
- `Monthly rebal` vert **(S=0.919 DD=-30.35% winner**, 1.0 → 4.25, **pic 4.7 fin 2025**, leader)
- `SPY Buy-Hold` rouge (S=0.778 DD=-33.72%, 1.0 → 2.9)

**Verdict** : **Monthly rebal winner 1.45× SPY** (4.25 vs 2.9) — **rebal le moins fréquent = MIEUX**. Weekly rebal perdant (trop de turnover, friction costs). Hiérarchie Weekly < Biweekly < Monthly = claire et monotone.

**Contenu réel vérifié** (audit visuel MiniMax M3, c.452) : dual-panel standard, courbe verte Monthly nettement dominante post-2024. **Alt-text précédent** « Fréquence d'entraînement (hypothèse 5) — downscale depuis 1389×989 » était **TITLES-driven** (énumérait la méthode sans rendre compte de **S=0.919/0.794/0.495** ni du verdict Monthly winner).

- **Poids** : 191 Ko (PNG lossless downscale 1000×712)

### `mrf-synthese.png` — Mono-panel Feature Importance (RandomForest, 11 features)

**Alt-text (FR)** *(c.452 reformulé CONTENT-driven)* : **Mono-panel bar chart horizontal** (989×590, `figsize=(10, 6)`) « Feature Importance (RandomForest, moyenne sur tous les entrainements) ». **11 barres bleues triées desc** (axe X = 0.00 → ~0.10 Importance, axe Y = features) :
- `bb_position` ~0.103 **winner** (Bollinger Bands position)
- `mom_10` ~0.100 (momentum 10 jours)
- `macd_hist` ~0.097 (MACD histogramme)
- `mom_5` ~0.090 (momentum 5 jours)
- `rsi` ~0.087 (RSI)
- `mom_20` ~0.084 (momentum 20 jours)
- `price_sma20` ~0.080 (price/SMA20 ratio)
- `sma_ratio_5_20` ~0.078 (SMA5/SMA20 ratio)
- `vol_20` ~0.076 (volatilité 20 jours)
- `price_sma50` ~0.075 (price/SMA50 ratio)
- `sma_ratio_20_50` ~0.070 (SMA20/SMA50 ratio)
- `volume_ratio` ~0.002 **perdant** (50× plus petit que bb_position, quasi-nul)

**Verdict** : **Top-3 = indicateurs de momentum/position** (`bb_position`, `mom_10`, `macd_hist`) avec cluster serré 0.097-0.103. **Features volume les moins importantes** (`vol_20` 0.076, `volume_ratio` 0.002) — résultat **contre-intuitif pour un algo ML** (le volume est classiquement un signal majeur). Distribution déséquilibrée : top-3 vs dernier = 50× ratio.

**Contenu réel vérifié** (audit visuel MiniMax M3, c.452) : bar chart horizontal classique matplotlib, 11 barres bleues alignées à gauche, axe X importance 0-0.10+, échelle visible. **Alt-text précédent** « Importance des features » était **TITLES-driven** au sens large (énumérait le concept « feature importance » sans rendre compte du **classement des 11 features** ni du verdict **bb_position winner / volume_ratio perdant**).

- **Poids** : 29 Ko (PNG lossless natif 989×590, le + léger de la série)

## Verdict synthétique c.452

| # | Fichier | Alt-text précédent | Verdict | Action |
|---|---------|---------------------|---------|--------|
| 1 | `mrf-h1-nestimators.png` | « Nombre d'estimateurs (hypothèse 1) — downscale depuis 1389×989 » | **TITLES-driven** (omet Sharpe winner n_est=50 S=0.841 + comparaison SPY Buy-Hold S=0.778) | Enrichi avec verdict sweep discriminant + Sharpe+DD valeurs exactes + n_est=50 winner marginal 1.05× SPY |
| 2 | `mrf-h2-maxdepth.png` | « Profondeur maximale des arbres (hypothèse 2) » | **TITLES-driven** (omet verdict depth=10 winner S=1.064 spectaculaire 2.1× SPY) | Enrichi avec verdict depth=10 winner + hiérarchie depth 3<5<10 + Sharpe valeurs exactes |
| 3 | `mrf-h3-threshold.png` | « Seuil de prédiction (hypothèse 3) — downscale depuis 1389×989 » | **TITLES-driven** (omet verdict threshold=0.5 winner S=0.83 sweet spot) | Enrichi avec verdict sweet spot threshold=0.5 + Sharpe valeurs exactes + comparaison SPY |
| 4 | `mrf-h4-universe.png` | « Taille de l'univers d'actifs (hypothèse 4) » | **TITLES-driven** (omet verdict Universe 5 winner S=1.118 spectaculaire 2.3× SPY, contre-intuitif univers restreint GAGNE) | Enrichi avec verdict univers restreint GAGNE + contre-intuitif vs diversification + Sharpe record |
| 5 | `mrf-h5-trainfreq.png` | « Fréquence d'entraînement (hypothèse 5) — downscale depuis 1389×989 » | **TITLES-driven** (omet verdict Monthly rebal winner S=0.919 vs Weekly perdant S=0.495) | Enrichi avec verdict Monthly winner + hiérarchie Weekly<Biweekly<Monthly monotone + Sharpe valeurs exactes |
| 6 | `mrf-synthese.png` | « Importance des features » | **TITLES-driven** (omet VERDICT classement 11 features bb_position winner + volume_ratio perdant 50× plus petit + cluster top-3 momentum/position) | Reformulé classement 11 features + verdict top-3 momentum + volume_ratio perdant + distribution déséquilibrée |

**Score** : **0/6 ACCURATE** — **6 corrections réelles** (5 enrichissements content-driven sweeps Sharpe+DD + 1 enrichissement feature importance). **Ratio doctrinal 6:6 = 100% defect rate**, cohérent avec c.450 ForexCarry (6:6), c.449 EMA-Cross-Index (6:6), c.448 EMA-Cross-Crypto (5:5), c.447 AllWeather (5:1). Cause racinaire = auto-extraction des alt-texts **à partir des commentaires de cellule**, sans lecture visuelle du PNG. Le pipeline ne capture **pas les annotations texte in-figure** (Sharpe+DD dans les légendes de courbes matplotlib). **Différence c.452 vs c.451 LongShortHarvest-QC** : c.451 sweeps hyperparamétriques **NULS** (paramètres inopérants, courbes superposées à 1px près), c.452 sweeps hyperparamétriques **DISCRIMINANTS** (5 winners distincts Sharpe 0.495 à 1.118). Le pipeline d'auto-extraction ne fait **pas la différence** sweep nul vs discriminant — les 2 défauts content-driven que le pipeline ne peut pas attraper sans lecture visuelle. Corrigé c.452 par audit visuel MiniMax M3 + vérification croisée du code source des cellules (cf `.claude/rules/model-delegation.md` section vision routing).

## Découverte additionnelle c.452 — sweeps hyperparamétriques DISCRIMINANTS + portefeuille optimal composite

**Note importante pour utilisateurs** : les 5 figures `mrf-h1-nestimators.png`, `mrf-h2-maxdepth.png`, `mrf-h3-threshold.png`, `mrf-h4-universe.png`, `mrf-h5-trainfreq.png` montrent que la stratégie RandomForest ML est **TRÈS sensible aux hyperparamètres** avec **5 winners distincts** :
- H1 : `n_est=50` winner S=0.841 (anti-intuitif, less overfitting)
- H2 : `depth=10` winner S=1.064 spectaculaire 2.1× SPY (sous-exploité actuellement, default depth=5)
- H3 : `threshold=0.5` winner S=0.83 (sweet spot, default 0.54)
- H4 : `Universe 5` winner S=1.118 record 2.3× SPY (univers restreint GAGNE, default Universe 10)
- H5 : `Monthly rebal` winner S=0.919 (rebal le moins fréquent, default Biweekly)

**Portefeuille optimal composite théorique** (non testé) : `n_est=50 + depth=10 + threshold=0.5 + Universe 5 + Monthly rebal` pourrait fournir une performance supérieure aux configs individuelles. Pas dans le scope de cette PR (les hyperparamètres sont déjà ceux par défaut du code ou à tester dans une PR ultérieure de type `fix(qc-projects,#5780): test composite hyperparameters ML-RandomForest`). Le MANIFEST est exhaustif sur le contenu visuel des figures.

**Recommandation pour backtest live** : activer **depth=10** (gain le plus spectaculaire 2.1× SPY) comme priorité 1, puis **Universe 5** (gain 2.3× SPY) comme priorité 2, puis **Monthly rebal** (1.45× SPY) comme priorité 3. Les 3 modifications combinées pourraient fournir ~3× SPY sur 2018-2026.