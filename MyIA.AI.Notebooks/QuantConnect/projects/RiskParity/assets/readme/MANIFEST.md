# Manifeste des figures — RiskParity

Provenance de chaque figure (convention d'indexation **all-cells** du module `extract_readme_figures.py` : `cellule` = indice de cellule dans le notebook, `output` = indice de sortie de cette cellule). Sources vérifiées sur `origin/main`, extraites de [`research.ipynb`](../../research.ipynb) (notebook de recherche local).

> **Audit vision fondateur c.454 (2026-07-15, doctrine #5780, po-2024 lane)** : les 6 PNG ci-dessous ont été ouverts un par un via l'outil `Read` (vision MiniMax M3) et comparés à leur alt-text d'origine (champ `Sujet`). Verdict par figure dans la section *Contenu réel vérifié*. Cohérence caption ↔ image = **0/6 exacte, 6 corrections content-driven appliquées** — **défaut fondateur type (g) CONTENT-DRIFTED uniforme** (vs pattern dual-panel-invisible L490 ou inversions-factuelles c.448-c.449) : les alt-texts d'origine étaient **génériquement justes** (ils nomment bien l'hypothèse H1/H2/H3/H4 et le thème), mais **omettaient** (a) la **structure multi-panel** (dual/triple/quad-panel invisible), (b) les **valeurs mesurées** (Sharpe, MaxDD, rendements par régime, % contribution au risque), (c) les **verdicts discriminants** (winner lookback 40j, GLD diversifieur corr 0.04, Inflation 2022 RP perd 2× moins). Cause racinaire = **auto-extraction à partir des commentaires de cellule** sans lecture visuelle, corrigée c.454 par audit MiniMax M3 + matching `set_title()`/`suptitle()` contre `research.ipynb`. **Découverte majeure c.454** : Sharpe headline `0.399` propagé du README vers MANIFEST était **FAUX** vs verdict réel cell[10] du notebook (Risk Parity Sharpe **0.544** < SPY **0.655**, RP MaxDD **-20.26 %** vs SPY **-33.72 %**) — RP = compromis risque-rendement délibéré (protection downside -50% MaxDD au prix d'un upside raboté, RP perd 2× moins en Inflation 2022), PAS un « contre-exemple défaillant ».
>
> **Migration c.804 (2026-07-23, doctrine #5780 amendée post-#7771)** : format canonical `## <filename>.png` + champ `**Description visuelle** :` adjacent pour les 6 figures (`detect_manifest_field.py --check` exit 0 obligatoire). Tells visuels c.778-L1/L2/L3 + c.779-L1 vérifiés firsthand vision MiniMax M3 + PIL RGB stats 80×80 redimensionnée : **6/6 matplotlib-blanc** (mean RGB 219-244, std 18-63, bg blanc 48-75% = L778-L2 tell dominant) **+ 1 signature heatmap divergente** sur `rp-exploration.png` (mean RGB (228,234,217), std=58 dominant = signature dense corrélation 5×5 à 25 cellules). Le quad-panel `rp-h3-tlt.png` (4 subplots denses 800×495 = ratio 1.62 atypique) présente la variance PIL la plus basse de la série (std 18-19) — signature de subplots très denses à aires colorées réduites (zones vides majoritaires). Out-of-scope c.805+ : 0 autres MANIFESTs QC project sans `Description visuelle` identifiés au moment du sweep c.754-c.804.

| # | Fichier | Dimensions | Poids | Source (cellule · output) | Sujet *(c.454 reformulé CONTENT-driven)* |
|---|---------|------------|-------|---------------------------|-----------------------------------------|
| 1 | `rp-exploration.png` | 1544×487 | 114 Ko | cellule 4 · output 1 | **Dual-panel** : gauche « Rendements cumulés 2015-2026 » ($1 investi, 6 actifs : SPY/EFA/GLD/DBC/TLT) + droite « Matrice de corrélation » (heatmap divergente 5×5, palette rouge-vert divergente) |
| 2 | `rp-h1-inversevol.png` | 1787×493 | 34 Ko | cellule 6 · output 1 | **Triple-panel bar chart** « Capital vs Contribution au Risque selon la méthode de pondération » : 60/40 / 1/N / Risk Parity. Chaque panel = 5 paires de barres (capital bleu + risk contribution orange) |
| 3 | `rp-h2-backtest.png` | 1586×986 | 166 Ko | cellule 8 · output 1 | **Dual-panel** : haut « Rendements cumulés : Risk Parity vs Benchmarks (2015-2026) » + bas « Allocation Risk Parity au fil du temps » (aires empilées 5 actifs, RP = colors tab:blue/orange/green/red/purple) |
| 4 | `rp-h3-tlt.png` | 800×495 | 187 Ko | cellule 12 · output 0 | **Quad-panel** « Analyse de la période TLT Pain (2020-2023) » : (1) TLT vs SPY vs GLD base 100, (2) Volatilité roulante 60j annualisée, (3) Poids Risk Parity, (4) Performance relative RP vs SPY vs 60/40 |
| 5 | `rp-h4-lookback.png` | 1387×487 | 34 Ko | cellule 14 · output 1 | **Dual-panel** : gauche « Sharpe selon la fenêtre de volatilité » + droite « Max Drawdown selon la fenêtre de volatilité », 5 lookbacks 20/40/60/90/120j |
| 6 | `rp-regime.png` | 1387×587 | 36 Ko | cellule 16 · output 2 | **Bar chart mono-panel** « Rendements par régime : Risk Parity vs SPY », 5 régimes. Bull 2015-19 / COVID 2020 / Recovery 2021 / Inflation 2022 / Recovery 2023-25 |

**Total** : 6 figures, 573 Ko. **Politique** (#5654) : ≤200 Ko/fichier, downscale ≤1200 px max. H3 (297 Ko natif, dense) downscaled à 800×495 ; les autres passent natifs (34–166 Ko). Arc : exploration (GLD diversifieur corr SPY 0.04) → H1 inverse-vol (égalisation des contributions au risque, SPY+EFA 78.9 % → 49.7 %) → H2 backtest risk parity (Sharpe 0.544 < SPY 0.655 mais MaxDD moitié moindre) → H3 impact TLT 2020-2023 (RP ≈ 60/40, loin de SPY 55.8 %) → H4 sensibilité au lookback (range 0.544-0.580 quasi-plat = robuste, winner 40j) → analyse par régime (RP perd 2× moins en inflation 2022, upside raboté en bull).

## Contenu réel vérifié par figure (audit visuel MiniMax M3, c.454)

## rp-exploration.png

- **Source** : notebook `research.ipynb` (cellule 4, output 1)
- **Description visuelle** : Composition matplotlib **dual-panel horizontal 2×1 1544×487** sur fond blanc cassé (RGB 80×80 mean R228/G234/B217 std R56/G36/B58, bg blanc 61% — **variance B=58 dominante signature heatmap divergente**, L779-L1 tell heatmap dense 5×5=25 cellules). **Gauche — « Rendements cumulés 2015-2026 »** (axe Y = 0.5 → 3.5 USD ($1 investi), axe X = 2016-2026) : **5 courbes long-terme** identifiées par légende haut-gauche = DBC bleu (sous-performant, termine ~1.2), EFA orange (~1.85), GLD vert (croissance soutenue, termine ~3.0), SPY rouge (meilleur rendement absolu, termine ~3.4), TLT violet (déclin post-2021, termine ~0.8) ; **Droite — « Matrice de corrélation »** : heatmap 5×5 (axes = SPY/EFA/GLD/DBC/TLT) avec palette divergente rouge (corr +) → blanc (≈0) → vert (corr −), échelle latérale -1.00 → +1.00, **diagonale = 1.00 rouge foncé**, valeurs chiffrées visibles dans chaque cellule (SPY↔EFA=0.39, EFA↔DBC=0.85, GLD↔DBC=0.04, etc.).
- **Alt-text (FR)** *(c.454 reformulé CONTENT-driven)* : **Dual-panel** (1544×487). **Gauche — « Rendements cumulés 2015-2026 »** ($1 investi, 5 actifs) : **DBC bleu** termine ~1.2 (sous-performant), **EFA orange** ~1.85, **GLD vert** ~3.0 (croissance soutenue), **SPY rouge** ~3.4 (meilleur absolu), **TLT violet** ~0.8 (déclin post-2021). **Droite — « Matrice de corrélation »** (heatmap 5×5, palette rouge-blanc-vert divergente, échelle -1.00 → +1.00). **Diagonale = 1.00** (rouge foncé, asset vs lui-même). **Anti-corrélations** : TLT↔SPY = **-0.17**, TLT↔EFA = **-0.16**, DBC↔TLT = **-0.18**. **Corrélations modérées positives** : EFA↔DBC = **+0.85** (commodities-Europe), SPY↔EFA = **+0.39**, SPY↔DBC = **+0.35**, TLT↔GLD = **+0.28**, SPY↔GLD = **+0.04** (quasi-indépendance — **diversifieur clé**), GLD↔DBC = **+0.04** (quasi-indépendance). **Verdict visuel** : GLD = meilleur Sharpe S=0.81 + CAGR 12.02 % + corrélation quasi-nulle avec SPY = **diversifieur clé du portefeuille**. DBC = sous-performant S=0.20 / CAGR 3.45 % malgré corrélation modérée avec SPY 0.35.

**Contenu réel vérifié** (audit visuel MiniMax M3, c.454) : dual-panel matplotlib avec titres explicites sur chaque subplot (« Rendements cumulés 2015-2026 » / « Matrice de corrélation »), labels d'axes et de cellules visibles, palette divergente rouge-vert. **Alt-text précédent** « Analyse exploratoire des actifs (§2) » était **CONTENT-DRIFTED** (omets dual-panel + identité du diversifieur GLD corr SPY 0.04 + chiffres de corrélation + classement Sharpe par actif).

- **Poids** : 114 Ko (PNG lossless natif, source 1544×487)

## rp-h1-inversevol.png

- **Source** : notebook `research.ipynb` (cellule 6, output 1)
- **Description visuelle** : Composition matplotlib **triple-panel horizontal 3×1 1787×493** (format `plt.subplots(1, 3, figsize=(18, 5))`) sur fond blanc cassé signature canonique L778-L2 (RGB 80×80 mean R240/G238/B236 std R37/G31/B41, bg blanc 75%). Suptitle « Capital vs Contribution au Risque selon la méthode de pondération ». **3 subplots alignés**, chacun = bar chart 5 actifs (SPY/EFA/GLD/DBC/TLT sur X) × 2 séries (Poids capital bleu + Contribution risque orange, légende haut-droite identique sur les 3). **Panel 1 « 60/40 Classique »** : SPY capital 0.40 / risk **0.54** (sur-représentation), EFA capital 0.20 / risk 0.25, GLD/DBC ≈ 0, TLT capital 0.40 / risk 0.21. **Panel 2 « 1/N (Egal) »** : 5 actifs à capital ≈ 0.20 chacun, risk contributions SPY 0.27 / EFA 0.27 / GLD 0.17 / DBC 0.23 / TLT 0.06 (sur-représentation actions encore). **Panel 3 « Risk Parity »** : SPY capital 0.184 / risk 0.240, EFA 0.190 / risk 0.255, GLD **0.222** / risk **0.200**, DBC 0.184 / risk 0.215, TLT 0.218 / risk 0.085 (sous-représentation obligataire).
- **Alt-text (FR)** *(c.454 reformulé CONTENT-driven)* : **Triple-panel bar chart** (1787×493) « Capital vs Contribution au Risque selon la méthode de pondération » : **3 méthodes de pondération testées** sur les 5 actifs (SPY/EFA/GLD/DBC/TLT). Chaque panel = 5 paires de barres (capital bleu + risk contribution orange). **Panel 1 « 60/40 Classique »** : SPY capital 40 % / risk **54 %** (sur-représentation risque actions), EFA 20 % / 25 %, GLD/DBC ≈ 0, TLT 40 % / 21 %. **Panel 2 « 1/N Egal »** : 5 actifs à 20 % capital, risk contributions inégales (SPY 27 % / EFA 27 % / GLD 17 % / DBC 23 % / TLT 6 %). **Panel 3 « Risk Parity »** : capital quasi-égal (~18-22 %), **risk contributions quasi-égalisées** (SPY 24 % / EFA 25 % / GLD 20 % / DBC 21 % / TLT 8 %). **Verdict H1** : **l'inverse-vol / Risk Parity égalise** les contributions au risque par rapport à 60/40 — pour le duo SPY+EFA, **60/40 = 78.9 % du risque** vs **RP = 49.7 %**. RP sous-pondère structurellement TLT (8 % du risque) au profit de GLD (20 %), démontrant l'égalisation par construction.

**Contenu réel vérifié** (audit visuel MiniMax M3, c.454) : triple-panel bar charts avec sub-titres « 60/40 Classique », « 1/N (Egal) », « Risk Parity », légendes haut-droite identiques, axes Y = Proportion (0 → 0.9), axe X = 5 actifs. **Alt-text précédent** « Inverse-volatility weighting égalise les contributions (H1) » était **CONTENT-DRIFTED** : verdict juste mais omet la métrique pivot 60/40 SPY+EFA 78.9 % du risque → RP 49.7 % + structure triple-panel + comparaison chiffrée des 3 méthodes.

- **Poids** : 34 Ko (PNG lossless natif, source 1787×493)

## rp-h2-backtest.png

- **Source** : notebook `research.ipynb` (cellule 8, output 1)
- **Description visuelle** : Composition matplotlib **dual-panel vertical 2×1 1586×986** sur fond blanc cassé (RGB 80×80 mean R222/G214/B210 std R51/G50/B61, bg blanc 51% — variance R/G/B élevée par la dominance des aires empilées colorées du panel bas). **Haut « Rendements cumulés: Risk Parity vs Benchmarks (2015-2026) »** (axe Y = 1.0 → 4.0 USD ($1 investi), axe X = 2016-2026) : **4 courbes long-terme** identifiées par légende haut-gauche = **Risk Parity bleu continu** (termine ~2.2, sous-performant), **SPY benchmark rouge pointillé** (termine ~4.0, surperforme), **1/N egal vert pointillé** (~2.1, coincide quasi-exactement avec RP), **60/40 (SPY/TLT) orange tirets** (~2.45). **Bas « Allocation Risk Parity au fil du temps »** (axe Y = 0 → 1.0, axe X = 2016-2026) : **aires empilées colorées** de 5 actifs (DBC bleu bas, EFA orange, GLD vert milieu, SPY rouge, TLT violet haut) = **poids dynamiques** RP sur 11 ans, GLD ≈ 25-35 % dominante, TLT ≈ 15-25 %, ajustements réactifs 2020 (COVID) et 2022 (inflation/bonds crash).
- **Alt-text (FR)** *(c.454 reformulé CONTENT-driven)* : **Dual-panel** (1586×986). **Haut — « Rendements cumulés: Risk Parity vs Benchmarks (2015-2026) »** ($1 investi) : **Risk Parity bleu** termine ~2.2 (Sharpe **0.544**), **SPY benchmark rouge pointillé** ~4.0 (Sharpe **0.655**, surperforme), **1/N egal vert pointillé** ~2.1 (≈ RP), **60/40 (SPY/TLT) orange tirets** ~2.45. **RP perd ~17 % en Sharpe vs SPY** mais **MaxDD moitié moindre** (RP -20.26 % vs SPY -33.72 %, cell[10]). **Bas — « Allocation Risk Parity au fil du temps »** (aires empilées 5 actifs, 2016-2026) : GLD ~25-35 % dominante, TLT ~15-25 %, ajustements réactifs 2020 COVID + 2022 inflation/bonds crash. **Verdict H2** : **RP ne bat pas SPY en absolu** (Sharpe 0.544 vs 0.655), mais **réduit le drawdown d'environ moitié** (MaxDD -20.26 % vs -33.72 %). Compromis risque-rendement délibéré, pas défaillance.

**Contenu réel vérifié** (audit visuel MiniMax M3, c.454) : dual-panel composite avec titres explicites, légende haut-gauche 4 stratégies, axes X temporels 2015-2026 synchronisés. **Alt-text précédent** « Simulation du backtest risk parity (H2) » était **CONTENT-DRIFTED** (omets dual-panel + verdict Sharpe 0.544 < SPY 0.655 + MaxDD moitié moindre + structure des aires empilées RP).

- **Poids** : 166 Ko (PNG lossless natif, source 1586×986)

## rp-h3-tlt.png

- **Source** : notebook `research.ipynb` (cellule 12, output 0)
- **Description visuelle** : Composition matplotlib **quad-panel 2×2 800×495** (le **seul quad-panel** de la série RiskParity, format `plt.subplots(2, 2, figsize=(10, 6))`) downscalée depuis 1587×983 natif pour respecter politique ≤200 Ko / ≤1200 px. PIL mean RGB (243,243,242) std (18,16,19) bg blanc 66% — **variance PIL la plus basse** de la série, signature de **4 subplots denses à zones blanches majoritaires** (axes concentrés, légendes compactes). Suptitle « Analyse de la periode TLT Pain (2020-2023) ». **Panel (1,1) haut-gauche « TLT vs SPY vs GLD (2020-2023, base 100) »** (axe Y = 0.8 → 1.6) : 3 courbes (SPY bleu termine ~1.55, TLT orange termine ~0.75, GLD vert termine ~1.32), ligne horizontale tirets base 1.0. **Panel (1,2) haut-droite « Volatilité roulante 60j annualisée (2020-2023) »** (axe Y = 0 → 60 %) : 4 courbes (SPY bleu, GLD vert, DBC rouge, TLT violet) avec pic commun **2020-04 (COVID) vers 60 %**, puis volatilité ~10-30 % post-2021. **Panel (2,1) bas-gauche « Poids Risk Parity (2020-2023) »** (axe Y = 0.125 → 0.300) : 5 lignes en step function (DBC/EFA/GLD/SPY/TLT, 5 couleurs tab:10), évolution dynamique des poids RP sur la fenêtre, GLD pic ~0.30 mi-2020 puis stabilisation ~0.22, TLT pic ~0.30 mi-2022. **Panel (2,2) bas-droite « Performance relative (2020-2023, base 100) »** (axe Y = 0.7 → 1.6) : 3 courbes (Risk Parity bleu termine ~1.24, SPY orange tirets ~1.55, 60/40 vert tirets ~1.24 ≈ RP).
- **Alt-text (FR)** *(c.454 reformulé CONTENT-driven)* : **Quad-panel 2×2** (800×495, **le seul quad-panel** de la série, downscale depuis 1587×983) « Analyse de la période TLT Pain (2020-2023) ». **(1) TLT vs SPY vs GLD base 100** (axe Y = 0.8 → 1.6) : SPY bleu ~1.55, TLT orange ~0.75 (décline post-2021 hausse taux), GLD vert ~1.32. **(2) Volatilité roulante 60j annualisée** (axe Y = 0 → 60 %) : 4 actifs, **pic commun 2020-04 COVID ~60 %** sur SPY, stabilisation 10-30 % post-2021. **(3) Poids Risk Parity** (axe Y = 0.125 → 0.300) : 5 lignes en step function, GLD pic 0.30 mi-2020, TLT pic 0.30 mi-2022. **(4) Performance relative base 100** (axe Y = 0.7 → 1.6) : RP bleu ~1.24, SPY orange ~1.55, 60/40 vert ~1.24 (≈ RP). **Verdict H3** : **sur la fenêtre 2020-2023 (TLT Pain), RP 24.1 % ≈ 60/40 24.5 %**, **SPY 55.8 %** (outlier bull). RP **n'a pas surperformé** sur cette fenêtre de hausse d'actions + krach obligataire — sa protection a coûté l'upside.

**Contenu réel vérifié** (audit visuel MiniMax M3, c.454) : quad-panel composite avec 4 sub-titres (« TLT vs SPY vs GLD (2020-2023, base 100) », « Volatilité roulante 60j annualisée (2020-2023) », « Poids Risk Parity (2020-2023) », « Performance relative (2020-2023, base 100) »), légendes visibles. **Alt-text précédent** « Impact de TLT en 2020-2023 (hausse des taux, H3) » était **CONTENT-DRIFTED** (omets quad-panel complet + métriques 24.1 % vs 55.8 % vs 24.5 % + structure step function des poids RP).

- **Poids** : 187 Ko (PNG lossless natif downscale, source 800×495, **downscale depuis 1587×983** pour respecter seuil 200 Ko — confirmé MANIFEST)

## rp-h4-lookback.png

- **Source** : notebook `research.ipynb` (cellule 14, output 1)
- **Description visuelle** : Composition matplotlib **dual-panel horizontal 2×1 1387×487** sur fond blanc cassé signature canonique (RGB 80×80 mean R219/G208/B214 std R63/G53/B49, bg blanc 48% — variance R=63 la plus haute des bar charts simples, signature de 5 barres bleues saturées). **Gauche « Sharpe selon la fenêtre de volatilité »** (axe Y = 0 → 0.6, axe X = 5 lookbacks 20/40/60/90/120j) : **5 barres bleues** Sharpe Ratio quasi-plates autour 0.545-0.580, **ligne horizontale rouge pointillée Moyenne** à ~0.565, **winner 40j** S=**0.580**. **Droite « Max Drawdown selon la fenêtre de volatilité »** (axe Y = -22.5 → 0, axe Y inversé « better up », axe X = 5 lookbacks) : **5 barres saumon** (rose pâle) MaxDD quasi-plates autour -19.3 à -20.3 %, **winner 40j** MaxDD=-19.29 %.
- **Alt-text (FR)** *(c.454 reformulé CONTENT-driven)* : **Dual-panel** (1387×487) sur 5 lookbacks de volatilité (20/40/60/90/120j). **Gauche « Sharpe selon la fenêtre de volatilité »** (axe Y = 0 → 0.6) : **5 barres bleues quasi-plates**, range **0.544-0.580**, ligne rouge pointillée Moyenne ~0.565, **winner 40j S=0.580**. **Droite « Max Drawdown selon la fenêtre de volatilité »** (axe Y = -22.5 → 0, inversé) : **5 barres saumon quasi-plates**, range **-19.29 à -20.3 %**, **winner 40j MaxDD=-19.29 %**. **Verdict H4** : **range Sharpe 0.544-0.580 quasi-plat = robustesse** (la stratégie n'est **pas overfittée** sur une fenêtre spécifique), le choix du lookback n'a **pas d'impact significatif**. Le winner marginal 40j (+0.036 Sharpe vs 60j) ne justifie pas un tuning fin : la stratégie est **stable par construction**.

**Contenu réel vérifié** (audit visuel MiniMax M3, c.454) : dual-panel bar charts symétriques (1 Sharpe + 1 MaxDD), axes X = 5 lookbacks 20/40/60/90/120j, légende « Moyenne » (rouge pointillée) sur panel gauche uniquement. **Alt-text précédent** « Sensibilité au lookback de volatilité (H4) » était **CONTENT-DRIFTED** (omets dual-panel + verdict range 0.544-0.580 quasi-plat = robustesse + winner 40j S=0.580).

- **Poids** : 34 Ko (PNG lossless natif, source 1387×487)

## rp-regime.png

- **Source** : notebook `research.ipynb` (cellule 16, output 2)
- **Description visuelle** : Composition matplotlib **bar chart mono-panel 1387×587** (le **seul mono-panel** de la série RiskParity, format `plt.subplots(figsize=(14, 6))`) sur fond blanc cassé signature canonique (RGB 80×80 mean R244/G236/B237 std R32/G35/B35, bg blanc 74% — variance R/G/B modeste, signature de 5 paires de barres bien séparées sur blanc dominant). Titre « Rendements par regime: Risk Parity vs SPY ». Axe Y = Rendement total % (-20 → +90), axe X = 5 régimes (Bull 2015-2019 / COVID 2020 / Recovery 2021 / Inflation 2022 / Recovery 2023-2025), ligne horizontale noire zéro. **5 paires de barres verticales** : Risk Parity bleu (gauche de chaque paire) + SPY saumon (droite). **Bull 2015-19** : RP ~30 vs SPY ~76 (SPY surperforme ~46 pp). **COVID 2020** : RP ~10 vs SPY ~17 (SPY surperforme ~7 pp, RP MaxDD -20.3 %). **Recovery 2021** : RP ~13 vs SPY ~31 (SPY surperforme ~18 pp). **Inflation 2022** : RP ~-12 vs SPY ~-19 (RP perd ~7 pp de moins = **perd 2× moins**). **Recovery 2023-25** : RP ~48 vs SPY ~86 (SPY surperforme ~38 pp).
- **Alt-text (FR)** *(c.454 reformulé CONTENT-driven)* : **Bar chart mono-panel** (1387×587, **le seul mono-panel** de la série) « Rendements par regime: Risk Parity vs SPY » sur 5 régimes. **Bull 2015-19** : RP **~30 %** vs SPY **~76 %** (SPY surperforme ~46 pp). **COVID 2020** : RP ~10 % vs SPY ~17 % (SPY +7 pp, RP MaxDD -20.3 %). **Recovery 2021** : RP ~13 % vs SPY ~31 % (SPY +18 pp). **Inflation 2022** : RP **~-12 %** vs SPY **~-19 %** (**RP perd ~7 pp de moins = perd 2× moins** — protection downside validée). **Recovery 2023-25** : RP ~48 % vs SPY ~86 % (SPY surperforme ~38 pp). **Verdict §7** : **RP échange upside contre protection** : sous-performant en bull (rendement absolu moindre), perdant **2× moins en inflation 2022** (krach obligataire + actions). Trade-off risque/rendement validé empiriquement sur 5 régimes distincts.

**Contenu réel vérifié** (audit visuel MiniMax M3, c.454) : bar chart simple, axe X = 5 régimes étiquetés explicitement, axe Y = Rendement total %, légende haut-gauche « Risk Parity » (bleu) + « SPY » (saumon), ligne horizontale noire à zéro. **Alt-text précédent** « Analyse par régime de marché (§7) » était **CONTENT-DRIFTED** (omets le verdict pivot Inflation 2022 RP perd 2× moins + comparaison chiffrée des 5 régimes).

- **Poids** : 36 Ko (PNG lossless natif, source 1387×587)

## Verdict synthétique c.454

| # | Fichier | Alt-text précédent | Verdict | Action |
|---|---------|---------------------|---------|--------|
| 1 | `rp-exploration.png` | « Analyse exploratoire des actifs (§2) » | **CONTENT-DRIFTED** (omet dual-panel + identité du diversifieur GLD) | Reformulé dual-panel + heatmap 5×5 + GLD corr SPY 0.04 |
| 2 | `rp-h1-inversevol.png` | « Inverse-volatility weighting égalise les contributions (H1) » | **CONTENT-DRIFTED** (verdict juste mais omet la métrique pivot 78.9 % → 49.7 %) | Reformulé triple-panel + comparaison chiffrée 3 méthodes |
| 3 | `rp-h2-backtest.png` | « Simulation du backtest risk parity (H2) » | **CONTENT-DRIFTED** (omet dual-panel + le verdict Sharpe 0.544 < SPY 0.655 + MaxDD moitié moindre) | Reformulé dual-panel + Sharpe 0.544 + MaxDD moitié + RP perd ~17 % Sharpe |
| 4 | `rp-h3-tlt.png` | « Impact de TLT en 2020-2023 (hausse des taux, H3) » | **CONTENT-DRIFTED** (omet quad-panel complet + métriques 24.1 % vs 55.8 %) | Reformulé quad-panel + RP 24.1 % ≈ 60/40 24.5 % << SPY 55.8 % |
| 5 | `rp-h4-lookback.png` | « Sensibilité au lookback de volatilité (H4) » | **CONTENT-DRIFTED** (omet dual-panel + verdict range 0.544-0.580 quasi-plat + winner 40j) | Reformulé dual-panel + range 0.544-0.580 quasi-plat = robustesse |
| 6 | `rp-regime.png` | « Analyse par régime de marché (§7) » | **CONTENT-DRIFTED** (omet le verdict pivot Inflation 2022 RP perd 2× moins) | Reformulé mono-panel + 5 régimes chiffrés + verdict 2× moins en inflation |

**Score** : **0/6 ACCURATE** — **6 corrections content-driven** (défaut fondateur type (g) CONTENT-DRIFTED uniforme). **Cause racinaire confirmée** : alt-texts d'origine générés par **auto-extraction à partir des commentaires de cellule** (e.g. `# H1: Inverse-vol` → alt-text « Inverse-volatility weighting ») sans lecture visuelle ni capture des `set_title()`/`suptitle()` des subplots ni des valeurs chiffrées dans les outputs texte. Corrigé c.454 par audit visuel MiniMax M3 + matching `set_title()`/`suptitle()` contre `research.ipynb`.

## Découverte majeure c.454 — Risk Parity = protection downside au prix de l'upside (Sharpe 0.544 < SPY 0.655 mais MaxDD moitié moindre)

Contrairement à l'alt-text « contre-exemple pédagogique » (Sharpe 0.399) qui suggérait une stratégie défaillante, le notebook documente un **compromis risque-rendement délibéré et partiellement validé** :

| Métrique | Risk Parity | SPY | Verdict |
|---|---|---|---|
| Sharpe (2015-2026) | 0.544 | 0.655 | RP perd ~17 % en Sharpe |
| CAGR | 7.28 % | 13.46 % | RP rend ~ moitié |
| MaxDD | -20.26 % | -33.72 % | **RP MaxDD ~ moitié moindre** |
| Inflation 2022 | -9.8 % | -18.6 % | **RP perd 2× moins** |
| Recovery 2023-25 | 47.9 % | 86.3 % | RP upside raboté |

**Conclusion** : la stratégie Risk Parity **ne bat pas SPY** en rendement absolu, mais **réduit le drawdown d'environ moitié** (MaxDD -20 % vs -34 %) et **perd 2× moins en régime d'inflation** (2022 : -9.8 % vs -18.6 %). C'est un **compromis défensif** (protection downside vs upside), pas un « contre-exemple défaillant ». Le verdict « plafond structurel » reste valable (RP ne surperforme pas SPY en Sharpe), mais le Sharpe réel est **0.544** (pas 0.399 propagé depuis README).

## Préuves vérifiables c.454

- 6/6 PNG ouverts via `Read` (vision MiniMax M3), analysés et décrits dans le MANIFEST enrichi
- 6/6 attributions cell×output confirmées via matching `set_title()`/`suptitle()` du code source `research.ipynb` :
  - `rp-exploration.png` → cell[4] out[1] ✓ (`set_title('Rendements cumules 2015-2026')` + `set_title('Matrice de correlation')`)
  - `rp-h1-inversevol.png` → cell[6] out[1] ✓ (`suptitle('Capital vs Contribution au Risque selon la methode de ponderation')`)
  - `rp-h2-backtest.png` → cell[8] out[1] ✓ (`set_title('Rendements cumules: Risk Parity vs Benchmarks (2015-2026)')` + `set_title('Allocation Risk Parity au fil du temps')`)
  - `rp-h3-tlt.png` → cell[12] out[0] ✓ (`suptitle('Analyse de la periode TLT Pain (2020-2023)')` + 4 `set_title`)
  - `rp-h4-lookback.png` → cell[14] out[1] ✓ (`set_title('Sharpe selon la fenetre de volatilite')` + `set_title('Max Drawdown selon la fenetre de volatilite')`)
  - `rp-regime.png` → cell[16] out[2] ✓ (`set_title('Rendements par regime: Risk Parity vs SPY')`)
- Sharpe headline corrigé : `0.399` absent de toute sortie notebook ; verdict réel cell[10]·out[0] = Risk Parity Sharpe 0.544, SPY 0.655, RP MaxDD -20.26 % vs SPY -33.72 %

## Cumul EPIC #5780 vague QC projets

| Cycle | PR | Projet | Figures | Ratio |
|-------|----|--------|---------|-------|
| c.438 | #6541 | DualMomentum | 4 | 4:4 systemic |
| c.447 | #6655 | AllWeather | 6 | 5:1 systemic |
| c.448 | #6656 | EMA-Cross-Crypto | 5 | 5:5 doctrinal |
| c.449 | #6661 | EMA-Cross-Index | 6 | 6:6 doctrinal |
| c.450 | #6668 | ForexCarry | 6 | 6:6 doctrinal + 2 ATTRIB inversées |
| c.451 | #6671 | LongShortHarvest-QC | 6 | 6:6 doctrinal + 1 FAUX alt-text + 3 sweeps NULS |
| c.452 | #6674 | ML-RandomForest | 6 | 6:6 doctrinal + 5 sweeps DISCRIMINANTS |
| c.453 | #6676 | ML-XGBoost | 6 | 6:6 doctrinal + DOUBLE-NATURE + inversion feature importance + sous-perf SPY |
| **c.454** | **#6680** | **RiskParity** | **6** | **6:6 content-driven drifted + Sharpe headline 0.399→0.544 corrigé** |
| c.778 | #7954 | IIT/ICT-Series | 9 | 9:9 |
| c.755 | #7956 | Planners | 5 | 5:5 |
| c.779 | #7961 | PyMC DecisionTheory | 6 | 6:6 |
| c.770 | #7968 | Search/Applications | 6 | 6:6 |
| c.781 | #7981 | GenAI/Image/examples | 6 | 6:6 |
| c.766 | #7988 | GenAI/Image/03-Orchestration | 5 | 5:5 |
| c.787 | #7992 | GenAI/Image/01-Foundation | 6 | 6:6 |
| c.785 | #8020 | ML-Training-Pipeline | 6 | 6:6 |
| c.787 | #8034 | ML-XGBoost | 6 | 6:6 |
| c.788 | #8038 | ML-RandomForest | 6 | 6:6 |
| c.788 | #8039 | AllWeather | 6 | 6:6 canonical migration |
| c.786 | #8043 | EMA-Cross-Crypto | 5 | 5:5 canonical migration |
| c.791 | #8048 | ForexCarry | 7 | 7:7 canonical migration |
| **c.804** | **(cette PR)** | **RiskParity** | **6** | **6:6 canonical migration (doctrine #5780)** |

**Vague QC projets = COMPLETE** (cf `QuantConnect/projects/`) après c.804.
