# Manifeste des figures — AllWeather

Provenance de chaque figure (convention d'indexation **all-cells** du module `extract_readme_figures.py` : `cellule` = indice de cellule dans le notebook, `output` = indice de sortie de cette cellule). Sources vérifiées sur `origin/main`, extraites de [`research.ipynb`](../../research.ipynb) (notebook de recherche local).

> **Audit vision po-2026 c.447 (2026-07-15, doctrine #5780)** : les 6 PNG ci-dessous ont été ouverts un par un via l'outil `Read` (vision MiniMax M3) et comparés à leur alt-text d'origine (champ `Sujet`). Verdict par figure dans la section *Contenu réel vérifié*. Cohérence caption ↔ image = **1/6 exacte, 5 corrections d'alt-text appliquées** — la quasi-totalité des alt-texts d'origine étaient **TITLES-driven** (un seul mot ou expression générique méthode/conclusion : « Exploration », « Fréquence de rebalancing », « Overlay tactique SMA200 », « Exploration de la grille de paramètres ») ometant la structure réelle (heatmap, dual-panel equity/drawdown, scatter Pareto, rolling multi-strategy), les valeurs concrètes (Sharpe 0.691/0.718/0.744 pour H1, S=0.858 à 50% SMA200 pour H4, période 2016-2026, range Sharpe -2 à +3.5 pour rolling), et l'**inversion factuelle** (aw-exploration.png est une **matrice de corrélation**, pas un graphique rendements/vol). Défaut fondateur type systemic 5:1 documenté par L490 (c.433 → c.438) et confirmé pour les projets QC.
>
> **Migration c.788 (2026-07-22, doctrine #5780 amendée post-#7771)** : format canonical `## <filename>.png` + champ `**Description visuelle** :` adjacent pour les 6 figures (`detect_manifest_field.py --check` exit 0 obligatoire). Tells visuels c.778-L1/L2/L3 + c.779-L1/L2 vérifiés firsthand vision MiniMax M3 + PIL RGB stats 100×50 redimensionnée : **5/6 matplotlib-blanc** (mean RGB 245-252, std 10-26, bg blanc 79-96% = L778-L2 tell dominant) **+ 1 heatmap divergente** sur `aw-exploration.png` (mean RGB (211,180,182), std B=87 dominant = L779-L1 tell heatmap dense divergente bleu-rouge). Out-of-scope c.789+ : 3 autres MANIFESTs QC project non-ML (EMA-Cross-Crypto 5f, EMA-Cross-Index 6f, ForexCarry 7f) — distincts en genre ET substance vs ML-trilogie close (c.785/c.786/c.787), G-VAR-3 ✓ cross-famille pivot.
>
> **Régénération #24513 (2026-11-04)** : le moteur `backtest_portfolio` du notebook laisse désormais dériver les poids entre deux rééquilibrages (`w_i <- w_i (1 + r_i) / (1 + r_p)`). L'ancien moteur réappliquait chaque jour les poids cibles, ce qui revenait à rééquilibrer quotidiennement quelle que soit la fréquence demandée. Le notebook a été ré-exécuté de bout en bout et les six figures ont été régénérées depuis ses sorties (données 2015-2026). Les valeurs citées par l'audit c.447 (Sharpe 0.691 / 0.718 / 0.744 en H1, 0.817 identique pour les trois fréquences en H3, optimum 0.858 à 50 % en H4) venaient de l'ancien moteur : le verdict « la fréquence n'a aucun impact » de H3 était un artefact du moteur, et l'optimum à 50 % de H4 ne tient plus — chaque palier de réduction baisse à la fois le drawdown et le Sharpe. La cellule 6 du notebook contrôle le moteur : « jamais rééquilibré » coïncide avec un achat-conservation calculé directement depuis les prix, le rééquilibrage trimestriel coïncide avec un achat-conservation repris aux poids cibles à chaque date de rééquilibrage, lui aussi calculé depuis les prix, et l'ancien moteur rend toujours le Sharpe publié de 0.691. Le 2026-11-05, ce deuxième contrôle a remplacé la comparaison au rééquilibrage quotidien, vraie par construction ; le carnet a été ré-exécuté et les quatre figures réduites régénérées par la même recette (Lanczos, PNG optimisé). Elles diffèrent des précédentes de quelques pixels, effet des prix ajustés téléchargés, et leurs poids sont inchangés au Ko près. Les sections par figure ci-dessous décrivent les nouvelles images, relues une à une le 2026-11-04 ; le tableau *Verdict synthétique c.447* en fin de fichier reste l'historique de l'audit des alt-texts. Le 2026-11-06, les alt-texts et les paragraphes du README de la stratégie ont été alignés sur ces valeurs.

| Figure | Fichier | Dimensions | Poids | Source (cellule · output) | Sujet |
|--------|---------|------------|-------|---------------------------|-------|
| Exploration | `aw-exploration.png` | 691×589 | 40 Ko | cellule 8 · output 1 | **Matrice de corrélation** 5×5 des sous-jacents (SPY/TLT/IEF/GLD/DBC), heatmap divergente bleu-rouge (-1 → +1) |
| H1 — Parity | `aw-h1-parity.png` | 1000×712 | 195 Ko | cellule 10 · output 1 | Dual-panel : equity de 3 stratégies (Static Dalio S=0.682 DD=-23.59 %, Risk Parity S=0.702 DD=-18.81 %, Tactical SMA200 S=0.719 DD=-15.84 %) + drawdowns 2015-2026 |
| H3 — Rebalancing | `aw-h3-rebalance.png` | 1100×783 | 199 Ko | cellule 16 · output 3 | Dual-panel : equity de 3 fréquences (Monthly S=0.792, Quarterly S=0.798, Semi-Annual S=0.788) + 2 références (Daily S=0.817, Never S=0.919) ; « Never » se détache après 2023 |
| H4 — SMA200 | `aw-h4-sma200.png` | 800×569 | 192 Ko | cellule 19 · output 2 | Dual-panel : equity de 5 niveaux de réduction tactique (0 % à 100 %) + drawdowns ; **0 % garde le meilleur Sharpe** (0.798), le drawdown passe de -24.24 % à -16.21 % |
| Comparaison | `aw-comparison.png` | 989×590 | 33 Ko | cellule 21 · output 0 | **Nuage de points** Sharpe vs MaxDD : 5 points alignés de 100 % (16.21 %, 0.597) à 0 % (24.24 %, 0.798), sans optimum intérieur |
| Grille optimale | `aw-grid-optimal.png` | 1200×422 | 169 Ko | cellule 26 · output 0 | **Rolling 1-Year Sharpe** 2016-2026 : 3 stratégies (Original Static Dalio Q, Optimized Static+Tactical, RP+Tactical Combo), pic vers +3 début 2020, creux vers -2 fin 2022 |

**Total** : 6 figures, 827 Ko. **Politique** (#5654) : ≤200 Ko/fichier, downscale ≤1200 px max. Courbes matplotlib → **PNG lossless**. Sorties natives du notebook : H1, H3 et H4 en 1389×989, grille en 1389×489 ; downscale à 1000×712 (H1), 1100×783 (H3), 800×569 (H4, 275 Ko natif) et 1200×422 (grille) pour tenir les deux seuils. Arc : exploration des données → hypothèses H1 (parity) / H3 (rebalancing) / H4 (overlay SMA200) → comparaison des configurations → Sharpe glissant des configurations finales.

## Contenu vérifié par figure (relecture visuelle du 2026-11-04, #24513)

## aw-exploration.png

- **Source** : notebook `research.ipynb` (cellule 8, output 1)
- **Description visuelle** : Heatmap de corrélation 5×5 intitulée « Correlation Matrix - AllWeather Assets », palette divergente rouge (corrélation positive) / blanc (≈ 0) / bleu (négative), échelle latérale -1.00 → +1.00. Axes X et Y labellés SPY, TLT, IEF, GLD, DBC, valeur inscrite dans chaque case, diagonale rouge foncé (1.00). Valeurs inchangées par la régénération : TLT↔IEF = +0.92, SPY↔DBC = +0.35, IEF↔GLD = +0.35, TLT↔SPY = -0.18.
- **Alt-text (FR)** : Heatmap de corrélation des 5 sous-jacents AllWeather (SPY, TLT, IEF, GLD, DBC), échelle bleu (négatif) → blanc (≈ 0) → rouge (positif). Diagonale à 1.00. Les deux obligations sont très corrélées entre elles (TLT↔IEF = **+0.92**) et légèrement anti-corrélées aux actions (TLT↔SPY = **-0.18**, IEF↔SPY = **-0.16**). L'or est quasi indépendant des actions (SPY↔GLD = **+0.04**), les matières premières modérément liées aux actions (SPY↔DBC = **+0.35**).

**Contenu vérifié** : matrice de corrélation identique à celle de l'audit c.447 — la régénération ne change que l'indice de cellule (6 → 8, deux cellules insérées avant : présentation et contrôle du moteur) et l'encodage du PNG. Historique c.447 : l'alt-text d'origine annonçait des « rendements et volatilités », la figure est une matrice de corrélation.

- **Poids** : 40 Ko (PNG lossless, 691×589 natif, pas de downscale)

## aw-h1-parity.png

- **Source** : notebook `research.ipynb` (cellule 10, output 1)
- **Description visuelle** : Dual-panel intitulé « H1: Static vs Risk Parity vs Tactical », 2015-2026. Panneau haut = Portfolio Value (normalisé) avec 3 courbes : Static Dalio bleu (S=0.682, DD=-23.59 %) qui finit le plus haut vers 1.83, Risk Parity (60d) orange (S=0.702, DD=-18.81 %) vers 1.68, Tactical SMA200 vert (S=0.719, DD=-15.84 %) vers 1.67. Panneau bas = Drawdowns en aires superposées, le plus profond pour Static Dalio, vers -0.23 en 2022. Légende avec Sharpe et drawdown par stratégie.
- **Alt-text (FR)** : Hypothèse H1 sur **2015-2026**, deux graphiques empilés. En haut, la valeur du portefeuille pour 3 pondérations : **Static Dalio** (bleu, Sharpe **0.682**, drawdown **-23.59 %**) finit le plus haut, vers **1.83** ; **Risk Parity 60 j** (orange, **0.702**, **-18.81 %**) et **Tactical SMA200** (vert, **0.719**, **-15.84 %**) finissent vers **1.67-1.68**. En bas, les drawdowns : celui de Static Dalio est le plus profond, vers **-23 %** en 2022. Le tactique a le meilleur Sharpe et le drawdown le plus contenu, au prix d'un rendement final plus bas.

**Contenu vérifié** : 3 courbes distinctes, légende conforme au tableau imprimé par la cellule (0.682 / 0.702 / 0.719). Les valeurs c.447 (0.691 / 0.718 / 0.744) venaient de l'ancien moteur, qui rééquilibrait chaque jour.

- **Poids** : 195 Ko (PNG lossless, downscale 1389×989 → 1000×712)

## aw-h3-rebalance.png

- **Source** : notebook `research.ipynb` (cellule 16, output 3)
- **Description visuelle** : Dual-panel intitulé « H3: Rebalancing Frequency Comparison », 2015-2026, sur l'allocation Gold Heavy. Panneau haut = Portfolio Value (normalisé, axe 1.0 → 2.4) avec 5 courbes : Monthly bleu (S=0.792, DD=-24.2 %), Quarterly orange (S=0.798, DD=-24.24 %), Semi-Annual vert (S=0.788, DD=-24.34 %), Daily (reference) rouge (S=0.817, DD=-23.9 %), Never (reference) violet (S=0.919, DD=-23.55 %). Les courbes restent serrées jusqu'en 2020, s'écartent ensuite ; après 2023 la courbe violette se détache nettement et finit vers 2.4, les quatre autres vers 2.05-2.1. Panneau bas = Drawdowns quasi superposés, creux commun vers -0.24 fin 2022. Légende en haut à gauche.
- **Alt-text (FR)** : Hypothèse H3 (fréquence de rééquilibrage) sur **2015-2026**, deux graphiques empilés. En haut, 5 courbes de valeur : mensuel (bleu, Sharpe **0.792**), trimestriel (orange, **0.798**), semestriel (vert, **0.788**), et deux références, quotidien (rouge, **0.817**) et jamais rééquilibré (violet, **0.919**). Les courbes s'écartent après 2020 ; la référence « jamais rééquilibré » se détache après 2023 et finit vers **2.4**, les autres vers **2.05-2.1**. En bas, des drawdowns quasi superposés, vers **-24 %** fin 2022. La fréquence change le résultat de quelques centièmes de Sharpe ; ne jamais rééquilibrer laisse courir la poche action sur la période.

**Contenu vérifié** : les 5 courbes sont distinctes et la légende reprend le tableau de la cellule. La figure c.447 montrait 3 courbes confondues à S=0.817 : c'était l'artefact de l'ancien moteur, qui rééquilibrait chaque jour quelle que soit la fréquence demandée (cf. bloc de régénération en tête).

- **Poids** : 199 Ko (PNG lossless, downscale 1389×989 → 1100×783)

## aw-h4-sma200.png

- **Source** : notebook `research.ipynb` (cellule 19, output 2)
- **Description visuelle** : Dual-panel intitulé « H4: SMA200 Tactical Overlay - Reduction Factors », 2015-2026. Panneau haut = Portfolio Value (normalisé, axe 1.0 → 2.0+) avec 5 courbes étagées : No overlay (0%) bleu (S=0.798, DD=-24.24 %) qui finit vers 2.07, red=25% orange (S=0.785, DD=-21.07 %) vers 1.93, red=50% vert (S=0.751, DD=-18.08 %) vers 1.79, red=75% rouge (S=0.689, DD=-17.07 %) vers 1.66, red=100% violet (S=0.597, DD=-16.21 %) vers 1.53. Panneau bas = Drawdowns en aires superposées, plus profondes pour 0 % (vers -0.24 fin 2022) et plus contenues quand la réduction augmente. Légende en haut à gauche.
- **Alt-text (FR)** : Hypothèse H4 (overlay tactique SMA200) sur **2015-2026**, deux graphiques empilés. En haut, 5 courbes de valeur étagées selon la part réduite quand un actif passe sous sa moyenne 200 jours : **0 %** (bleu, Sharpe **0.798**, drawdown **-24.24 %**) finit le plus haut, vers **2.07** ; **25 %** (orange, **0.785**, **-21.07 %**) ; **50 %** (vert, **0.751**, **-18.08 %**) ; **75 %** (rouge, **0.689**, **-17.07 %**) ; **100 %** (violet, **0.597**, **-16.21 %**) finit le plus bas, vers **1.53**. En bas, des drawdowns d'autant moins profonds que la réduction est forte. Chaque palier de réduction achète du drawdown en cédant du Sharpe : aucun niveau ne bat le portefeuille sans overlay en Sharpe.

**Contenu vérifié** : 5 courbes distinctes, légende conforme au tableau de la cellule. L'optimum c.447 à 50 % (S=0.858) venait de l'ancien moteur.

- **Poids** : 192 Ko (PNG lossless, downscale 1389×989 → 800×569, 275 Ko natif)

## aw-comparison.png

- **Source** : notebook `research.ipynb` (cellule 21, output 0)
- **Description visuelle** : Nuage de points intitulé « H4: Risk-Return Tradeoff by SMA200 Reduction Factor ». Axe X = Max Drawdown % (16 → 24, étiqueté « inverted = better right »), axe Y = Sharpe Ratio (0.60 → 0.80). 5 points colorés étiquetés 0 %, 25 %, 50 %, 75 %, 100 %, alignés sur une diagonale montante : 100 % en bas à gauche (16.21 %, 0.597), puis 75 %, 50 %, 25 %, jusqu'à 0 % en haut à droite (24.24 %, 0.798). Grille de fond.
- **Alt-text (FR)** : Synthèse H4 en **nuage de points** : drawdown maximal en abscisse (**16 % → 24 %**), Sharpe en ordonnée (**0.60 → 0.80**). Les 5 niveaux de réduction s'alignent sur une diagonale : **100 %** (drawdown **16.21 %**, Sharpe **0.597**) en bas à gauche, **0 %** (**24.24 %**, **0.798**) en haut à droite, les paliers intermédiaires entre les deux. Il n'y a pas d'optimum intérieur : chaque palier de réduction baisse à la fois le drawdown et le Sharpe, le choix dépend du drawdown qu'on accepte.

**Contenu vérifié** : 5 points sur une relation monotone. La lecture c.447 (point à 50 % en coin supérieur gauche, Pareto-optimal) ne tient plus avec le moteur à dérive.

- **Poids** : 33 Ko (PNG lossless, 989×590 natif, pas de downscale)

## aw-grid-optimal.png

- **Source** : notebook `research.ipynb` (cellule 26, output 0)
- **Description visuelle** : Courbes temporelles intitulées « Rolling 1-Year Sharpe Ratio », 2016-2026, axe Y Sharpe Ratio (-2 → +3.5), ligne horizontale pointillée à 0, légende en haut à gauche. 3 courbes : Original (Static Dalio, Q) bleu, Optimized (Static + Tactical) orange, RP + Tactical Combo vert. Pic commun vers +3 début 2020, creux commun vers -2 fin 2022. En 2021-2022 la courbe bleue passe au-dessus des deux autres ; en 2024-2025 l'orange et la verte repassent au-dessus de la bleue.
- **Alt-text (FR)** : **Sharpe glissant sur un an**, **2016-2026** (axe Y de **-2** à **+3.5**, ligne pointillée à 0), pour 3 configurations : **Original** (Static Dalio trimestriel, bleu), **Optimized** (allocation Gold Heavy trimestrielle, orange) et **RP + Tactical Combo** (vert). Les trois courbes oscillent ensemble : pic vers **+3** début 2020, creux vers **-2** fin 2022. L'Original fait mieux en 2021-2022, les deux autres en 2024-2025 : aucune configuration ne domine sur toute la période, et aucune n'évite le creux de 2022.

**Contenu vérifié** : 3 séries temporelles fortement corrélées, légende conforme aux noms imprimés par la cellule 24. Historique c.447 : l'alt-text d'origine annonçait une « grille de paramètres », la figure est un Sharpe glissant.

- **Poids** : 169 Ko (PNG lossless, downscale 1389×489 → 1200×422)

## Verdict synthétique c.447

| # | Fichier | Alt-text précédent | Verdict | Action |
|---|---------|---------------------|---------|--------|
| 1 | `aw-exploration.png` | « Rendements et volatilité annualisés » | **FAUX** (heatmap corrélation) | Reformulé CONTENT-driven |
| 2 | `aw-h1-parity.png` | « Static vs Risk Parity vs Tactical (equity curves) » | **TITLES-driven** (3 noms sans structure/values) | Enrichi avec dual-panel + Sharpe/DD concrets + sweet spot |
| 3 | `aw-h3-rebalance.png` | « Fréquence de rebalancing » | **TITLES-driven** (concept, pas résultat) | Enrichi avec 3 lignes confondues + métriques identiques + conclusion aucun impact |
| 4 | `aw-h4-sma200.png` | « Overlay tactique SMA200 (downscale) » | **TITLES-driven + MÉTA** | Enrichi avec 5 niveaux + Sharpe/DD + sweet spot 50% |
| 5 | `aw-comparison.png` | « Comparaison Sharpe et drawdown entre configurations » | **TITLES-driven** (scatter Pareto non explicité) | Enrichi avec scatter Pareto + frontière + seuil 50% |
| 6 | `aw-grid-optimal.png` | « Exploration de la grille de paramètres » | **FAUX** (rolling Sharpe, pas grille) | Reformulé CONTENT-driven |

**Score** : **1/6 ACCURATE** (aucun, en fait) — **5 corrections réelles + 1 ré-écriture complète** (aw-grid-optimal.png et aw-exploration.png). **Ratio systemic 5:1** typique L490 (c.433 → c.438). **Cause racinaire** : les alt-texts d'origine étaient générés par auto-extraction à partir des **commentaires de cellule** (« # H1: Static vs Risk Parity vs Tactical », « # H3: Rebalancing Frequency Comparison », etc.), pas à partir du **contenu visuel réel**. Le rédacteur original ne pouvait pas voir les PNG (LLM sans vision au moment de la génération initiale) — corrigé c.447 par audit visuel MiniMax M3.
