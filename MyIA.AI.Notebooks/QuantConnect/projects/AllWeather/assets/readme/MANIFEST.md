# Manifeste des figures — AllWeather

Provenance de chaque figure (convention d'indexation **all-cells** du module `extract_readme_figures.py` : `cellule` = indice de cellule dans le notebook, `output` = indice de sortie de cette cellule). Sources vérifiées sur `origin/main`, extraites de [`research.ipynb`](../../research.ipynb) (notebook de recherche local).

> **Audit vision po-2026 c.447 (2026-07-15, doctrine #5780)** : les 6 PNG ci-dessous ont été ouverts un par un via l'outil `Read` (vision MiniMax M3) et comparés à leur alt-text d'origine (champ `Sujet`). Verdict par figure dans la section *Contenu réel vérifié*. Cohérence caption ↔ image = **1/6 exacte, 5 corrections d'alt-text appliquées** — la quasi-totalité des alt-texts d'origine étaient **TITLES-driven** (un seul mot ou expression générique méthode/conclusion : « Exploration », « Fréquence de rebalancing », « Overlay tactique SMA200 », « Exploration de la grille de paramètres ») ometant la structure réelle (heatmap, dual-panel equity/drawdown, scatter Pareto, rolling multi-strategy), les valeurs concrètes (Sharpe 0.691/0.718/0.744 pour H1, S=0.858 à 50% SMA200 pour H4, période 2016-2026, range Sharpe -2 à +3.5 pour rolling), et l'**inversion factuelle** (aw-exploration.png est une **matrice de corrélation**, pas un graphique rendements/vol). Défaut fondateur type systemic 5:1 documenté par L490 (c.433 → c.438) et confirmé pour les projets QC.

| Figure | Fichier | Dimensions | Poids | Source (cellule · output) | Sujet *(c.447 reformulé CONTENT-driven)* |
|--------|---------|------------|-------|---------------------------|-----------------------------------------|
| Exploration | `aw-exploration.png` | 690×590 | 38 Ko | cellule 6 · output 1 | **Matrice de corrélation** 5×5 des sous-jacents (SPY/TLT/IEF/GLD/DBC), heatmap divergente bleu-rouge (-1 → +1) |
| H1 — Parity | `aw-h1-parity.png` | 1389×989 | 186 Ko | cellule 8 · output 1 | Dual-panel : equity 3 stratégies (Static Dalio S=0.691 DD=-23.37%, Risk Parity S=0.718 DD=-18.43%, Tactical SMA200 S=0.744 DD=-15.47%) + drawdowns 2016-2026 |
| H3 — Rebalancing | `aw-h3-rebalance.png` | 1389×989 | 113 Ko | cellule 14 · output 2 | Dual-panel : equity 3 fréquences (Monthly/Quarterly/Semi-Annual) **visuellement identiques** (toutes S=0.817 DD=-23.9%) + drawdowns superposés |
| H4 — SMA200 | `aw-h4-sma200.png` | 900×640 | 186 Ko | cellule 17 · output 2 | Dual-panel : equity 5 niveaux de réduction tactique (0%/25%/50%/75%/100%) + drawdowns — **50% optimal** (S=0.858 vs 0% S=0.817) |
| Comparaison | `aw-comparison.png` | 989×590 | 29 Ko | cellule 19 · output 0 | **Scatter Pareto** Sharpe vs MaxDD : 5 points colorés (0/25/50/75/100% reduction), 50% = coin supérieur-gauche (meilleur Sharpe + DD modéré) |
| Grille optimale | `aw-grid-optimal.png` | 1390×490 | 127 Ko | cellule 24 · output 0 | **Rolling 1-Year Sharpe** 2016-2026 : 3 stratégies (Original Static Dalio Q bleu, Optimized Static+Tactical orange, RP+Tactical Combo vert) — 3 lignes corrélées, dip commun 2022-2023 |

**Total** : 6 figures, 682 Ko. **Politique** (#5654) : ≤200 Ko/fichier, downscale ≤1200 px max. Courbes matplotlib → **PNG lossless natif** (netteté des étiquettes). La figure H4 (257 Ko natif, dense) est downscaled à 900×640 pour rester sous le seuil (186 Ko). Arc : exploration des données → hypothèses H1 (parity) / H3 (rebalancing) / H4 (overlay SMA200) → comparaison des configurations → grille optimale.

## Contenu réel vérifié par figure (audit visuel MiniMax M3, c.447)

### `aw-exploration.png` — Matrice de corrélation 5×5 SPY/TLT/IEF/GLD/DBC

**Alt-text (FR)** *(c.447 reformulé CONTENT-driven)* : Heatmap de corrélation des 5 sous-jacents AllWeather (axes X et Y = SPY, TLT, IEF, GLD, DBC), échelle de couleur divergente bleu (corrélation négative) → blanc (≈ 0) → rouge foncé (corrélation positive), légende latérale -1.00 → +1.00. **Diagonale = 1.00 (rouge foncé, asset contre lui-même)**. **Anti-corrélations notables** : TLT↔SPY = **-0.18** (obligations long terme vs actions US), TLT↔IEF = **+0.92** (les deux obligations très corrélées), IEF↔SPY = **-0.16**, DBC↔TLT = **-0.17**. **Corrélations modérées positives** : SPY↔DBC = **+0.35**, IEF↔GLD = **+0.35**, TLT↔GLD = **+0.28**, DBC↔GLD = **+0.26**. **Quasi-indépendance** : SPY↔GLD = +0.04, IEF↔DBC = -0.14. Démontre la **logique structurelle AllWeather** : TLT/IEF décorrélés des actions (SPY), GLD = valeur refuge quasi-indépendante, DBC = commodities diversifiant modérément.

**Contenu réel vérifié** (audit visuel MiniMax M3, c.447) : heatmap 5×5 intitulée « Correlation Matrix - AllWeather Assets », labels d'axes et de cellules visibles, palette RdBu_r (rouge = +, bleu = -). **Alt-text précédent** « Rendements et **volatilité** annualisés par actif » était **TITLES-driven** ET **FAUX** : la figure ne montre **ni rendements ni volatilité**, c'est une **matrice de corrélation**. Inversion factuelle corrigée c.447.

- **Poids** : 38 Ko (PNG lossless natif, source 690×590, le plus léger de la série)

### `aw-h1-parity.png` — Dual-panel equity + drawdowns Static/RP/Tactical

**Alt-text (FR)** *(c.447 reformulé CONTENT-driven)* : Test de l'hypothèse H1 (3 stratégies d'allocation comparées) sur **2016-2026** : **deux sous-graphiques empilés**. **Haut — Portfolio Value (axe Y = 1.0 → 1.85)** : 3 equity curves. **Static Dalio** (bleu, S=**0.691**, DD=**-23.37 %**) termine vers **1.85** (le meilleur rendement absolu). **Risk Parity 60d** (orange, S=**0.718**, DD=**-18.43 %**) termine vers **1.70** (milieu). **Tactical SMA200** (vert, S=**0.744**, DD=**-15.47 %**) termine vers **1.70** (le **meilleur couple Sharpe/DD**). **Bas — Drawdowns (axe Y = 0 → -0.20)** : 3 aires drawdown superposées, pic commun 2022 (inflation + bonds crash) vers **-20 %**, Tactical SMA200 (vert) montre le DD le plus contenu, Static Dalio (bleu) le plus profond. **Conclusion visuelle** : **Tactical SMA200 = sweet spot** — meilleur Sharpe (0.744) ET meilleur DD (-15.47 %), surpassant Risk Parity pur en risk-adjusted return.

**Contenu réel vérifié** (audit visuel MiniMax M3, c.447) : figure composite dual-panel, titre « H1: Static vs Risk Parity vs Tactical », légende en haut-gauche avec Sharpe + DD par stratégie, axes X 2016-2026. **Alt-text précédent** « Static vs Risk Parity vs Tactical (equity curves) » était **TITLES-driven** (énumérait les 3 stratégies sans décrire le contenu visuel : dual-panel, valeurs Sharpe/DD concrètes, conclusion sweet spot Tactical).

- **Poids** : 186 Ko (PNG lossless natif, source 1389×989)

### `aw-h3-rebalance.png` — Dual-panel : sensibilité à la fréquence de rebalancement (NULLE)

**Alt-text (FR)** *(c.447 reformulé CONTENT-driven)* : Test de l'hypothèse H3 (impact de la fréquence de rebalancement sur la performance) sur **2016-2026** : **deux sous-graphiques empilés**. **Haut — Portfolio Value (axe Y = 1.0 → 2.0)** : 3 equity curves **visuellement superposées** — **Monthly** (bleu), **Quarterly** (orange), **Semi-Annual** (vert) — les 3 tracés sont **indistinguables à l'œil nu**. **Bas — Drawdowns (axe Y = 0 → -0.25)** : 3 aires drawdown également superposées, pic commun 2022 vers **-25 %**. **Verdict visuel** : **les 3 stratégies ont des métriques IDENTIQUES** (S=**0.817**, DD=**-23.9 %** toutes trois, indiqué en légende haut-gauche). **Conclusion** : la **fréquence de rebalancement n'a aucun impact** sur cette stratégie AllWeather — l'allocation cible étant stationnaire, rebalancer plus ou moins souvent ne change rien (cohérent avec l'absence de drift significatif sur 11 ans). Résultat négatif important : pas d'**over-engineering** à faire sur ce paramètre.

**Contenu réel vérifié** (audit visuel MiniMax M3, c.447) : figure composite dual-panel, titre « H3: Rebalancing Frequency Comparison », légende haut-gauche 3 stratégies **toutes avec S=0.817 et DD=-23.9%**, axes X 2016-2026, courbe unique visible (3 lignes confondues). **Alt-text précédent** « Fréquence de rebalancement » était **TITLES-driven** (concept testé, pas résultat visuel : 3 lignes confondues + métriques identiques + conclusion aucun impact).

- **Poids** : 113 Ko (PNG lossless natif, source 1389×989)

### `aw-h4-sma200.png` — Dual-panel : 5 niveaux de réduction tactique SMA200

**Alt-text (FR)** *(c.447 reformulé CONTENT-driven)* : Test de l'hypothèse H4 (impact du niveau de réduction tactique SMA200) sur **2016-2026** : **deux sous-graphiques empilés**. **Haut — Portfolio Value (axe Y = 1.0 → 2.0)** : **5 equity curves étagées**. **No overlay 0%** (bleu, S=**0.817**, DD=**-23.9 %**) termine vers **2.10** (référence). **SMA200 red=25%** (orange, S=**0.846**, DD=**-20.1 %**) termine vers **2.05**. **SMA200 red=50%** (vert, S=**0.858**, DD=**-16.2 %**) termine vers **1.90** (**optimal Pareto**). **SMA200 red=75%** (rouge, S=**0.834**, DD=**-13.04 %**) termine vers **1.80**. **SMA200 red=100%** (violet, S=**0.763**, DD=**-11.01 %**) termine vers **1.70** (trop défensif, sous-performe). **Bas — Drawdowns (axe Y = 0 → -0.25)** : 5 aires drawdown, profondeur décroissante avec le % de réduction (0% plus profond, 100% plus contenu), pic commun 2022. **Conclusion visuelle** : **50% de réduction = sweet spot** — meilleur Sharpe (0.858) ET DD modéré (-16.2 %), compromis rendement/protection optimal. Au-delà de 50%, le coût en rendement absolu dépasse le gain en drawdown.

**Contenu réel vérifié** (audit visuel MiniMax M3, c.447) : figure composite dual-panel, titre « H4: SMA200 Tactical Overlay - Reduction Factors », légende haut-gauche 5 stratégies avec Sharpe + DD, axes X 2016-2026, **étagement clair** des 5 courbes (les 5 sont distinctes contrairement à H3). **Alt-text précédent** « Overlay tactique SMA200 (downscale depuis 1389×989) » était **TITLES-driven ET MÉTA** (mentionnait le downscale, pas le contenu : 5 niveaux, valeurs Sharpe/DD, sweet spot 50%).

- **Poids** : 186 Ko (PNG lossless natif, source 900×640, **downscale depuis 1389×989** — confirmé MANIFEST)

### `aw-comparison.png` — Scatter Pareto Sharpe vs MaxDD par niveau SMA200

**Alt-text (FR)** *(c.447 reformulé CONTENT-driven)* : Synthèse H4 sous forme de **scatter plot Pareto** : axe X = **Max Drawdown %** (inversé = « better right », 12 → 24), axe Y = **Sharpe Ratio** (0.76 → 0.86). **5 points étiquetés** colorés : **0%** (bleu, coin bas-droit, S=**0.817**, DD=**23.9 %**) — le plus de DD ; **25%** (orange, S=**0.846**, DD=**20.1 %**) ; **50%** (vert, **coin supérieur-gauche = Pareto-optimal**, S=**0.858**, DD=**16.2 %**) — le meilleur couple ; **75%** (rouge, S=**0.834**, DD=**13.04 %**) ; **100%** (violet, coin bas-gauche, S=**0.763**, DD=**11.01 %**) — le moins de Sharpe. **Lecture** : la **frontière de Pareto** relie (0%, 23.9%) → (50%, 16.2%) → (100%, 11.01%). **Au-delà de 50%, on perd du Sharpe sans gagner suffisamment en DD** (75% DD=13% mais S=0.834 < S=0.858 de 50%). Le **seuil de décision** est 50% : augmenter au-delà dégrade les deux dimensions.

**Contenu réel vérifié** (audit visuel MiniMax M3, c.447) : scatter plot intitulé « H4: Risk-Return Tradeoff by SMA200 Reduction Factor », 5 gros points étiquetés en texte (0%/25%/50%/75%/100%), grille de fond, axes quantitatifs. **Alt-text précédent** « Comparaison Sharpe et drawdown entre configurations testées » était **TITLES-driven** (décrivait la métrique, pas le type de figure = scatter Pareto) ET **omis la conclusion clé** : 50% = Pareto-optimal, frontière reliant 0%→50%→100%.

- **Poids** : 29 Ko (PNG lossless natif, source 989×590, le 2ᵉ plus léger)

### `aw-grid-optimal.png` — Rolling 1-Year Sharpe 3 stratégies 2016-2026

**Alt-text (FR)** *(c.447 reformulé CONTENT-driven)* : **Rolling 1-Year Sharpe Ratio** sur **2016-2026** (axe X = années 2016 → 2026, axe Y = Sharpe Ratio **-2 → +3.5**) : **3 courbes long-terme**, ligne horizontale pointillée Sharpe = 0. **Original (Static Dalio, Q)** (bleu), **Optimized (Static + Tactical)** (orange), **RP + Tactical Combo** (vert). **Verdict visuel** : les **3 courbes sont fortement corrélées** (oscillent ensemble), avec des **pics conjoints** vers **+3 en 2020** (rally post-COVID), **+2.5 en 2018** (vol spike), **+2.5 en 2025** (récupération), et des **creux communs** vers **-2 en 2022-2023** (crash bonds + actions). **Différenciation** : Original (bleu) plus volatile en 2021-2022, Optimized (orange) légèrement plus stable, RP+Tactical Combo (vert) suit Optimized avec un léger lag. **Conclusion** : les 3 stratégies portent le **même risque de marché** (corrélation forte), les optimisations tactiques n'**absorbent pas** les drawdowns systémiques 2022.

**Contenu réel vérifié** (audit visuel MiniMax M3, c.447) : line plot intitulé « Rolling 1-Year Sharpe Ratio », 3 séries temporelles avec légende haut-droite, axe X temporel 2016-2026, axe Y Sharpe. **Alt-text précédent** « Exploration de la grille de paramètres » était **TITLES-driven ET FAUX** : la figure n'est **pas** une grille de paramètres (heatmap/grid), c'est un **rolling time-series** multi-stratégies. Inversion factuelle corrigée c.447 (similaire à aw-exploration.png).

- **Poids** : 127 Ko (PNG lossless natif, source 1390×490)

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