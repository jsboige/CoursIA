# Manifeste des figures — DualMomentum

Provenance de chaque figure (convention d'indexation **all-cells** du module `extract_readme_figures.py` : `cellule` = indice de cellule dans le notebook, `output` = indice de sortie de cette cellule). Sources vérifiées sur `origin/main`, extraites de [`research.ipynb`](../../research.ipynb) (notebook de recherche local).

> **Audit vision po-2026 c.438 (2026-07-14, doctrine #5780)** : les 4 PNG ci-dessous ont été ouverts un par un via l'outil `Read` et comparés à leur alt-text. Verdict par figure dans le champ *Contenu réel vérifié*. Cohérence caption ↔ image = **0/4 exacte, 4 corrections d'alt-text appliquées** — tous les alt-texts d'origine étaient **generiques** (un seul mot ou expression methode/conclusion : «Exploration», «Drawdown», «H2 — Lookback», «Sharpe»), ometant la structure dual-panel/3-panneaux et les valeurs concretes visibles (BND/EFA/SPY, periodes 2015-2026, max drawdown -25%, Sharpe glissant 12 mois, etc.), defaut fondateur type isole par L490 c.433 + c.436 + c.437.

| Figure | Fichier | Dimensions | Poids | Source (cellule · output) | Sujet |
|--------|---------|------------|-------|---------------------------|-------|
| Exploration | `dm-exploration.png` | 1590×590 | 122 Ko | cellule 4 · output 1 | Analyse exploratoire (§2) |
| Drawdown | `dm-drawdown.png` | 1589×1389 | 170 Ko | cellule 14 · output 0 | Comparaison des drawdowns entre configurations |
| H2 — Lookback | `dm-h2-lookback.png` | 1389×490 | 23 Ko | cellule 16 · output 1 | Robustesse par lookback period (hypothèse 2) |
| Sharpe | `dm-sharpe.png` | 1389×490 | 76 Ko | cellule 21 · output 1 | Comparaison du Sharpe entre configurations |

**Total** : 4 figures, 392 Ko. **Politique** (#5654) : ≤200 Ko/fichier, downscale ≤1200 px max. Courbes matplotlib → **PNG lossless natif** (tous sous le seuil sans downscale, max 170 Ko). Arc : exploration → comparaison des drawdowns → robustesse au lookback (H2) → comparaison du Sharpe. Stratégie documentée comme remplacée par DualMomentumNoTLT (contre-exemple pédagogique, échec TLT 2022).

## Contenu réel vérifié par figure (audit visuel MiniMax M3, c.438)

### `dm-exploration.png` — Analyse exploratoire dual-panel (BND/EFA/SPY)

**Alt-text (FR)** *(c.438 reformulé CONTENT-driven)* : Analyse exploratoire des 3 sous-jacents **2015-2026** : **deux sous-graphiques côte-à-côte**. **Gauche** — rendements cumulés Buy & Hold (axe Y = 1.0 → 4.0) sur 11 ans : **BND** (obligations, bleu) termine ~1.25, **EFA** (Europe/Japon, orange) termine ~2.20, **SPY** (US, vert) termine **~4.0** (le grand gagnant). **Droite** — volatilité réalisée 63 jours annualisée (axe Y = 0 → 0.60) des 3 mêmes sous-jacents : pic commun **mars 2020 (COVID)** vers **0.60 pour SPY** (vert), rebond vers **0.34** vers 2024. La BND reste la moins volatile (~0.05-0.10) sur toute la période — confirmation du rôle « valeur refuge » dans la stratégie dual-momentum.

**Contenu réel vérifié** (audit visuel MiniMax M3, c.438) : figure composite à 2 panneaux titrés « Rendements cumulés 2015-2026 (Buy & Hold) » et « Volatilité réalisée 63j (annualisée) ». 3 séries temporelles par panneau, légende implicite par couleur (BND bleu, EFA orange, SPY vert). **Alt-text précédent** «Analyse exploratoire (§2)» était **TITLES-driven** (decrit la section du notebook, pas le visuel) — corrigé c.438 pour decrire **CONTENT-driven** : structure dual-panel, tickers BND/EFA/SPY concrets, periode 2015-2026, valeur concrete SPY ~4.0, pic volatilite COVID 0.60 / 2024 ~0.34.

- **Poids** : 122 Ko (PNG lossless natif, source 1590×590)

### `dm-drawdown.png` — Triple-panel equity/holdings/drawdown

**Alt-text (FR)** *(c.438 reformulé CONTENT-driven)* : Diagnostic complet Dual Momentum vs SPY Buy & Hold **2015-2026** : **trois sous-graphiques empilés**. **Haut** — equity cumulée comparée : **Dual Momentum** (bleu, plein) termine ~2.25, **SPY B&H** (orange, tirets) termine **~3.9** (le buy-and-hold gagne sur la période complète, grace au rally 2017+2020+2024). **Milieu** — Holdings par mois en barres verticales empilées : **SPY** (vert) domine quand le momentum US est positif, **EFA** (bleu) prend le relais sur les periodes Europe forte (2017), **BND** (gris) sert de refuge lors des stress (2022). **Bas** — Drawdown comparison : courbe **Dual Momentum** (bleu, aire bleu clair) atteint **max DD ~-25 % vers 2022-2023**, tandis que **SPY B&H** (orange tirets) subit le meme choc mais sur une fenêtre plus courte — l'aire bleu clair entre les 2 courbes = période d'écart de drawdown. Démontre que la stratégie **préserve le capital en stress** (DD contenu) **au prix d'un rendement absolu inférieur**.

**Contenu réel vérifié** (audit visuel MiniMax M3, c.438) : figure composite à **3 panneaux** (grille verticale). Haut : equity cumulée 2 séries. Milieu : stacked bars mensuels coloré par ticker. Bas : 2 courbes de drawdown avec aire entre les deux. **Alt-text précédent** «Comparaison des drawdowns entre configurations» etait TITLES-driven (section §3 du notebook, omet structure 3 panneaux) — corrigé c.438 pour decrire CONTENT-driven : structure 3 panneaux, equity Dual Momentum ~2.25 vs SPY ~3.9, max DD -25% vers 2022-2023, rotation holdings SPY/EFA/BND.

- **Poids** : 170 Ko (PNG lossless natif, source 1589×1389)

### `dm-h2-lookback.png` — Robustesse Sharpe/MaxDD par lookback (3-24 mois)

**Alt-text (FR)** *(c.438 reformulé CONTENT-driven)* : Test de robustesse H2 (impact du lookback period sur la performance) : **deux sous-graphiques côte-à-côte**, **6 lookbacks testés** (3, 6, 9, 12, 18, 24 mois). **Gauche** — Sharpe Ratio (axe Y = 0 → 0.85, barres bleues) : **3 mois** ~0.62, **6 mois** ~0.39 (le pire), **9 mois** ~0.46, **12 mois** ~0.46, **18 mois** ~0.60, **24 mois** ~**0.88 (le meilleur)**. **Droite** — Max Drawdown absolu (axe Y = 0 → 0.27, barres saumon/orange) : **3 mois** ~0.20, **6 mois** ~0.24, **9 mois** ~0.20, **12 mois** ~0.20, **18 mois** ~**0.27 (le pire)**, **24 mois** ~0.24. **Conclusion visuelle** : **le lookback 24 mois offre le meilleur couple Sharpe/MaxDD** (~0.88 Sharpe pour ~24% DD), tandis que **18 mois est à éviter** (Sharpe 0.60 mais DD 27%). Pas de corrélation monotone entre longueur du lookback et performance — la robustesse est non-linéaire.

**Contenu réel vérifié** (audit visuel MiniMax M3, c.438) : bar chart double, gauche «Sharpe Ratio par Lookback» (bleu), droite «Max Drawdown par Lookback (abs)» (saumon). 6 catégories X communes (3, 6, 9, 12, 18, 24 mois). **Alt-text précédent** «Robustesse par lookback period (hypothèse 2)» etait TITLES-driven (hypothese testee, pas le resultat visuel) — corrigé c.438 pour decrire CONTENT-driven : structure dual-panel bar charts, valeurs concretes Sharpe 0.39-0.88, MaxDD 0.20-0.27, conclusion lookback 24 mois optimal vs 18 mois sous-optimal.

- **Poids** : 23 Ko (PNG lossless natif, source 1389×490, le plus leger)

### `dm-sharpe.png` — Sharpe Ratio glissant 12 mois 2016-2025

**Alt-text (FR)** *(c.438 reformulé CONTENT-driven)* : Analyse de stabilité temporelle du **Sharpe Ratio glissant sur 12 mois** (axe Y = -2 → +5, axe X = 2016 → 2025) : **deux courbes** + une ligne de référence. **Dual Momentum** (bleu, plein) oscille autour de **SPY B&H** (orange, tirets), mais **sous-performe presque toujours** (Dual Momentum plus bas sur la majeure partie de la période). Pics conjoints vers **+4.5 en 2017** (rally synchronized) ; Dual Momentum touche **-1.8 vers 2018-2019** (sous-performance marquee), remonte vers **+1.5 vers 2024**, finit vers **+1.2** vs SPY ~+1.4 fin 2025. **Sharpe=0.5 target** (ligne horizontale verte pointillée) = seuil de rentabilité ajustée au risque — les 2 strategies passent au-dessus en 2017, 2020, 2021, 2024, et **plongent en dessous en 2018-2019, 2022-2023** (stress periods ou momentum défavorable). Démontre la **forte variance temporelle** du momentum (fenetre de lookback glissante = signal bruité).

**Contenu réel vérifié** (audit visuel MiniMax M3, c.438) : line plot «Sharpe Ratio glissant 12 mois», 2 series Dual Momentum (bleu plein) vs SPY B&H (orange tirets), ligne horizontale verte pointillée «Sharpe=0.5 target», legende en haut-droite, axe X 2016-2025. **Alt-text précédent** «Comparaison du Sharpe entre configurations» etait TITLES-driven (methode de comparaison, pas le resultat) — corrigé c.438 pour decrire CONTENT-driven : structure line plot unique, 2 series + baseline 0.5, valeurs concretes -1.8 vers 2018, +4.5 vers 2017, +1.2 fin 2025, pedagogie variance temporelle momentum.

- **Poids** : 76 Ko (PNG lossless natif, source 1389×490)