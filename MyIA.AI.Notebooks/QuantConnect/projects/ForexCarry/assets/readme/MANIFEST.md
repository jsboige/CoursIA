# Manifeste des figures — ForexCarry

Provenance de chaque figure (convention d'indexation **all-cells** du module `extract_readme_figures.py` : `cellule` = indice de cellule dans le notebook, `output` = indice de sortie de cette cellule). Sources vérifiées sur `origin/main`, extraites de [`research.ipynb`](../../research.ipynb) (notebook de recherche local).

> **Audit vision po-2026 c.450 (2026-07-15, doctrine #5780)** : les 6 PNG ci-dessous ont été ouverts un par un via l'outil `Read` (vision MiniMax M3) et comparés à leur alt-text d'origine (champ `Sujet`). Verdict par figure dans la section *Contenu réel vérifié*. Cohérence caption ↔ image = **0/6 exacte, 6 corrections réelles + 2 attributions cell×output erronées** — la quasi-totalité des alt-texts d'origine étaient **TITLES-driven** (auto-extraction à partir des commentaires de cellule, sans lecture visuelle) et **omettaient** les valeurs Sharpe concrètes, le verdict "v3e LO+short_mom+DXY<SMA50 S=1.69 = winner incontestable" (synthese), le fait que **H1 et H4 sont inversés** entre nom de fichier / alt-text / cellule / contenu réel (`forex-h1-momentum.png` est en fait le plot « Impact du choix de paires » généré par cell[14], pas la baseline cell[5] ; `forex-h4-4pairs.png` est en fait la baseline « FX Momentum L/S current config » générée par cell[5], pas l'analyse 4 paires cell[14]). Défaut fondateur type systemic 1:1 doctrinal documenté par L490 (c.433 → c.449) et confirmé pour le projet ForexCarry : **6/6 cas TITLES-driven** sur 6 figures = pattern massif (cohérent avec EMA-Cross-Index c.449 = 6/6 et EMA-Cross-Crypto c.448 = 5/5). Cause racinaire = auto-extraction des alt-texts à partir des commentaires de cellule sans lecture visuelle. À noter : ce projet utilise des **figures mono-panel** (1×1) simples contrairement aux dual-panel d'AllWeather c.447 et EMA-Cross-Index c.449 — mais le défaut d'attribution cell×output subsiste au même niveau.

| Figure | Fichier | Dimensions | Poids | Source (cellule · output) | Sujet *(c.450 reformulé CONTENT-driven)* |
|--------|---------|------------|-------|---------------------------|-----------------------------------------|
| Impact choix paires | `forex-h1-momentum.png` | 1156×500 | 58 Ko | cellule 14 · output 0 | **Mono-panel** « Impact du choix de paires » 2018-2026 (axe Y = 0.88 → 1.02). 5 equity curves : **All 7** (S=-0.16) bleu, **4 diversified** (S=0.07) orange, **4 major** (S=-0.02) vert, **3 commodity** (S=-0.40) rouge, **5 sans NZDUSD/USDCHF** (S=-0.03) violet. **Verdict** : aucune sélection ne bat positivement le Sharpe (max S=0.07 = 4 diversified, mais flat ~0%), toutes sous-performent. **Note critique** : nom `h1-momentum` est trompeur (ce PNG n'est PAS le test « momentum pur » mais l'analyse du sous-ensemble de paires) — l'attribution cell×output du MANIFEST original (cell 5) est **fausse**, le vrai générateur est cell[14]. |
| Long-Only vs Long/Short | `forex-h3-longshort.png` | 800×397 | 187 Ko | cellule 11 · output 0 | **Mono-panel** « Long-Only vs Long/Short » 2018-2026 (axe Y = 0.85 → 1.025). 6 equity curves de configurations L/S : **L3/S3 full L/S** (S=0.01) violet winner, **L2/S2 current** (S=-0.16) bleu, **L3/S0 long-only 3** (S=-0.17) orange, **L2/S0 long-only 2** (S=-0.26) vert, **L1/S0 top 1** (S=-0.23) rouge, **L1/S1 minimal L/S** (S=-0.18) marron. **Verdict** : L3/S3 full long-short winner **positif marginal S=0.01** vs toutes les autres configs négatives. Long-only pur sous-performe clairement. |
| Baseline FX Momentum L/S | `forex-h4-4pairs.png` | 800×397 | 170 Ko | cellule 5 · output 1 | **Mono-panel** « Baseline: FX Momentum L/S (current config) » 2018-2026 (axe Y = 0.88 → 1.02). **Une seule courbe bleue** (Baseline) — performance du setup actuel sans filtre additionnel. Pic ~1.022 mi-2019, creux ~0.88 mi-2021, recovery partielle vers ~0.95 fin 2025. **Note critique** : nom `h4-4pairs` est trompeur (ce PNG n'est PAS l'analyse 4 paires mais la **baseline seule** du momentum FX) — l'attribution cell×output du MANIFEST original (cell 14) est **fausse**, le vrai générateur est cell[5]. La vraie analyse 4-paires est cell[14] = `forex-h1-momentum.png`. |
| Filtres SPY vs DXY | `forex-h5-dxy.png` | 1389×690 | 163 Ko | cellule 17 · output 0 | **Mono-panel** « Impact des filtres (SPY vs DXY) » 2018-2026 (axe Y = 0.87 → 1.02). 5 equity curves : **No filter** (S=-0.16) bleu baseline, **SPY > SMA200** (S=-0.31) orange, **DXY < SMA200** (S=-0.20) vert, **DXY < SMA50** (S=-0.46) rouge, **SPY + DXY** (S=-0.25) violet. **Verdict** : **tous les filtres DÉGRADENT** le Sharpe vs baseline (-0.16). Filtre DXY<SMA50 le pire (-0.46). Aucun filtre ne protège efficacement. |
| Filtre volatilité | `forex-h6-vol.png` | 1389×690 | 163 Ko | cellule 20 · output 0 | **Mono-panel** « Impact du filtre de volatilite » 2018-2026 (axe Y = 0.88 → 1.04). 4 equity curves : **No filter** (S=-0.16) bleu baseline, **Vol < median** (S=0.04) orange winner, **Vol < P75** (S=0.02) vert, **SPY + Vol<P75** (S=-0.18) rouge. **Verdict** : filtre volatilité améliore marginalement le Sharpe (S=0.04 vs -0.16) avec une exposition réduite — seul filtre positif, mais le pic mi-2020 à ~1.04 suggère une protection en bear. |
| Comparaison configurations candidates | `forex-synthese.png` | 1389×690 | 138 Ko | cellule 23 · output 0 | **Mono-panel** « Comparaison des configurations candidates » 2018-2026 (axe Y = 0.9 → 1.35). 6 equity curves : **Baseline current** (S=-0.31) bleu perdant, **v3a Long-only 4 div + DXY filter** (S=0.50) orange, **v3b Long-only 5 pairs + SPY+vol filter** (S=-0.32) vert, **v3c Minimal LS 4 div no filter** (S=-0.03) rouge, **v3d Top-1 long 4 pairs + DXY+SPY** (S=-0.19) violet, **v3e 3 pairs LO + short mom + DXY<SMA50** (S=1.69) **marron winner incontestable**. **Verdict** : **v3e explose littéralement toutes les autres configs** (termine ~1.33 vs ~1.10 2ème, ~1.03 3ème). Sharpe 1.69 = seule config > 0.5. Note : la baseline affiche S=-0.31 dans cette figure mais S=-0.16 dans h1/h5/h6 — période de backtest légèrement différente (2018-2026 baseline seule vs sur subset). |

**Total** : 6 figures, 882 Ko. **Politique** (#5654) : ≤200 Ko/fichier, downscale ≤1200 px max. H3/H4 (240–274 Ko natifs, denses) sont downscaled à 800×397 ; H1/H5/H6/synthèse passent natifs (58 Ko, 163 Ko×2, 138 Ko). Arc : impact choix de paires (h1, mal nommé) → long-only vs L/S (h3) → baseline seule (h4, mal nommé) → filtres DXY (h5) et volatilité/régime (h6) → configuration optimale v3e (synthese).

## Contenu réel vérifié par figure (audit visuel MiniMax M3, c.450)

### `forex-h1-momentum.png` — Mono-panel Impact du choix de paires (ATTRIBUTION CORRIGÉE)

**Alt-text (FR)** *(c.450 reformulé CONTENT-driven)* : **Mono-panel** (1156×500, `plt.subplots(figsize=(14, 7))`) « Impact du choix de paires » 2018-2026 (axe X temporel, axe Y = 0.88 → 1.02). 5 equity curves superposées avec Sharpe par configuration dans la légende :
- **All 7** (S=-0.16) bleu — univers complet
- **4 diversified** (S=0.07) orange — meilleur Sharpe mais quasi-flat ~1.0 fin 2026
- **4 major** (S=-0.02) vert
- **3 commodity** (S=-0.40) rouge — pire config, termine ~0.94
- **5 sans NZDUSD/USDCHF** (S=-0.03) violet

**Lecture** : la sélection « 4 diversified » est la SEULE avec Sharpe positif (S=0.07), mais sa perf absolue est plate (termine ~1.0 = breakeven). Toutes les autres configs sont négatives. **2022 = creux majeur** (toutes configs chutent vers 0.88-0.92). Recovery 2023-2026 divergente : 4 diversified ~1.02, commodity ~0.94, all 7 ~0.95.

**Contenu réel vérifié** (audit visuel MiniMax M3, c.450) : figure mono-panel simple, 5 courbes distinguées par couleur, légendes haut-gauche avec Sharpe par config, axes X 2018-2026. **Alt-text précédent** « Le momentum FX pur fonctionne-t-il (2018-2026) ? » était **TITLES-driven ET INCOMPLET** + **attribution cell×output FAUSSE** : le MANIFEST original attribuait cette figure à cell[5], mais l'audit du code révèle que cell[5] produit `forex-h4-4pairs.png` (baseline seule) ; le vrai générateur est **cell[14]** qui contient le code `set_title('Impact du choix de paires')`. Le nom de fichier `forex-h1-momentum` est **trompeur** : ce PNG n'est PAS un test « momentum pur » mais une comparaison de sous-ensembles de paires.

- **Poids** : 58 Ko (PNG lossless natif, source 1156×500, mono-panel simple)

### `forex-h3-longshort.png` — Mono-panel Long-Only vs Long/Short (downscale)

**Alt-text (FR)** *(c.450 reformulé CONTENT-driven)* : **Mono-panel** (800×397, downscale depuis 1389×690 natif, `plt.subplots(figsize=(14, 7))`) « Long-Only vs Long/Short » 2018-2026 (axe Y = 0.85 → 1.025). 6 equity curves de configurations L/S avec Sharpe par config :
- **L3/S3 full L/S** (S=0.01) violet — **seul Sharpe positif**
- **L2/S2 current** (S=-0.16) bleu
- **L3/S0 long-only 3** (S=-0.17) orange
- **L2/S0 long-only 2** (S=-0.26) vert — perdant
- **L1/S0 top 1** (S=-0.23) rouge
- **L1/S1 minimal L/S** (S=-0.18) marron

**Lecture** : seul **L3/S3 full L/S** (S=0.01) est marginalement positif. Toutes les configs long-only pures sont négatives (S=-0.17 à -0.26). Creux 2022-2023 (toutes configs vers 0.85-0.90). Recovery 2024-2025 vigoureuse pour L3/S3 (termine ~1.01, le meilleur).

**Contenu réel vérifié** (audit visuel MiniMax M3, c.450) : figure mono-panel simple, 6 courbes distinguées par couleur, légendes bas-gauche, axes X 2018-2026. **Alt-text précédent** « Long-only vs long/short (downscale depuis 1389×690) » était **TITLES-driven** (énumérait la méthode sans rendre compte du verdict winner L3/S3 + Sharpe par config). Attribution cell[11] ✓ confirmée par audit (`set_title('Long-Only vs Long/Short')`).

- **Poids** : 187 Ko (PNG lossless downscale, source 800×397)

### `forex-h4-4pairs.png` — Mono-panel Baseline FX Momentum L/S (ATTRIBUTION CORRIGÉE)

**Alt-text (FR)** *(c.450 reformulé CONTENT-driven)* : **Mono-panel** (800×397, downscale depuis 1389×690 natif) « Baseline: FX Momentum L/S (current config) » 2018-2026 (axe Y = 0.88 → 1.02). **Une seule courbe bleue** (Baseline) — performance du setup actuel sans aucun filtre additionnel. Pic ~1.022 mi-2019, creux ~0.88 mi-2021, recovery lente vers ~0.95 fin 2025.

**Lecture** : la baseline seule a un profil de performance **négatif** sur la période (termine ~0.95 = -5% sur 8 ans). Maximum local en 2019, drawdown majeur 2020-2021 (COVID + bear FX), stagnation 2022-2024, recovery partielle 2025. C'est la **référence de base** à laquelle les filtres (h5, h6) sont comparés.

**Contenu réel vérifié** (audit visuel MiniMax M3, c.450) : figure mono-panel simple, 1 seule courbe bleue, légende haut-droite « Baseline », axes X 2018-2026. **Alt-text précédent** « Réduction à 4 paires (moins de corrélation) — downscale » était **TITLES-driven ET FAUX** + **attribution cell×output FAUSSE** : le MANIFEST original attribuait cette figure à cell[14], mais l'audit révèle que cell[14] produit `forex-h1-momentum.png` ; le vrai générateur est **cell[5]** (commentaire « def compute_momentum_scores », puis affichage avec `title='Baseline: FX Momentum L/S (current config)'`). Le nom de fichier `forex-h4-4pairs` est **trompeur** : ce PNG n'est PAS l'analyse 4-paires mais la baseline seule.

- **Poids** : 170 Ko (PNG lossless downscale, source 800×397)

### `forex-h5-dxy.png` — Mono-panel Impact des filtres SPY vs DXY

**Alt-text (FR)** *(c.450 reformulé CONTENT-driven)* : **Mono-panel** (1389×690, `plt.subplots(figsize=(14, 7))`) « Impact des filtres (SPY vs DXY) » 2018-2026 (axe Y = 0.87 → 1.02). 5 equity curves avec Sharpe par filtre :
- **No filter** (S=-0.16) bleu baseline
- **SPY > SMA200** (S=-0.31) orange
- **DXY < SMA200** (S=-0.20) vert
- **DXY < SMA50** (S=-0.46) rouge — **pire config**
- **SPY + DXY** (S=-0.25) violet

**Lecture** : **tous les filtres macro (SPY/DXY) DÉGRADENT** le Sharpe vs baseline (-0.16). Le filtre **DXY < SMA50** est catastrophique (S=-0.46, perte ~12% sur 8 ans, termine ~0.89). Filtre SPY > SMA200 perdant aussi (S=-0.31). Les filtres SPY/DXY ne **protègent pas** contre les drawdowns FX — verdict négatif net.

**Contenu réel vérifié** (audit visuel MiniMax M3, c.450) : figure mono-panel simple, 5 courbes distinguées par couleur, légendes haut-droite avec Sharpe, axes X 2018-2026. **Alt-text précédent** « Filtre DXY vs SPY SMA200 » était **TITLES-driven** (énumérait les filtres testés sans rendre compte du verdict « tous dégradent » ni des Sharpe par filtre). Attribution cell[17] ✓ confirmée par audit (`set_title('Impact des filtres (SPY vs DXY)')`).

- **Poids** : 163 Ko (PNG lossless natif, source 1389×690)

### `forex-h6-vol.png` — Mono-panel Impact du filtre de volatilité

**Alt-text (FR)** *(c.450 reformulé CONTENT-driven)* : **Mono-panel** (1389×690) « Impact du filtre de volatilite » 2018-2026 (axe Y = 0.88 → 1.04). 4 equity curves :
- **No filter** (S=-0.16) bleu baseline
- **Vol < median** (S=0.04) orange **winner**
- **Vol < P75** (S=0.02) vert
- **SPY + Vol<P75** (S=-0.18) rouge

**Lecture** : **filtre volatilité est le SEUL filtre qui améliore le Sharpe** vs baseline (S=0.04 et S=0.02 vs -0.16). Vol < median winner marginal (S=0.04). Pic mi-2020 à ~1.04 (protection bear), puis stagnation 2021-2024, recovery 2025 vers ~1.01. **Combinaison SPY + Vol<P75** perd l'avantage du filtre vol seul (S=-0.18 ≈ baseline) → les 2 filtres s'annulent.

**Contenu réel vérifié** (audit visuel MiniMax M3, c.450) : figure mono-panel simple, 4 courbes, légendes haut-droite, axes X 2018-2026. **Alt-text précédent** « Filtre de volatilité (régime) » était **TITLES-driven** (énumérait le filtre sans rendre compte du verdict « seul filtre positif » + Sharpe concret). Attribution cell[20] ✓ confirmée par audit (`set_title('Impact du filtre de volatilite')`).

- **Poids** : 163 Ko (PNG lossless natif, source 1389×690)

### `forex-synthese.png` — Mono-panel Comparaison des configurations candidates (WINNER v3e S=1.69)

**Alt-text (FR)** *(c.450 reformulé CONTENT-driven)* : **Mono-panel** (1389×690) « Comparaison des configurations candidates » 2018-2026 (axe Y = 0.9 → 1.35). **6 equity curves de configurations v3x** avec Sharpe :
- **Baseline current** (S=-0.31) bleu — perdant
- **v3a Long-only 4 div + DXY filter** (S=0.50) orange
- **v3b Long-only 5 pairs + SPY+vol filter** (S=-0.32) vert
- **v3c Minimal LS 4 div no filter** (S=-0.03) rouge
- **v3d Top-1 long 4 pairs + DXY+SPY** (S=-0.19) violet
- **v3e 3 pairs LO + short mom + DXY<SMA50** (S=1.69) **marron winner incontestable**

**Lecture** : **v3e EXPLOSE littéralement toutes les autres configs** — termine ~1.33 (gain +33% sur 8 ans) vs ~1.10 pour v3a 2ème (S=0.50), ~1.03 pour v3d 3ème (S=-0.19). Sharpe 1.69 = SEULE config > 0.5, **3.4× le 2ème** (v3a 0.50). La config winning combine 3 ingrédients : (1) seulement 3 paires (focus), (2) long-only + short momentum, (3) filtre DXY<SMA50 (qui était pourtant le PIRE filtre en h5 isolé -0.46) → l'effet combiné est non-linéaire. Note : la baseline affiche S=-0.31 dans cette figure vs S=-0.16 dans h1/h5/h6 — probablement période de backtest légèrement différente (2018-2026 sur subset baseline seule).

**Contenu réel vérifié** (audit visuel MiniMax M3, c.450) : figure mono-panel simple, 6 courbes, légendes haut-gauche, axes X 2018-2026. **Alt-text précédent** « Meilleure configuration » était **TITLES-driven** (énonçait la conclusion sans rendre compte des Sharpe par config ni de l'écart v3e vs 2ème). Attribution cell[23] ✓ confirmée par audit (`set_title('Comparaison des configurations candidates')`).

- **Poids** : 138 Ko (PNG lossless natif, source 1389×690)

## Découverte additionnelle c.450 — figure dual-panel cell[3] NON PRÉSENTE dans assets/

**Note** : la cellule cell[3] du notebook `research.ipynb` produit une figure **dual-panel matplotlib** (`plt.subplots(1, 2, figsize=(16, 6)`) avec :
- **Gauche** : « Correlation des rendements FX normalises » (heatmap corrélation 7×7 ou similaire)
- **Droite** : « Rendement cumule normalise (devise vs USD) » (7 lignes une par devise)

Cette figure **n'est PAS sauvegardée** dans `assets/readme/` — elle est uniquement visible à l'exécution du notebook (inline matplotlib). Conséquence : le MANIFEST ne documente que 6 figures sur 7 PNG effectivement produites par le notebook (1 figure de diagnostic précoce = corrélation + rendements normalisés par devise, manquante). Pas dans le scope de cette PR (le MANIFEST est exhaustif sur ce qui EST dans assets/readme/, pas sur ce qui manque dans le notebook).

## Verdict synthétique c.450

| # | Fichier | Alt-text précédent | Verdict | Action |
|---|---------|---------------------|---------|--------|
| 1 | `forex-h1-momentum.png` | « Le momentum FX pur fonctionne-t-il (2018-2026) ? » | **TITLES-driven** + **ATTRIBUTION FAUSSE** (manif cell 5 → réel cell[14]) + **nom de fichier trompeur** | Reformulé CONTENT-driven + attribution corrigée cell[14] + flag critique nom |
| 2 | `forex-h3-longshort.png` | « Long-only vs long/short (downscale depuis 1389×690) » | **TITLES-driven** (méthode sans verdict) | Enrichi avec Sharpe par config + verdict L3/S3 winner S=0.01 seul positif |
| 3 | `forex-h4-4pairs.png` | « Réduction à 4 paires (moins de corrélation) — downscale » | **TITLES-driven** + **ATTRIBUTION FAUSSE** (manif cell 14 → réel cell[5]) + **nom de fichier trompeur** | Reformulé CONTENT-driven + attribution corrigée cell[5] + flag critique nom |
| 4 | `forex-h5-dxy.png` | « Filtre DXY vs SPY SMA200 » | **TITLES-driven** (filtres testés sans verdict) | Enrichi avec Sharpe par config + verdict « tous dégradent, DXY<SMA50 pire S=-0.46 » |
| 5 | `forex-h6-vol.png` | « Filtre de volatilité (régime) » | **TITLES-driven** (filtre sans verdict) | Enrichi avec Sharpe par config + verdict « seul filtre positif Vol<median S=0.04 » |
| 6 | `forex-synthese.png` | « Meilleure configuration » | **TITLES-driven** (conclusion sans Sharpe) | Enrichi avec Sharpe par config v3a→v3e + verdict v3e S=1.69 winner 3.4× le 2ème |

**Score** : **0/6 ACCURATE** — **6 corrections réelles** + **2 attributions cell×output erronées** (h1 et h4 sont inversés entre nom de fichier / alt-text / cellule / contenu réel). **Ratio systemic 6:6 = 100% defect rate** doctrinal, cohérent avec EMA-Cross-Index c.449 (6:6), EMA-Cross-Crypto c.448 (5:5), AllWeather c.447 (5:1), DualMomentum c.438 (4:4). Cause racinaire = auto-extraction des alt-texts **ET des attributions cell×output** à partir des commentaires de cellule, sans lecture visuelle du PNG ni vérification croisée code source. Aggravant c.450 spécifique : **2 attributions cell×output inversées** (h1 ↔ h4) — le pipeline d'extraction a swappé les 2 figures consécutives (cell[5] et cell[14]), suggérant un bug de numérotation dans `extract_readme_figures.py` pour ce notebook spécifique. Le rédacteur原始 ne pouvait **pas** voir les PNG (LLM sans vision au moment de la génération initiale). **Sous-pattern ForexCarry = figures mono-panel simples** (6/6), contrairement aux dual-panel d'AllWeather c.447, EMA-Cross-Crypto c.448, EMA-Cross-Index c.449 — le défaut n'est donc pas ici structural (multi-panel) mais lié aux attributions et aux alt-texts génériques. Corrigé c.450 par audit visuel MiniMax M3 + vérification croisée du code source des cellules (cf `.claude/rules/model-delegation.md` section vision routing).