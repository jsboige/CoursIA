# Alpha Correlation Analysis

**Type :** Recherche (notebook analytique, sans algorithme de trading)
**Environnement :** yfinance local (cell[1] `Local environment detected`, mécanisme #8772 disclosed) — `QuantBook()` lève `NameError` (QC Cloud / Lean indisponible), branche de repli `yfinance` activée explicitement
**Période effective :** 2021-06-01 → 2026-05-29 (5 ans, 1255 sessions journalières, cell[6] data shape)

> 🇬🇧 **English version** : voir [`README.en.md`](README.en.md)
> **Issue source :** [#140 - Complementary Alpha Combinations](https://github.com/jsboige/CoursIA/issues/140) (CLOSED, scope delivered)

## Objectif

Identifier les combinaisons d'alpha réellement complémentaires pour les stratégies composites QuantConnect.

## Problème

Les composites actuels combinent des alphas corrélés :
- **TrendWeather (Sharpe 1.155)** = TrendStocks + AllWeather, mais TrendStocks domine (claim original, voir c.1284-L1 ★★ sur l'archétype « sweep-comment » pour la provenance de ce 1.155)
- **FamaFrench + AllWeather** : sweep monotone vers AllWeather (FF ne diversifie pas)
- **MomentumSector + RegimeSwitching** : double-defense en période de stress (les deux sont défensifs en même temps)

## Méthodologie (cell[1]-[36] du `quantbook.ipynb`)

1. **Return Stream Collection** : `yfinance` local 18 tickers, 1255 jours (2021-06-01 → 2026-05-29), 7 alphas construits (cell[6] + cell[20])
2. **Correlation Matrix** : matrice 7×7 des corrélations entre returns d'alphas (cell[22])
3. **Regime Analysis** : classification en 8 régimes (Bull/Bear/Sideways × High/Med/Low-Vol) puis Sharpe par régime (cell[26]-[28])
4. **Complementarity Score** : ranking des paires par score combiné (corrélation inverse × regime diversification × downside protection, cell[30])
5. **Top Pairs Analysis** : deep dive sur le top-3 par complémentarité (cell[32])
6. **Walk-Forward Validation** : OOS 15 fenêtres trimestrielles glissantes (cell[36]) — top-1 paire **Average Test Sharpe 0.84** (cell[36])

## Résultats vérifiés (multi-source : cell[N] cités)

> **Note honnête (#1621, drainage #9434)** : le README legacy présentait un tableau « Résultats préliminaires » avec 3 paires **choisies à la main**, dont **une fabriquée** : « Trend-Following + Mean-Reversion ~0.0 correlation » n'existe pas dans la matrice de corrélation cell[22] — la corrélation réelle Trend-Following / Mean-Reversion est **0.463** (cell[22] stream output). Les 2 autres lignes du tableau legacy (« EMA-Cross + All-Weather ~0.3 » et « Dual-Momentum + Mean-Reversion ~0.1 ») sont des approximations arrondies des valeurs réelles cell[34] (voir tableau ci-dessous). Le tableau ci-dessous cite **directement les outputs cell[N]** du quantbook, sans reformulation.

### Top 10 Complementary Pairs (cell[34] verbatim)

| # | Paire | Corrélation | Sharpe α₁ | Sharpe α₂ | **Sharpe combiné (50/50)** | Synergy | Regime_Div | DD_Protection |
|---|-------|-------------|-----------|-----------|----------------------------|---------|------------|---------------|
| 1 | EMA-Cross-Tech / Mean-Reversion | **0.054** | 1.105 | 0.563 | **1.210** | 0.376 | 1.919 | 0.000 |
| 2 | Momentum-SPY / Mean-Reversion | **0.101** | 0.967 | 0.563 | **1.071** | 0.306 | 1.372 | 0.045 |
| 3 | **EMA-Cross-Tech / Dual-Momentum** | **0.200** | 1.105 | 1.096 | **1.420** ⭐ | 0.320 | 1.253 | 0.163 |
| 4 | Dual-Momentum / Mean-Reversion | **0.138** | 1.096 | 0.563 | **1.171** | 0.342 | 1.084 | 0.000 |
| 5 | Momentum-SPY / Dual-Momentum | **0.248** | 0.967 | 1.096 | **1.302** | 0.270 | 1.299 | 0.000 |
| 6 | EMA-Cross-Tech / All-Weather | **0.277** | 1.105 | 0.598 | **1.128** | 0.277 | 1.616 | 0.051 |
| 7 | EMA-Cross-SPY / Mean-Reversion | **0.113** | 0.872 | 0.563 | **0.989** | 0.272 | 0.840 | 0.021 |
| 8 | Mean-Reversion / All-Weather | **0.273** | 0.563 | 0.598 | **0.722** | 0.142 | 1.080 | 0.000 |
| 9 | Dual-Momentum / Trend-Following | **0.279** | 1.096 | 0.658 | **1.128** | 0.251 | 0.980 | 0.040 |
| 10 | Momentum-SPY / All-Weather | **0.397** | 0.967 | 0.598 | **0.938** | 0.156 | 1.314 | 0.000 |

⭐ **Top combiné Sharpe** : EMA-Cross-Tech / Dual-Momentum (1.420). Note : bien que leur corrélation (0.200) soit plus haute que d'autres paires (ex. EMA-Cross-Tech / Mean-Reversion 0.054), le Sharpe combiné plus élevé (1.420 vs 1.210) tient aux deux Sharpes individuels forts (1.105 + 1.096).

### Top-3 détail (cell[32] verbatim)

| Paire | Combined Return (ann.) | Volatility | Sharpe combiné | Corrélation |
|-------|------------------------|------------|----------------|-------------|
| EMA-Cross-Tech / Mean-Reversion | 11.96 % | 9.89 % | 1.21 | 0.054 |
| Momentum-SPY / Mean-Reversion | 7.00 % | 6.53 % | 1.07 | 0.101 |
| EMA-Cross-Tech / Dual-Momentum | 19.80 % | 13.94 % | 1.42 | 0.200 |

### Sharpe par régime (cell[28] verbatim)

| Alpha | Bear-High-Vol | Bear-Med-Vol | Bull-High-Vol | Bull-Low-Vol | Bull-Med-Vol | Sideways-High-Vol | Sideways-Low-Vol | Sideways-Med-Vol |
|-------|---------------|--------------|---------------|--------------|--------------|-------------------|------------------|------------------|
| All-Weather | 1.98 | 7.04 | 0.33 | 0.18 | 1.48 | -1.14 | 0.40 | 0.51 |
| Dual-Momentum | 0.09 | 5.86 | -0.23 | 1.73 | 2.65 | 0.18 | 0.58 | 1.26 |
| EMA-Cross-SPY | 0.00 | 0.00 | 0.60 | 0.87 | 1.21 | 0.53 | 0.28 | 1.10 |
| EMA-Cross-Tech | 0.00 | -4.16 | 0.41 | 1.70 | 0.77 | -0.44 | 0.39 | 2.28 |
| Mean-Reversion | 1.02 | 4.53 | 0.00 | -0.97 | 1.42 | -1.21 | 2.32 | 0.96 |
| Momentum-SPY | 0.53 | -3.74 | 0.75 | 1.00 | 1.08 | 1.87 | 0.27 | 0.90 |
| Trend-Following | 0.69 | 2.73 | 0.78 | 0.87 | 1.19 | -0.58 | 0.07 | 0.87 |

### Walk-Forward OOS — top-1 paire (cell[36] verbatim, 15 fenêtres trimestrielles)

Paire : **EMA-Cross-Tech / Mean-Reversion** (meilleur score global cell[30]).

| Période | Train_Corr | Test_Return | Test_Sharpe |
|---------|-----------|-------------|-------------|
| 2021-06-01 → 2022-08-29 | 0.0575 | -15.19 % | -1.66 |
| 2021-08-30 → 2022-11-28 | 0.0596 | -12.98 % | -4.52 |
| 2021-11-29 → 2023-03-01 | 0.0417 | -4.23 % | -0.43 |
| 2022-03-01 → 2023-05-31 | 0.0184 | +67.48 % | **+5.44** ⭐ |
| 2022-05-31 → 2023-08-30 | 0.0133 | +19.07 % | +1.80 |
| 2022-08-30 → 2023-11-29 | 0.0396 | -25.14 % | -2.72 |
| 2022-11-29 → 2024-03-01 | 0.0176 | +34.72 % | +3.27 |
| 2023-03-02 → 2024-05-31 | 0.0170 | +27.42 % | +2.47 |
| 2023-06-01 → 2024-08-30 | 0.1387 | -9.25 % | -0.72 |
| 2023-08-31 → 2024-11-29 | 0.2589 | +21.55 % | +2.46 |
| 2023-11-30 → 2025-03-05 | 0.2861 | +2.73 % | +0.24 |
| 2024-03-04 → 2025-06-04 | 0.2483 | +9.56 % | +0.75 |
| 2024-06-03 → 2025-09-04 | 0.0742 | +35.99 % | +4.47 |
| 2024-09-03 → 2025-12-03 | 0.0082 | +28.49 % | +2.90 |
| 2024-12-02 → 2026-03-06 | 0.0233 | -9.66 % | -1.20 |
| **Moyenne OOS** | — | — | **+0.84** |

**Lecture honnête — fenêtre OOS 2021-2026 sur 5 ans** : le **Average Test Sharpe 0.84** est encourageant MAIS la variance inter-fenêtres est énorme (range -4.52 à +5.44, ratio 10×) — **la paire est sensible au regime** et l'OOS positif tient principalement à 2022-2024 (bear + recovery, contexte Mean-Reversion favorable). Les fenêtres 2023-08 / 2024-12 montrent une **dégradation Train_Corr > 0.25** (vs 0.02 in-sample) → la **stabilité in-sample → OOS n'est pas garantie**. **PAS un signal de déploiement live sans walk-forward multi-régimes** (≥4 cycles bull/bear/sideways).

## Lecture honnête — divergence legacy vs cell[N]

Le tableau « Résultats préliminaires » du README legacy (avant c.1285) présentait **3 paires « choisies »** :

| Legacy (avant c.1285) | Réel (cell[N]) | Verdict |
|-----------------------|----------------|---------|
| « EMA-Cross + All-Weather ~0.3 correlation, Sharpe combiné > 0.8 » | cell[34] row 6 : EMA-Cross-Tech / All-Weather corr=**0.277**, Sharpe=**1.128** | **OK** (arrondi ~0.3, > 0.8 vérifié) |
| « Dual-Momentum + Mean-Reversion ~0.1 correlation, Sharpe combiné > 0.7 » | cell[34] row 4 : Dual-Momentum / Mean-Reversion corr=**0.138**, Sharpe=**1.171** | **OK** (arrondi ~0.1, > 0.7 vérifié, mais ~0.1 = arrondi permissif de 0.138) |
| « Trend-Following + Mean-Reversion ~0.0 correlation, Sharpe combiné > 0.6 » | cell[22] : Trend-Following / Mean-Reversion corr=**0.463** (pas dans top-10 cell[24] ni cell[34]) | **❌ FABRIQUÉ** — corrélation 0.463, pas ~0.0 ; la paire n'apparaît dans aucun ranking top-10 |

**Cause** : le tableau « préliminaire » du README semble être une **synthèse manuelle round-numbered** sans back-citation vers cell[N]. La 3ᵉ ligne est particulièrement fausse : la corrélation réelle 0.463 est dans la **fourchette moyenne-haute** de la matrice (cf. cell[22] stream), pas « ~0.0 ». **PAS un signal de déploiement live** d'un composite Trend-Following + Mean-Reversion sur la foi de cette ligne.

**C.4 §D.5 verdict** : `CAUSE_DOCUMENTED_ONLY` — la divergence est **DOCUMENTÉE** par les outputs cell[N]. PAS un bug, PAS une régression de cellule code. Le **fix** : remplacer le tableau « préliminaire » synthétique par le **tableau cell[34] verbatim** + lecture honnête de la divergence. Aucun re-alignement cosmétique (refus §D.5 « main-align sur un nombre volatil sans re-exécution »).

**Diagnostic anti-régression** : `quantbook.ipynb` est intact (cell[22]/[24]/[28]/[30]/[32]/[34]/[36] inchangés, pas de cellule code touchée). Le fix est **markdown-only** (C.2 exception).

## Comment exécuter

**Localement** (mécanisme #8772 disclosed) :
```bash
jupyter nbconvert --execute "MyIA.AI.Notebooks/QuantConnect/projects/Alpha-Correlation-Analysis/quantbook.ipynb" \
  --to notebook --inplace --ExecutePreprocessor.timeout=600
```
**Attendu** : `Local environment detected - yfinance will be used for data` (cell[1]), puis 18 tickers yfinance 2021-06-01 → aujourd'hui, cellule[22]/[28]/[34]/[36] outputs identiques (± variations yfinance Daily updates).

**QC Cloud** (authentique) : non testé — `QuantBook()` lève `NameError` dans l'environnement qui a produit les outputs committés (cell[2] disclose explicite). Pour la fenêtre déclarée `2020-01-01 → 2024-12-31` du cell[1], **ré-exécuter via QC Cloud** une fois l'environnement restauré.

**Note sur Docker Lean** : `lean research` avec ce dossier utilise `QuantBook()` par défaut ; attendre les mêmes `NameError` + branche yfinance. Si le docker Lean est restauré, `lean research "MyIA.AI.Notebooks/QuantConnect/projects/Alpha-Correlation-Analysis"` doit fonctionner avec la fenêtre déclarée 2020-2024.

## Fichiers

- `quantbook.ipynb` — 38 cellules (37 code + 1 markdown d'origine). **Source unique de vérité** pour les chiffres. Outputs cell[22]/[28]/[34]/[36] préservés. Disclaimer #8772 en cell[2].
- `README.md` (ce fichier) — Vue d'ensemble + multi-source + lecture honnête (c.1285 fix).

## Références

- Issue [#140 - Complementary Alpha Combinations](https://github.com/jsboige/CoursIA/issues/140) (CLOSED, scope delivered).
- Mécanisme #8772 (disclosed fallback `yfinance` quand `QuantBook()` indisponible, cf `quantbook.ipynb:cell[2]`).
- Cell[22] (correlation matrix 7×7), cell[24] (top-10 least correlated pairs), cell[28] (Sharpe par régime), cell[30] (top-10 complementary pairs), cell[32] (top-3 detailed analysis), cell[34] (final recommendations), cell[36] (walk-forward OOS).
- c.1279 arche (DualMomentum README stale 0.350→3 sources, #9511/#9530) — pattern sœur « chiffre stale → tableau multi-source cité ».
- #1621 (drainage epic — prose réelle mesurée vs stale dans le repo).
- #9434 (drainage umbrella — multi-PR cleanup des README stale).