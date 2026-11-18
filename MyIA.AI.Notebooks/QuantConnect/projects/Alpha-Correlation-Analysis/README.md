# Alpha Correlation Analysis

**Type :** Recherche (notebook analytique, sans algorithme de trading)
**Environnement :** yfinance local (cell[1] `Local environment detected`, mécanisme #8772 disclosed) — `QuantBook()` lève `NameError` (QC Cloud / Lean indisponible), branche de repli `yfinance` activée explicitement
**Période effective :** 2020-01-02 → 2024-12-31, figée sur la période déclarée en cell[1] (plage imprimée par cell[6])

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

1. **Return Stream Collection** : prix de clôture ajustés `yfinance` sur la fenêtre figée 2020-2024, puis séries de rendements journaliers des alphas (cell[6] + cell[20])
2. **Correlation Matrix** : matrice des corrélations entre rendements d'alphas (cell[22])
3. **Regime Analysis** : classification en régimes (Bull/Bear/Sideways × High/Med/Low-Vol) puis Sharpe par régime (cell[26]-[28])
4. **Complementarity Score** : classement des paires par score combiné (corrélation inverse × diversification de régime × protection en baisse, cell[30])
5. **Top Pairs Analysis** : analyse détaillée des trois paires de tête (cell[32])
6. **Walk-Forward Validation** : fenêtres trimestrielles glissantes, entraînement sur 252 séances puis test sur les 63 suivantes (cell[36]) — paire de tête **Average Test Sharpe 0.55**

## La fenêtre est figée (#21836)

Le repli `yfinance` demandait auparavant `period="5y"`, soit les cinq dernières années comptées depuis l'heure d'exécution. Chaque ré-exécution déplaçait la fenêtre, et les chiffres de ce README avec elle : la version précédente citait une fenêtre 2021-06-01 → 2026-05-29.

La cellule de chargement passe désormais les mêmes bornes aux deux chemins : `qb.History(symbole, début, fin)` côté `QuantBook`, `history(start=..., end=...)` côté `yfinance`. Deux exécutions successives ne diffèrent qu'au-delà de la troisième décimale, et les tableaux ci-dessous restent identiques une fois arrondis.

## Résultats vérifiés (cell[N] cités)

### Paires complémentaires (cell[34] verbatim)

Classement par score total de complémentarité (cell[30]).

| # | Paire | Corrélation | Sharpe α₁ | Sharpe α₂ | **Sharpe combiné (50/50)** | Synergy | Regime_Div | DD_Protection |
|---|-------|-------------|-----------|-----------|----------------------------|---------|------------|---------------|
| 1 | EMA-Cross-Tech / Mean-Reversion | **0.152** | 1.015 | 0.796 | **1.153** | 0.247 | 1.433 | 0.702 |
| 2 | EMA-Cross-SPY / Mean-Reversion | **0.128** | 0.855 | 0.796 | **1.071** | 0.245 | 0.828 | 0.436 |
| 3 | **Momentum-SPY / Mean-Reversion** | **0.082** | 1.249 | 0.796 | **1.429** ⭐ | 0.407 | 1.452 | 0.000 |
| 4 | Dual-Momentum / Mean-Reversion | **0.283** | 0.574 | 0.796 | **0.735** | 0.050 | 1.056 | 0.341 |
| 5 | EMA-Cross-Tech / All-Weather | **0.368** | 1.015 | 0.517 | **1.001** | 0.235 | 1.572 | 0.064 |
| 6 | Momentum-SPY / All-Weather | **0.400** | 1.249 | 0.517 | **1.065** | 0.182 | 1.446 | 0.000 |
| 7 | Mean-Reversion / All-Weather | **0.152** | 0.796 | 0.517 | **0.799** | 0.143 | 0.727 | 0.000 |
| 8 | EMA-Cross-Tech / Dual-Momentum | **0.434** | 1.015 | 0.574 | **0.951** | 0.157 | 1.210 | 0.000 |
| 9 | EMA-Cross-SPY / Dual-Momentum | **0.450** | 0.855 | 0.574 | **0.795** | 0.081 | 1.013 | 0.000 |
| 10 | EMA-Cross-SPY / All-Weather | **0.428** | 0.855 | 0.517 | **0.825** | 0.139 | 0.843 | 0.183 |

`Synergy` = Sharpe combiné moins la moyenne des deux Sharpes individuels ; elle est positive pour toutes les paires du tableau.

⭐ **Meilleur Sharpe combiné** : Momentum-SPY / Mean-Reversion (1.429), qui est aussi la paire la moins corrélée (0.082). Elle n'arrive pourtant que troisième au score total, parce que sa protection en baisse est nulle (`DD_Protection` 0.000). La paire de tête, EMA-Cross-Tech / Mean-Reversion, doit sa place à cette composante (0.702).

Les trois premières paires partagent la même jambe Mean-Reversion : le classement désigne d'abord un diversificateur, plus qu'une paire.

### Détail des trois paires de tête (cell[32] verbatim)

| Paire | Rendement combiné (ann.) | Volatilité | Sharpe combiné | Corrélation |
|-------|--------------------------|------------|----------------|-------------|
| EMA-Cross-Tech / Mean-Reversion | 13.93 % | 12.09 % | 1.15 | 0.152 |
| EMA-Cross-SPY / Mean-Reversion | 8.11 % | 7.57 % | 1.07 | 0.128 |
| Momentum-SPY / Mean-Reversion | 9.93 % | 6.95 % | 1.43 | 0.082 |

### Sharpe par régime (cell[28] verbatim)

| Alpha | Bear-High-Vol | Bear-Med-Vol | Bull-High-Vol | Bull-Low-Vol | Bull-Med-Vol | Sideways-High-Vol | Sideways-Low-Vol | Sideways-Med-Vol |
|-------|---------------|--------------|---------------|--------------|--------------|-------------------|------------------|------------------|
| All-Weather | 2.05 | 4.79 | 2.59 | -0.45 | 0.94 | -1.59 | 0.19 | 0.61 |
| Dual-Momentum | 0.52 | 0.32 | 1.61 | 0.20 | 2.25 | 0.75 | 0.41 | 1.47 |
| EMA-Cross-SPY | 0.00 | 0.00 | 1.95 | 0.76 | 1.10 | 2.57 | 1.27 | 0.13 |
| EMA-Cross-Tech | 1.29 | -4.91 | 1.96 | 1.49 | 0.21 | -0.52 | 1.96 | 1.90 |
| Mean-Reversion | 2.74 | 2.49 | 0.00 | -0.35 | 0.92 | 0.38 | 0.17 | -0.12 |
| Momentum-SPY | 0.52 | -4.40 | 1.90 | 0.76 | 1.42 | 2.14 | 1.02 | 1.56 |
| Trend-Following | 2.22 | 2.10 | 1.75 | 0.76 | 1.46 | 0.38 | 1.18 | 1.07 |

La colonne Bear-Med-Vol repose sur très peu de séances (cell[26]) : ses Sharpes extrêmes (4.79, -4.91) ne se lisent pas comme des mesures. Ce qui se lit : Mean-Reversion et All-Weather tiennent en régime Bear-High-Vol, où les alphas de tendance sur SPY sont à plat ou faibles, et c'est ce qui fait leur valeur de diversificateurs.

### Walk-forward — paire de tête (cell[36] verbatim)

Paire : **EMA-Cross-Tech / Mean-Reversion** (meilleur score total, cell[30]). La période va du début de l'entraînement à la fin du test ; `Test_Return` est la moyenne journalière du test, annualisée (×252), pas le rendement du trimestre.

| Période | Train_Corr | Test_Return (ann.) | Test_Sharpe |
|---------|-----------|--------------------|-------------|
| 2020-01-02 → 2021-04-01 | 0.196 | -1.6 % | -0.13 |
| 2020-04-02 → 2021-07-01 | 0.071 | +31.6 % | +3.31 |
| 2020-07-02 → 2021-09-30 | 0.082 | +9.3 % | +1.04 |
| 2020-10-01 → 2021-12-30 | 0.130 | +35.5 % | +2.75 |
| 2020-12-31 → 2022-03-31 | 0.121 | -19.4 % | -2.84 |
| 2021-04-05 → 2022-07-01 | 0.080 | -8.1 % | -1.14 |
| 2021-07-02 → 2022-09-30 | 0.059 | -30.9 % | -3.30 |
| 2021-10-01 → 2022-12-30 | 0.034 | -1.4 % | -1.65 |
| 2021-12-31 → 2023-04-03 | 0.012 | +24.7 % | +2.00 |
| 2022-04-01 → 2023-07-05 | 0.010 | +47.0 % | +3.95 |
| 2022-07-05 → 2023-10-03 | 0.022 | -2.3 % | -0.21 |
| 2022-10-03 → 2024-01-03 | 0.031 | -11.5 % | -1.35 |
| 2023-01-03 → 2024-04-04 | 0.017 | +44.2 % | +4.15 |
| 2023-04-04 → 2024-07-05 | 0.022 | +43.1 % | +3.96 |
| 2023-07-06 → 2024-10-03 | 0.141 | -28.0 % | -2.31 |
| **Moyenne** | — | — | **+0.55** |

**Lecture honnête.** La moyenne de 0.55 cache une dispersion très forte, de -3.30 à +4.15 : la paire alterne trimestres très positifs et très négatifs, au rythme des régimes (reprise 2020-2021, baisse 2022, hausse 2023). La corrélation d'entraînement reste basse sur toute la période, ce qui est le résultat recherché ; la performance, elle, n'est pas stable.

Deux limites de méthode :
- la paire testée est choisie sur la fenêtre entière (cell[30]), fenêtres de test comprises. Ces fenêtres ne sont donc pas hors échantillon pour le choix de la paire, et la moyenne est optimiste ;
- le test porte sur une seule fenêtre de cinq ans. Retenir la paire pour un composite demanderait de refaire la sélection à chaque pas du walk-forward, sur plusieurs cycles de marché.

## Divergence avec le tableau « Résultats préliminaires » d'origine

Le README d'origine (avant c.1285) présentait **trois paires choisies à la main**, sans renvoi aux sorties du carnet. Confrontées à la fenêtre figée :

| Ligne d'origine | Mesure (cell[N]) | Verdict |
|-----------------|------------------|---------|
| « EMA-Cross + All-Weather ~0.3 correlation, Sharpe combiné > 0.8 » | cell[34] rang 5 : EMA-Cross-Tech / All-Weather, corrélation **0.368**, Sharpe combiné **1.001** | Sharpe > 0.8 vérifié ; corrélation plus proche de 0.4 que de 0.3 |
| « Dual-Momentum + Mean-Reversion ~0.1 correlation, Sharpe combiné > 0.7 » | cell[34] rang 4 : corrélation **0.283**, Sharpe combiné **0.735** | **Corrélation fausse** (≈ 0.3) ; Sharpe > 0.7 tout juste |
| « Trend-Following + Mean-Reversion ~0.0 correlation, Sharpe combiné > 0.6 » | cell[22] : corrélation **0.194** ; cinquième paire la moins corrélée (cell[24]), absente du classement de complémentarité (cell[30], cell[34]) | **Faux** : 0.194, pas ~0.0 |

Aucune des trois lignes ne désigne la paire de tête du classement. Les chiffres de ce README viennent tous des sorties du carnet, cellule citée.

## Comment exécuter

**Localement** (mécanisme #8772 disclosed) :
```bash
jupyter nbconvert --execute "MyIA.AI.Notebooks/QuantConnect/projects/Alpha-Correlation-Analysis/quantbook.ipynb" \
  --to notebook --inplace --ExecutePreprocessor.timeout=600
```
**Attendu** : `Local environment detected - yfinance will be used for data` (cell[1]), puis la plage 2020-01-02 → 2024-12-31 en cell[6], et des tableaux identiques à ceux de ce README une fois arrondis.

**QC Cloud** (authentique) : non testé — `QuantBook()` lève `NameError` dans l'environnement qui a produit les sorties committées (cell[2]). Le chemin `QuantBook` demande la même fenêtre que le repli ; la ré-exécution via QC Cloud reste à faire pour obtenir des sorties `QuantBook` authentiques.

**Note sur Docker Lean** : `lean research` avec ce dossier utilise `QuantBook()`. Si les données equity locales s'arrêtent avant la fin de 2024 (#8734), Lean prolonge la dernière barre en constante (`fillDataForward=True`, artefact de ligne plate de #8719) : vérifier la plage imprimée par cell[6] avant de lire les chiffres.

## Fichiers

- `quantbook.ipynb` — **Source unique de vérité** pour les chiffres. Note d'environnement #8772 et fenêtre figée en cell[2].
- `README.md` (ce fichier) — Vue d'ensemble + chiffres cités par cellule.

## Références

- Issue [#140 - Complementary Alpha Combinations](https://github.com/jsboige/CoursIA/issues/140) (CLOSED, scope delivered).
- Mécanisme #8772 (disclosed fallback `yfinance` quand `QuantBook()` indisponible, cf `quantbook.ipynb:cell[2]`).
- #21836 (carnets QC à fenêtre glissante : figer, déclarer ou classer faux positif).
- Cell[22] (matrice de corrélation), cell[24] (paires les moins corrélées), cell[28] (Sharpe par régime), cell[30] (paires les plus complémentaires), cell[32] (détail des trois paires de tête), cell[34] (recommandations finales), cell[36] (walk-forward).
- c.1279 arche (DualMomentum README stale 0.350→3 sources, #9511/#9530) — pattern sœur « chiffre stale → tableau multi-source cité ».
- #1621 (drainage epic — prose réelle mesurée vs stale dans le repo).
