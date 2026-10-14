# Paradox46Correlation

**ID projet Cloud :** 37331103 (créé 2026-10-04)

## Description

Corrélations hebdomadaires entre la stratégie 46 **sans levier**
(réimplémentation déclarée, identique à `Paradox46VolScaledMomentum` en mode
`unlevered`) et les allocations ETF du dépôt, sur la fenêtre commune
2018-01-01 → 2024-12-31 (issue #18906, point 4).

Paniers ombre suivis en portefeuille rebalancé mensuellement (poids cibles du
dépôt) :

| Panier | Poids | Provenance |
|---|---|---|
| VT2 | SPY/QQQ/IEF/GLD 25 % chacun | proxy déclaré de la variante 2 (ERC) de `Cloud-VolTargeting` |
| AW | SPY 0.30 / IEF 0.30 / GLD 0.30 / XLP 0.10 | `AllWeather` v5.0 |
| TW | SPY 0.30 / IEF 0.30 / GLD 0.30 / XLP 0.10 | sleeve AllWeather de `Framework_Composite_TrendWeather` (la jambe 75 % stock-picking n'est PAS répliquée — déclaré) |

Retours hebdomadaires échantillonnés le vendredi ; corrélations de Pearson
in fine sur la période pleine et par année civile. Sorties : ligne
`CORRELATIONS {...}` dans le log + `paradox46_correlations.json` dans
l'ObjectStore du run.

## Résultats

> **Recalcul en cours (code v2).** La review adjointe de PR #19082 a relevé
> que ce projet mesurait les paniers ombres en poids×prix (portefeuille à
> nombres de titres pondérés, pas à allocations de capital : 50/50 sur
> 100/10 → 100/20 donne +9,09 % au lieu de +50 %) avec une base
> début-de-mois (rendements cumulés intra-mois, effacés au franchissement de
> mois), et que sa jambe stratégie portait les mêmes défauts de fenêtres et
> de sens des rendements que le projet principal. Corrigé au commit
> `1d3584d8` : quantités fixées aux prix de rebalance (allocation de
> capital), rendements hebdo chainés vendredi-à-vendredi comme la jambe P46.
> Les valeurs ci-dessous restent publiées comme **mesures historiques du
> code v1, explicitement séparées**, remplacées par le run v2 relancé le
> 2026-10-04.

### Recalcul v2 (code corrigé, QC Cloud, 2026-10-04)

> Run `5bc6e8102a95a81881333994489580f2` (mode `unlevered`, fenêtre
> 2018-01-01 → 2024-12-31, 1 761 dates, 433 ordres, Sharpe 0,124) — valeurs
> lues dans la ligne `CORRELATIONS {...}` du log du run.

**Période pleine 2018-2024** :

| Panier | Corrélation hebdo avec la stratégie 46 sans levier |
|---|---:|
| VT2 | **0,305** |
| AW | 0,229 |
| TW | 0,229 |

Par année civile (VT2 / AW=TW) :

| Année | VT2 | AW/TW |
|---|---:|---:|
| 2018 | 0,615 | 0,536 |
| 2019 | **−0,010** | −0,198 |
| 2020 | 0,227 | 0,135 |
| 2021 | 0,209 | 0,173 |
| 2022 | 0,307 | 0,293 |
| 2023 | 0,324 | 0,246 |
| 2024 | 0,530 | 0,452 |

Lecture v2 : la correction **renforce** la décorrélation (0,23-0.31 sur la
période pleine contre 0.34-0.38 en v1 ; 2019 bascule négatif) — le noyau
momentum corrigé décorelle encore plus des paniers statiques. Mais la jambe
stratégie elle-même s'affaiblit fortement (Sharpe 0,124 contre 0,463 en v1) :
le potentiel de diversification existe toujours, porté par un moteur au
rendement corrigé plus faible — voir le verdict de
`Paradox46VolScaledMomentum/`.

### Mesures historiques — code v1 (avant correction #19082, remplacées)

> Run QC Cloud `3632c4a5f4ea219e3714cd27d32012d6` (2026-10-04, mode `unlevered`,
> fenêtre 2018-01-01 → 2024-12-31, 1 761 dates, 305 ordres, Sharpe 0,463,
> code v1) — valeurs lues dans le log du run (ligne `CORRELATIONS {...}`) et
> dans `paradox46_correlations.json` (ObjectStore).

**Période pleine 2018-2024** :

| Panier | Corrélation hebdo avec la stratégie 46 sans levier |
|---|---:|
| VT2 | **0,381** |
| AW | 0,339 |
| TW | 0,339 |

Par année civile (VT2 / AW=TW) :

| Année | VT2 | AW/TW |
|---|---:|---:|
| 2018 | 0,535 | 0,513 |
| 2019 | 0,288 | 0,169 |
| 2020 | 0,336 | 0,298 |
| 2021 | 0,395 | 0,352 |
| 2022 | 0,251 | 0,260 |
| 2023 | 0,459 | 0,394 |
| 2024 | 0,494 | 0,438 |

Lecture (code v1, provisoire) : contrairement à la stratégie 781 évaluée juste avant (corrélations
0,74-0,80, voir `ThreeZone781Correlation/`), le noyau 1x de la stratégie 46
est **peu corrélé** aux allocations du dépôt (0,34-0,38 sur la période pleine,
jamais > 0,54 par année) : la rotation sectorielle momentum quotidienne avec
passage en liquidités décorrèle naturellement des paniers statiques
actions/obligations/or. **Le potentiel de diversification est réel** — c'est
le risque (pire baisse 28,3 %) qui lui manque pour trancher en sa faveur.

## Comment exécuter

**QC Cloud :** projet 37331103, lancer le backtest (paramètres par défaut =
mode `unlevered`, fenêtre commune 2018-2024).

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Paradox46Correlation"`.

## Fichiers

- `main.py` — la jambe stratégie 46 + les paniers ombre et le calcul
- `config.json` — identifiants Cloud

## Voir aussi

- `Paradox46VolScaledMomentum/` — la stratégie évaluée
- Issue #18906
