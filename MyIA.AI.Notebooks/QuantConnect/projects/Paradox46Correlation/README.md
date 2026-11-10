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

Deux corrections successives, chacune suivie d'une nouvelle mesure. Les
mesures antérieures restent publiées, séparées, comme mesures historiques ;
les conclusions ne portent que sur la v3.

- **v2 (#19082)** : ce projet mesurait les paniers ombres en poids×prix
  (portefeuille à nombres de titres pondérés, pas à allocations de capital :
  50/50 sur 100/10 → 100/20 donne +9,09 % au lieu de +50 %) avec une base
  début-de-mois (rendements cumulés intra-mois, effacés au franchissement de
  mois), et sa jambe stratégie portait les mêmes défauts de fenêtres et de
  sens des rendements que le projet principal. Corrigé au commit `1d3584d8` :
  quantités fixées aux prix de rebalance (allocation de capital), rendements
  hebdo chainés vendredi-à-vendredi comme la jambe P46.
- **v3 (#20388)** : la rotation de la jambe P46 achetait la nouvelle cible
  par `set_holdings(cible, 1.0)` sans vendre la ligne précédente. Sur le
  compte marge par défaut (levier 2), jusqu'à trois lignes étaient détenues à
  la fois, 178 achats étaient refusés faute de marge et 36 ordres d'appel de
  marge vendaient à leur place : la jambe dont on mesurait la corrélation
  n'était pas la stratégie 46. La rotation vend désormais d'abord et vise
  98 % (même correctif que `Paradox46VolScaledMomentum`).

### Recalcul v3 (rotation corrigée, QC Cloud, 2026-10-15)

> Run `00505ff942dd9248f21b216d95328575` (nœud de backtest QC Cloud, projet
> 37847852, mode `unlevered`, fenêtre 2018-01-01 → 2024-12-31, 731 ordres,
> Sharpe 0,455, CAGR 11,678 %, pire baisse 19,700 %) — une seule ligne
> détenue à chaque clôture, 0 ordre refusé, 0 appel de marge. Valeurs lues
> dans la ligne `CORRELATIONS {...}` du log du run.

**Période pleine 2018-2024** :

| Panier | Corrélation hebdo avec la stratégie 46 sans levier |
|---|---:|
| VT2 | **0,324** |
| AW | 0,256 |
| TW | 0,256 |

Par année civile (VT2 / AW=TW) :

| Année | VT2 | AW/TW |
|---|---:|---:|
| 2018 | 0,652 | 0,628 |
| 2019 | 0,185 | −0,013 |
| 2020 | 0,266 | 0,201 |
| 2021 | 0,233 | 0,138 |
| 2022 | 0,220 | 0,209 |
| 2023 | 0,533 | 0,476 |
| 2024 | 0,389 | 0,327 |

Lecture v3 : la décorrélation tient (0,26-0,32 sur la période pleine, contre
0,23-0,31 en v2), elle bouge à peine avec la rotation. Ce qui change, c'est
la jambe stratégie elle-même : Sharpe 0,455 contre 0,124 en v2, pire baisse
19,7 % contre 45,3 %. Le potentiel de diversification est donc porté par un
moteur nettement plus solide que ce que la v2 laissait croire — le verdict
de la stratégie elle-même vit dans `Paradox46VolScaledMomentum/`.

### Mesures historiques — code v2 (rotation fautive, #20388, remplacées)

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

Lecture v2 (rotation fautive) : la correction **renforce** la décorrélation (0,23-0.31 sur la
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
