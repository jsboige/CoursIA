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

> Run QC Cloud `3632c4a5f4ea219e3714cd27d32012d6` (2026-10-04, mode `unlevered`,
> fenêtre 2018-01-01 → 2024-12-31, 1 761 dates, 305 ordres, Sharpe 0,463) —
> valeurs lues dans le log du run (ligne `CORRELATIONS {...}`) et dans
> `paradox46_correlations.json` (ObjectStore).

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

Lecture : contrairement à la stratégie 781 évaluée juste avant (corrélations
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
