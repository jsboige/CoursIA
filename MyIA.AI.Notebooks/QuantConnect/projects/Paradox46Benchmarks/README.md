# Paradox46Benchmarks

**ID projet Cloud :** 37331102 (créé 2026-10-04)

## Description

Benchmarks de comparaison pour l'évaluation de la stratégie 46 (issue #18906,
point 4) : **SPY détenu** (buy & hold) et **60/40** (SPY 60 % / IEF 40 %,
rebalancé mensuellement), même fenêtre 2018-01-01 → 2026-09-25, même modèle de
frais IBKR que la stratégie évaluée (`InteractiveBrokersFeeModel`, identité à
`fee_mult = 1`).

Un seul projet, mode par paramètre de backtest : `mode = "spy"` (défaut) ou
`mode = "6040"`.

## Résultats

> Runs QC Cloud du 2026-10-04, frais IBKR identiques à la stratégie évaluée
> (`fee_mult = 1`), fenêtre 2018-01-01 → 2026-09-25 (2 195 dates).

| Benchmark | Sharpe | CAGR | Pire baisse | Profit net | Orders | ID run |
|---|---:|---:|---:|---:|---:|---|
| SPY détenu (buy & hold) | 0,499 | 13,907 % | 33,600 % | 212,007 % | 1 | `3f8ffd4c12fb0e621eb29feac8dd194a` |
| 60/40 (SPY 60 % / IEF 40 %, mensuel) | 0,383 | 8,858 % | 21,200 % | 109,950 % | 173 | `54418ac625203c9cad5f7e8afade7578` |

## Comment exécuter

**QC Cloud :** projet 37331102, lancer un backtest avec `mode` = `spy` ou
`6040` (fenêtre par paramètres `start_date` / `end_date`).

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Paradox46Benchmarks"`
(mode SPY par défaut).

## Fichiers

- `main.py` — les deux benchmarks (mode par paramètre)
- `config.json` — identifiants Cloud

## Voir aussi

- `Paradox46VolScaledMomentum/` — la stratégie évaluée
- Issue #18906
