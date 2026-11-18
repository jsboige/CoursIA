# ThreeZone781Benchmarks

Benchmarks de comparaison pour l'évaluation de la stratégie 781 (issue
[jsboige/CoursIA#18905](https://github.com/jsboige/CoursIA/issues/18905),
point 3 du protocole). Projet compagnon de
[`ThreeZoneSPYDrawdownRotation`](../ThreeZoneSPYDrawdownRotation/).

## Modes (paramètre de backtest `mode`)

| Mode | Allocation | Rebalancement |
|------|------------|---------------|
| `spy` | 100 % SPY détenu | mensuel (idempotent) |
| `6040` | 60 % SPY / 40 % IEF | mensuel |

Même fenêtre (2018-01-01 → 2026-09-25) et même modèle de frais
(Interactive Brokers) que la stratégie évaluée, pour une comparaison
ceteris paribus.

## Résultats

| Run | Sharpe | CAGR | Pire baisse | Total |
|-----|--------|------|-------------|-------|
| bench-spy-2018-2026 (`43fa2e07`) | 0,499 | 13,91 % | 33,6 % | +212 % |
| bench-6040-2018-2026 (`d4a2b089`) | 0,383 | 8,86 % | 21,2 % | +110 % |

Rappel : la 781 réimplémentée rend 0,404 / 9,22 % / 16,4 % sur la même
fenêtre — elle domine le 60/40 sur les trois axes.

Table remplie à mesure des runs (protocole en cours).
