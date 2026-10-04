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

| Run | Sharpe | CAGR | Pire baisse |
|-----|--------|------|-------------|
| bench-spy-2018-2026 (`43fa2e07`) | à venir | | |
| bench-6040-2018-2026 | à venir | | |

Table remplie à mesure des runs (protocole en cours).
