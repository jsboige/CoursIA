# EMA-Cross-Alpha

**Asset class:** US Equities (Large-cap tech)
**Cloud project ID:** 28885488

## Description

Framework-based EMA crossover alpha strategy on 5 major tech stocks (AAPL, MSFT, GOOGL, AMZN, NVDA).
Uses the QuantConnect Alpha Model framework with `EMACrossAlpha` (fast=20, slow=50) and daily portfolio rebalance via `MultiStrategyPouchesPCM`.

Chaque jour, le modèle alpha émet pour chaque action un insight UP valable un jour de bourse tant que l'EMA rapide reste au-dessus de l'EMA lente, et un insight FLAT sinon. La ligne est donc détenue pendant toute la durée de la tendance, pas seulement le jour du croisement. Le module de construction de portefeuille répartit le capital entre les actions en tendance.

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/EMA-Cross-Alpha"`
```bash
lean backtest --project .
```

**QC Cloud :** créer un projet, y copier `main.py` et `alpha_models.py`, attacher le projet `SharedPCM` en bibliothèque (geste « Add Library », cf. README de `SharedPCM`), puis lancer le backtest. Le projet cloud 28885488 porte un autre code que celui du dépôt ([#22654](https://github.com/jsboige/CoursIA/issues/22654)) : ses résultats ne décrivent pas cette version.

## Backtest Metrics (2015-2024)

Mesure du 2026-10-26 sur le code du dépôt, avec deux contrôles de même fenêtre, même capital et mêmes frais. Protocole, identifiants de backtest et lecture : voir [README.md](README.md).

| Métrique | Stratégie | Mêmes titres, détention passive | SPY |
|----------|-----------|---------------------------------|-----|
| Sharpe (QC) | 1,12 | 1,134 | 0,536 |
| CAGR | 35,7 % | 37,3 % | 13,0 % |
| Pire baisse | 37,4 % | 41,7 % | 33,7 % |
| Ordres | 3812 | 500 | 2 |

> **Lecture honnête** : le Sharpe de la stratégie ne dépasse pas celui de la détention passive des mêmes titres. Le résultat vient du choix des titres, fait après coup, et le filtre EMA n'apporte rien de mesurable sur cette fenêtre. Les anciens chiffres de cette section (Sharpe -0,01, 314 ordres) venaient du projet cloud 28885488, dont le code diffère de celui du dépôt.

## Shared module non-regression (#20188)

Since #21140, `main.py` imports `MultiStrategyPouchesPCM` from `SharedPCM/pouches_pcm.py` instead of the local copy `portfolio_construction.py`. Two QC Cloud backtests run on 2026-10-26, with the default parameters and the window 2015-01-01 → 2024-12-31, check that this change alters no order:

- **A**: the `main` code at commit `54f9b9eec1`, with the shared module;
- **B**: the same `main.py` and `alpha_models.py`, with the old `portfolio_construction.py` copy taken at the commit before the migration (`fb3d05db0a^`). The project has a single pouch. The `additive=False` argument, which the old copy does not know, is removed from the call: the non-additive mode is the old copy's only behaviour.

A and B carry the same instrumentation, which places no order. It records the portfolio value every day at midnight, warm-up included (60 sessions). At the end of the backtest it computes a SHA-256 fingerprint per year of the orders (id, date, security, quantity, status, price) and of the recorded values.

| | A (shared module) | B (old copy) |
|---|---|---|
| Orders | 3,812 | 3,812 |
| Recorded values | 3,739 | 3,739 |
| Last recorded value | 2,145,082.06 | 2,145,082.06 |
| Sharpe (QC) | 1.12 | 1.12 |
| CAGR | 35.691% | 35.691% |
| Max drawdown | 37.4% | 37.4% |

The yearly fingerprints are equal: 10 of 10 for the orders, 11 of 11 for the values. The 27 QC statistics are equal, turnover included. The migration therefore does not change the project's behaviour. Traces kept outside the repository: `QC-traces/20188-nr/`.

These figures differ from those of the "Backtest Metrics" section above. That section measures the code of cloud project 28885488, which is not the repository code (checked on 2026-10-26); the re-measurement is tracked in #22654.

## Files

- `main.py` - Strategy entry point (framework alpha model)
- `alpha_models.py` - EMACrossAlpha implementation
- `SharedPCM/pouches_pcm.py` (QC project library) — `MultiStrategyPouchesPCM`, the canonical pouch PCM imported by `main.py` (extraction #19821 brick 1, dedup slice)
- `quantbook.ipynb` - Research notebook

## References

- QC Framework: Alpha Model + Portfolio Construction pattern
- Ref: Brock et al. (1992), moving average trading rules
