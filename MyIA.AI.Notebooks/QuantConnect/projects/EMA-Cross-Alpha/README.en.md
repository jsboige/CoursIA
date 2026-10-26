# EMA-Cross-Alpha

**Asset class:** US Equities (Large-cap tech)
**Cloud project ID:** 28885488

## Description

Framework-based EMA crossover alpha strategy on 5 major tech stocks (AAPL, MSFT, GOOGL, AMZN, NVDA).
Uses the QuantConnect Alpha Model framework with `EMACrossAlpha` (fast=20, slow=50) and daily portfolio rebalance via `MultiStrategyPCM`.

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

## Files

- `main.py` - Strategy entry point (framework alpha model)
- `alpha_models.py` - EMACrossAlpha implementation
- `SharedPCM/pouches_pcm.py` (bibliothèque de projet QC) — `MultiStrategyPouchesPCM`, PCM par poches canonique importé par `main.py` (extraction #19821 brique 1, tranche dedup)
- `quantbook.ipynb` - Research notebook

## References

- QC Framework: Alpha Model + Portfolio Construction pattern
- Ref: Brock et al. (1992), moving average trading rules
