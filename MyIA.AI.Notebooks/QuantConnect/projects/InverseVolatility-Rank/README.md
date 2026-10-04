# InverseVolatility-Rank (HandsOn Ex11)

**Asset class:** Futures (12 contracts)
**Cloud project ID:** 37313767 (version dépôt, mesurée 2026-10-03) · 29463533 (version code Cloud, voir avertissement ci-dessous)

## Description

Ridge regression inverse volatility ranking on 12 futures contracts. Predicts next-week volatility (6 trading days) and allocates inversely.

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/InverseVolatility-Rank"`
**QC Cloud:** Project 37313767 (« HandsOn-Ex11-InverseVolatility-Rank-repo ») = copie exacte du `main.py` du dépôt.

## Backtest Metrics

> **Deux versions, deux fenêtres (#19018).** Le projet Cloud historique 29463533 ne contient pas le `main.py` du dépôt : il démarre 2018-12-31 et n'a pas de brokerage model. Les chiffres Sharpe 0.124 / CAGR 4.13 % / MaxDD 41.0 % publiés auparavant décrivent ce code Cloud, pas le fichier commité ici. La version du dépôt (ci-dessous) a été mesurée séparément sur un projet Cloud dédié. Lecture honnête : PSR 3.34 % — l'edge reste statistiquement non significative sur les deux fenêtres ; l'écart de Sharpe (0.529 vs 0.124) vient de la fenêtre (2015-2018 inclus) et du brokerage IBKR, pas d'un changement de signal.

| Metric | Value |
|--------|-------|
| Sharpe Ratio (version dépôt) | 0.529 |
| CAGR (version dépôt) | 14.86 % |
| Max Drawdown (version dépôt) | 40.5 % |
| Probabilistic Sharpe (version dépôt) | 3.34 % |
| Fenêtre mesurée (version dépôt) | 2015-01-01 → 2024-04-01 (2865 j. tradeables), IBKR MARGIN, projet Cloud 37313767 |
| Sharpe Ratio (code Cloud 29463533) | 0.124 (fenêtre Cloud 2018-12-31 → 2024-04-01, sans brokerage, même cash 100 M$) — pour référence |
| Model | Ridge |
| Universe | 12 futures contracts |
| Rebalance | Weekly (`date_rules.week_start`) |
| Leverage | `weight_multiplier` 2.0, cap `max_position_pct` 15 % |

## Files

- main.py - Strategy (v1.0, inverse vol futures) — la source mesurée ci-dessus
- research.ipynb - **awaiting QC Cloud execution** (project 29463533). Research node unavailable on 2026-05-11 ("No spare research nodes"). Ridge regression: 12 futures indices/energy/grains, vol features 60/90/180d, inverse-vol allocation vs equal-weight, lookback sensitivity.

## References

- Hands-On AI Trading, Section 06, Example 11
