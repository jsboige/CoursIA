# Stoploss-Volatility-ML (HandsOn Ex08)

**Asset class:** US Equities (KO)
**Cloud project ID:** 29463529

## Description

Lasso regression stop-loss volatility prediction. Predicts next-day realized volatility. Adjusts stop-loss dynamically based on predicted vol.

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Stoploss-Volatility-ML"`
**QC Cloud:** Project 29463529. Research notebook executed on QC Cloud (2026-05-11).

## Backtest Metrics

| Metric | Value |
|--------|-------|
| Sharpe Ratio | 0.291 |
| CAGR | 7.83% |
| Max Drawdown | 20.0% |
| Model | Lasso |
| Universe | KO (Coca-Cola) |
| Rebalance | Daily |

## Mode référence 06/08/01 (`mode=fixed`, #18960)

Le paramètre `mode` (`'ml'` par défaut, inchangé) ajoute la variante de
référence du livre : achat 100 % KO à l'entrée hebdomadaire, puis stop
market à `round(prix × stop_loss_percent, 2)`. Au paramètre publié (0,95),
dans les conditions du livre (2018-12-31 → 2024-04-01, 100 k, frais IBKR,
édition de déploiement du projet cloud) : **Sharpe 0,266** — le buy-and-hold
KO du livre publie 0,263 — CAGR 7,57 %, pire baisse 22,5 %, 809 ordres,
PSR 2,0 % (backtest `a7433eb7aad818f0ffb53d4588c19361`). Écart assumé et
écrit : liquidation de fin de semaine conservée (le benchmark du livre
liquide à l'ouverture suivante) pour isoler le stop dans la comparaison à
trois. Détail et verdict : `BOOK_MAPPING.md` ligne 08/01.

## Files

- main.py - Strategy (v1.0, ML vol-adjusted stops)
- research.ipynb - QC Cloud executed (2026-05-11, project 29463529). LASSO: rolling vol features 30/60/90d, weekly low return prediction, fixed vs ML stop-loss comparison, drawdown recovery, sensitivity 2-14%. Outputs captured via QC Cloud Research IDE.

## References

- Hands-On AI Trading, Section 06, Example 08
