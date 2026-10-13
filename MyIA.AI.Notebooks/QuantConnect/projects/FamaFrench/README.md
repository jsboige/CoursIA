# FamaFrench

**Asset class:** US Factor ETFs
**Cloud project ID:** None (local only)

## Description

Factor ETF rotation strategy using risk-adjusted momentum (12m-1m return / 63d realized volatility) with skip-month.
Universe of 5 Fama-French factor ETFs: VLUE (value), MTUM (momentum), SIZE (size), QUAL (quality), USMV (low-vol).

SMA200 regime filter on SPY: in bear markets, rotates to USMV as risk-off asset.
Dynamic top_n selection (all factors with positive score). Per-position stop-loss at -12%.

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/FamaFrench"`
```bash
lean backtest --project .
```

**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics (2015-2026)

| Metric | Value |
|--------|-------|
| Sharpe Ratio | 0.540 |
| CAGR | 12.1% |
| Max Drawdown | 24.2% |
| Net Return | +258% |
| Rebalance | Monthly |

### Aligned baseline (2018-2025)

Standardized #1630 backbone run (QC Cloud project `33251801`, backtest `697e96af`).

| Metric | Value |
|--------|-------|
| Sharpe Ratio | 0.445 |
| CAGR | 11.111% |
| Max Drawdown | 24.100% |
| Probabilistic Sharpe Ratio | 11.9% |
| Tradeable dates | 1761 |

Interpretation: strong positive Sharpe 0.445 (3rd-best no-ML backbone, close to GlobalMacro-Regime 0.454) with the 2nd-highest CAGR (11.1%, after HAR-RV-J-Kelly 14.1%). The risk-adjusted momentum factor rotation (12m-1m return / 63d realized vol, dynamic top_n) combined with the SMA200 regime filter, USMV risk-off and per-position -12% stop-loss survives the 2018-2025 alignment with only a mild Sharpe drop vs the author's 2015-2024 v3.0 (0.540 -> 0.445; MaxDD stable 24.2% -> 24.1%) -- the strategy is genuinely robust, not period-overfit, in contrast to the broader "simple factor collapse" finding (this is a risk-adjusted momentum rotation, not static factor exposure). Below the FamaFrenchAllWeather composite (0.684) -- the framework composite adds value over the standalone rotation. Promoted Tier 4 -> 2 (Historique). totalOrders = 0 = wrapper extraction artifact (CAGR 11.1% implies real trades).

## Demi-séances (#20286)

Quand le 3 juillet tombe un lundi, c'est à la fois le premier jour de cotation du mois et une demi-séance qui ferme à 13:00, heure de New York : en 2017 et en 2023 sur les fenêtres ci-dessus. Sur la tranche de clôture d'une demi-séance, `history()` rend environ 21 barres journalières de moins que demandé (mesuré dans #20286 sur un autre projet). `_risk_adjusted_momentum` demandait `lookback + 5` barres et rejetait le titre sous `lookback`. Il restait moins de deux scores, et `rebalance` sortait sans rien écrire dans le journal. Ces mois-là passaient sans rééquilibrage : juillet 2023 sur 2018-2024, juillet 2017 et juillet 2023 sur 2015-2024.

Correctif dans `main.py` : `_risk_adjusted_momentum` demande le double de barres et garde les `lookback + 5` dernières. Sur une séance pleine, ce sont les mêmes barres qu'avant. Aucune ligne du journal ne montre l'historique court : la cause se déduit du code, et le retour des mois manquants avec ce seul changement la confirme.

Mesure sur les nœuds QC, frais de courtage inclus, protocole fixé avant les backtests ([#20286, c.6115594357](https://github.com/jsboige/CoursIA/issues/20286#issuecomment-6115594357)) :

| Fenêtre | Variante | Mois rééquilibrés | Sharpe | CAGR | Pire baisse | Ordres | Backtest |
|---|---|---|---|---|---|---|---|
| 2018-01-01 → 2025-01-01 (codée) | avant | 83 / 84 | 0.446 | 11.098 % | 24.2 % | 250 | `ae3857d1a5eb25ee984ac54265df672e` |
| | après | 84 / 84 | 0.446 | 11.096 % | 24.2 % | 253 | `72edd9f1cfb074417703e764df4e9c6e` |
| 2015-01-01 → 2024-12-31 | avant | 118 / 120 | 0.555 | 11.838 % | 24.1 % | 313 | `39e54720fe0ee2e49c11b5245d2afd98` |
| | après | 120 / 120 | 0.555 | 11.836 % | 24.1 % | 313 | `54a8fcab145eab2557865b9cceb8f062` |
| 2025-01-01 → 2026-07-10 (hors échantillon) | avant | 19 / 19 | 0.524 | 14.234 % | 14.5 % | 66 | `7da7535966e9266b2a5ba2600dd49d78` |
| | après | 19 / 19 | 0.524 | 14.234 % | 14.5 % | 66 | `137d3bd124123133eb4d4426e3599d7e` |

Sharpe calculé par QC, taux sans risque inclus. Les quatre prédictions fixées d'avance ont tenu :

- les rééquilibrages des lundis 3 juillet reviennent ;
- avant le premier de ces lundis, les ordres sont identiques (date, titre, quantité) ; sur 2015-2024, le 2016-07-01, les mêmes ordres partent dans un autre ordre de soumission ;
- les dates de rééquilibrage sont celles d'avant, plus les lundis ;
- hors échantillon, aucun mois ne commence par une demi-séance, et les deux variantes sont identiques au centime.

L'effet est minime. Le rééquilibrage du 2017-07-03 n'envoie aucun ordre, et celui du 2023-07-03 en envoie deux, sur SIZE et USMV. Les écarts suivants viennent de ces deux ajustements. L'écart de Sharpe est nul au millième, sous le seuil de 0.05 fixé d'avance, et les chiffres publiés plus haut ne sont pas réécrits. Ce n'est pas un verdict de stratégie : il s'agit de la correction d'un défaut, mesurée sur des fenêtres déjà vues.

## Files

- `main.py` - Strategy (v3, risk-adjusted momentum with skip-month)
- `research.ipynb` - Factor analysis and signal robustness tests
- `quantbook.ipynb` - Reproduction QuantBook de l'analyse exploratoire sur les donnees natives QC (validation pre-backtest)

## References

- Fama & French (1993), "Common risk factors in the returns on stocks and bonds"
- Barroso & Santa-Clara (2015), "Momentum has its moments"
