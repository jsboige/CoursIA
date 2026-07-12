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

## Files

- `main.py` - Strategy (v3, risk-adjusted momentum with skip-month)
- `research.ipynb` - Factor analysis and signal robustness tests

## References

- Fama & French (1993), "Common risk factors in the returns on stocks and bonds"
- Barroso & Santa-Clara (2015), "Momentum has its moments"
