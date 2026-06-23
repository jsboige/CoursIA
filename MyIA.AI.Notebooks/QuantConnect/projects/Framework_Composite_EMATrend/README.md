# Framework_Composite_EMATrend

**Asset class:** US Equities (Mag7 + mega-caps)
**Cloud project ID:** 28911253

## Description

Framework composite combining EMA-Cross-Alpha (5 tech/Mag7 stocks, daily
rebalance) with TrendStocks-Alpha (15 diversified mega-caps, weekly rebalance)
via the QC Algorithm Framework. Target allocation: EMA70/Trend30 (sweep winner).

Universe overlap: the 5 Mag7 stocks (AAPL, MSFT, GOOGL, AMZN, NVDA) are
included in both strategies; the MultiStrategyPCM additively combines weights,
giving Mag7 higher allocation when both strategies agree on direction.

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Framework_Composite_EMATrend"`
**QC Cloud:** Deployed as project 28911253 (IBKR margin, direct backtest).

## Backtest Metrics

| Metric | Catalog 2015-2025 | Aligned 2018-2025 |
|--------|-------------------|-------------------|
| Sharpe Ratio | 0.741 | **0.611** |
| CAGR | — | 16.670% |
| Max Drawdown | 28.0% | 27.9% |
| PSR | 27.4% | 19.8% |

Catalog backtest (2015-2025 full decade, EMA70/Trend30) = Sharpe 0.741
(docstring claim was 0.867 → real 0.741, -14%). See `docs/qc/qc-comparative-backtests.md`.

## Aligned baseline (2018-2025)

Verified on the cohort-aligned window (2018-01-01 → 2025-01-01, 1761 tradeable
dates), same EMA70/Trend30 winner config:

- **Sharpe 0.611** (backtest `3095a263d5bd30df181ec002c0a52b72`, project 28911253)
- CAGR 16.670%, MaxDD 27.9%, PSR 19.8%

**Verdict: survives alignment with a mild drop** (0.741 → 0.611, -18%) — not a
period-overfit collapse. Loses part of the 2015-2017 Mag7 pre-ramp and absorbs
the 2022 Mag7 drawdown, but the trend signal holds. On the aligned window this is
the **highest-Sharpe COMP (composite-framework) backbone verified to date**
(edges composite-c2-equityfactor 0.574, FamaFrenchAllWeather 0.338,
composite-c1-multiasset 0.258). Promoted Tier 4 (Untested) → Tier 2 (Historique).

**Mag7 survivorship caveat:** the EMA sleeve is 100% Mag7, so the Sharpe is
partly an artifact of Mag7 outperformance over the backtest decade. Highest
Sharpe is not the same as the most robust constitution: composite-c2-equityfactor
(0.574, factor-diversified across 25 stocks) is the more defensible COMP leader
constitution-wise, while EMATrend is the higher-Sharpe but Mag7-concentrated one.
See Key-finding #36 in `docs/qc/qc-comparative-backtests.md`.

## Files

- `main.py` - Strategy (EMA70/Trend30 composite, aligned 2018-2025)
- `alpha_models.py` - EMACrossAlpha + TrendStocksAlpha
- `portfolio_construction.py` - MultiStrategyPCM (alpha allocation blend)
