# Framework_Composite_EMATrend

**Asset class:** US Equities (Mag7 + mega-caps)
**Cloud project ID:** 28911253

## Description

Framework composite combining EMA-Cross-Alpha (5 tech/Mag7 stocks, daily
rebalance) with TrendStocks-Alpha (15 diversified mega-caps, weekly rebalance)
via the QC Algorithm Framework. Target allocation: EMA70/Trend30 (sweep winner).

Universe overlap: the 5 Mag7 stocks (AAPL, MSFT, GOOGL, AMZN, NVDA) are
included in both strategies. The portfolio construction model
(`MultiStrategyPCM`) gives each alpha a capital slice, then adds the two slices
on these five stocks. This is the `intent` mode, the default since #19759.

**Defect fixed by #19759.** Before calling `determine_target_percent`, Lean's
`PortfolioConstructionModel` keeps only the most recent active insight of each
symbol. EMACross emits every day on its five stocks, TrendStocks once a week on
its fifteen. Before #19759 the slices were therefore never added: on the five
shared stocks, the target followed the last alpha to emit. TrendStocks won in
602 of the 3502 measured calls. According to the code, each of these five
stocks then moved from the EMACross share (70 % split over its rising stocks,
i.e. 0.14 when all five rise) to the TrendStocks share (30 % split over its
rising stocks, up to fifteen), then moved back at the next EMACross emission.
Measured turnover is 74.7 times the portfolio per year, against 14.4 under
`intent`, and fees about 2.6 % of portfolio value per year, against 0.5 %.

This behaviour remains available under `mode` = `base` to reproduce the earlier
figures. Under `intent`, the model rebuilds the targets from the most recent
active insight of each (symbol, alpha) pair, then adds them per symbol.

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Framework_Composite_EMATrend"`
**QC Cloud:** Deployed as project 28911253 (IBKR margin, direct backtest).

## Measurement #19759: `NO BEATS`

QC Cloud backtests of 2026-10-07, from 2015-01-02 to 2026-07-09 (2894 sessions),
Interactive Brokers fees. The protocol and the verdict rule were fixed before
any computation ([#19759](https://github.com/jsboige/CoursIA/issues/19759), same
rule as #19740). The Sharpe ratio is computed at a zero risk-free rate on the
portfolio value at each close, by an analysis kept outside the repository; it
therefore differs from the Sharpe shown by QC, which subtracts a risk-free rate.

| Version | Sharpe | CAGR | Max drawdown | Turnover per year | Mean gross exposure |
|---------|--------|------|--------------|-------------------|---------------------|
| `intent` (default) | 1.20 | 27.1 % | −36.3 % | 14.4 | 0.93 |
| `base` (code before #19759) | 0.95 | 17.0 % | −28.0 % | 74.7 | 0.82 |
| EMACross alone (`ema`) | 1.19 | 30.8 % | −37.4 % | 14.6 | 0.91 |
| TrendStocks alone (`trend`) | 0.98 | 17.7 % | −33.7 % | 14.5 | 0.99 |
| SPY held (`spy`) | 0.83 | 13.8 % | −33.7 % | 0.09 | 1.00 |
| 60 % SPY / 40 % IEF (`sixty40`) | 0.88 | 8.9 % | −21.1 % | 0.29 | 1.00 |

**Verdict.** It is `NO BEATS` for `base` and for `intent`: no Sharpe difference
with the references is significant. The difference is tested by a circular
block bootstrap with 21-session blocks (10,000 draws, Holm correction over the
two references).

| Candidate | Difference vs SPY [95 % CI] | Difference vs 60/40 [95 % CI] | Holm p (SPY / 60/40) |
|-----------|-----------------------------|-------------------------------|----------------------|
| `intent` | +0.37 [−0.03; +0.76] | +0.32 [−0.11; +0.75] | 0.069 / 0.074 |
| `base` | +0.13 [−0.29; +0.52] | +0.07 [−0.38; +0.52] | 0.57 / 0.57 |

`intent` comes close to the threshold without crossing it. Its differences are
positive on all three sub-periods, but most of it comes from 2015-2018: +0.96
against SPY, then +0.11 on 2019-2022 and +0.07 on 2023 → 2026-07. The parameter
grid and the doubled-fee run were planned only for a significant candidate:
they were not launched.

**What each slice brings.** Under `intent`, the Sharpe difference with EMACross
alone is +0.00 [−0.10; +0.12], and the weekly return correlation is 0.985: the
composite behaves like EMACross alone, with a lower CAGR. Against TrendStocks
alone, the difference is +0.22 [−0.17; +0.58]. Under `base`, the difference
with EMACross alone is −0.24 [−0.49; −0.01]: the forced turnover cost Sharpe.
These differences are descriptive, outside the Holm correction.

**Choice of default.** `intent` is the design the project announces: the
`MultiStrategyPCM` docstring and this README describe adding the slices. `base`
turned the portfolio over five times faster for a lower Sharpe. Neither beats
the references: the default change makes the project match its description, it
does not create a demonstrated advantage.

**Limits.**
- The EMACross slice holds only five Mag7 stocks, chosen knowing the decade.
  NVDA alone provides 44 % of the closed-position result under `intent` (47 %
  under `ema`). This bias favoured the candidates, which strengthens the
  `NO BEATS`.
- The backtests asked for an end on 2026-09-30. The QC organisation used keeps
  back the last 90 days and moved the end to 2026-07-09, without error. All
  versions ran in the same organisation: the comparisons cover the same
  sessions.
- The `PCM calls with Trend on EMA tickers` statistic is 602 under `base` and
  under `intent`: it counts the insights received by `determine_target_percent`,
  before the rebuild. The rebuild shows in the turnover and in the orders on the
  ten stocks that only TrendStocks holds (622 to 875 per stock under `base`, 238
  to 284 under `intent`).

## Figures from before #19759

The two sections below date from before the measurement; they are kept for the
record.

**Reading corrected by #19759.**
- **Aligned baseline.** The `readme` run (`base` on 2018-01-01 → 2025-01-01,
  1760 sessions) reproduces it: QC Sharpe 0.614, CAGR 16.73 %, max drawdown
  27.9 %, 8396 orders. The PSR differs (8.95 % against 19.8 %); the cause was
  not measured. These figures measured the `base` code, whose slices were not
  added on the shared stocks.
- **"The MultiStrategyPCM additively combines weights."** This was false under
  `base`; it is true under `intent`.

### Backtest Metrics

| Metric | Catalog 2015-2025 | Aligned 2018-2025 |
|--------|-------------------|-------------------|
| Sharpe Ratio | 0.741 | **0.611** |
| CAGR | — | 16.670% |
| Max Drawdown | 28.0% | 27.9% |
| PSR | 27.4% | 19.8% |

Catalog backtest (2015-2025 full decade, EMA70/Trend30) = Sharpe 0.741
(docstring claim was 0.867 → real 0.741, -14%). See `docs/qc/qc-comparative-backtests.md`.

### Aligned baseline (2018-2025)

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

- `main.py` - Strategy (EMA70/Trend30 composite, aligned 2018-2025; `mode`, `start`, `end`, `fee_mult` and grid parameters since #19759)
- `alpha_models.py` - EMACrossAlpha + TrendStocksAlpha
- `portfolio_construction.py` - MultiStrategyPCM (alpha allocation blend)
