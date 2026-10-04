# BitcoinRegimeGate-QC — BTC regime gate for QQQ/SHY

Distillation of QC Research **"Bitcoin Regime Signal for Growth Equities"** (Derek Melchin, published Aug 2026) — [source](https://www.quantconnect.com/research/21195/bitcoin-regime-signal-for-growth-equities/). Ported into the repository for issue #18576 (re-evaluation of reading #12748: the August IGNORE verdict's "not published" and "no primary sources" reasons fell on the published version).

## Idea

Read the risk regime from **BTC, a 24/7 market** ("no halts, circuit breakers, or closing bell" — the author), to allocate between **QQQ** (risk on) and **SHY** (risk off) — the **crypto → equity** face of the spillover documented by Iyer 2022 (IMF GFSN 2022/001): BTC explains 14-18% of equity volatility variation, ~17% for the S&P 500.

**Rule** (faithful to the article):

> Hold QQQ when (BTC > SMA50 BTC) AND (ROC20 BTC > 0), else hold SHY.
> Weekly re-evaluation: first trading day at 8:00 ET, before the US open.

Same gesture as `DynamicVIXSpyRegime-QC` (regime gate → equity/bonds), with a **different source** (24/7 Bitfinex BTC instead of VIX) and a growth underlying (QQQ). The repository's BTC cohort tranche 11 measured **no crypto → crypto edge**; this distillate tests the crypto → equity face, which is uncovered.

## Primary sources (published article)

- Faber 2007 (SSRN 962461) — tactical timing via moving average.
- Liu & Tsyvinski 2021 (RFS 34(6)) — systematic crypto risks.
- Iyer 2022 (IMF GFSN 2022/001) — BTC → equity vol spillovers.

## Author claims confronted — repository measurements (QC Cloud, 2026-09-30)

| Author claim (2014-2026) | Value |
|---|---|
| Strategy Sharpe | 0.838 (vs QQQ 0.682, SPY 0.564) |
| 30-70 d × 10-30 d grid | 25/25 > SPY, 23/25 > QQQ, median 0.812 |

**Measured (QC project 37168922, one compile for all 4 runs, paired QQQ buy-and-hold benchmark):**

| Run | Period | Sharpe | CAGR | MaxDD | PSR |
|---|---|---|---|---|---|
| **Gate IS** | 2016-01 → 2021-12 | **1.133** | 18.51% | **14.40%** | 56.4% |
| QQQ-hold IS (benchmark) | 2016-01 → 2021-12 | 0.961 | 24.74% | 28.20% | 36.0% |
| **Gate OOS** | 2022-01 → 2026-06 | **0.640** | 14.87% | **15.20%** | 14.3% |
| QQQ-hold OOS (benchmark) | 2022-01 → 2026-06 | 0.426 | 15.25% | 34.70% | 5.9% |

**Reading**: the gate beats the QQQ buy-and-hold on a risk-adjusted basis in **both** windows (OOS Sharpe +50%, OOS MaxDD cut by 2.3x — 15.2% vs 34.7%, while covering the 2022 bear) at equal CAGR. Honest caveats: OOS PSR 14.3% (the edge vs cash is not statistically established on the OOS window alone), and the repository's BTC tranche-11 cohort measured no **crypto → crypto** edge — the edge here lives on the **crypto → equity** face. Status: `Alive — risk-adjusted` (entry in `docs/qc/qc-strategies-status.md`).

## Structure

- `main.py` — LEAN algorithm with no ML: the article's gate is a pure regime filter.
- No research notebook: unlike `DynamicVIXSpyRegime-QC` (RandomForest overlay), there is nothing to train — the distillate is the filter itself.
