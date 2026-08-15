# HighBookToMarketFScore-QC

**Asset class:** US Equities (value stocks)
**Cloud project ID:** QC Project ID: 29687591 (cloned 2026-04-05, **not deployed in QC Cloud**)

## Description

Clone of **QC Strategy Library #343** (*High Book-to-Market High F-Score Quality Value* by **Louis Szeto**). Systematic value+quality strategy selecting stocks with high book-to-market filtered by Piotroski F-Score ≥ 8, equally-weighted, monthly rebalance.

## Verified measures (multi-source)

> **Honest note (#1621, drainage #9434)**: the HighBookToMarketFScore-QC folder suffered from a **library-claim misattribution**: the README presented "Sharpe 2.09, CAGR 18.44%, MaxDD 24.20%" as "Backtest Metrics" while these figures are the **QC Strategy Library #343 claim** (cf. `main.py:5-10`: `# OOS 1Y Sharpe 2.09, 5Y CAGR 18.44%, 5Y Drawdown 24.20%, 62% Win Rate`) — **NOT a local backtest output**. The folder **does not contain a `research.ipynb`** unlike other clones (#9530 DualMomentum, #9537 EMA-Cross-Crypto, #9542 DynamicVIXSpyRegime-QC) — local reproduction **never happened**. The legacy README also said "Cloud project ID: None (local only)" while `main.py:10` mentions QC Project ID **29687591** (cloned 2026-04-05) — contradiction corrected. The tables below cite the **library claim with explicit traceability** + a **SUSPECT structural overfit flag** (Sharpe 2.09 on value+quality screen = exposed to look-ahead bias + small-universe variance).

| Source | Sharpe | CAGR | MaxDD | Period | Universe |
|--------|--------|------|-------|--------|----------|
| **QC Strategy Library #343** (original claim, `main.py:5-10`) | **2.09** | **18.44%** | **24.20%** | **OOS 1Y** (5Y CAGR — window unspecified) | Top 20% book-to-market stocks filtered by F-Score ≥ 8, equal-weighted |
| `main.py:5-10` docstring | n/a | n/a | n/a | `self.set_start_date(self.end_date - timedelta(12*365))`, `set_end_date(2025, 1, 1)` | idem |
| Local reproduction | **NOT REPRODUCED** | n/a | n/a | n/a | n/a |

**Honest reading — SUSPECT STRUCTURAL OVERFIT (c.1283-L1 ★★)** : a Sharpe of **2.09** on a value+quality screen (Piotroski F-Score ≥ 8) on **library OOS 1Y** is exposed to **3 structural sources of overestimation**:

1. **Fundamental look-ahead bias**: the Piotroski F-Score (2000) uses financial ratios published with a delay (60-90 days post-quarter-close for most US fundamentals via SEC 10-Q/10-K filings). In a classic QuantConnect backtest, these data are loaded at the monthly decision moment — but **unless `SetDataNormalizationMode(PointInTimeFundamentals)` is used**, the backtest may include data that was **not available at the decision time** (snapshot bias).

2. **Data mining on a 12y rolling window**: library #343 uses `set_start_date(self.end_date - timedelta(12*365))` + `set_end_date(2025, 1, 1)` = **12 years rolling**. A strategy filtering top 20% B/M + F-Score ≥ 8 on a window chosen a posteriori is **exposed to test multiplicity** (backtest on N possible start periods → cherry-picked favorable results).

3. **Small-universe variance**: top 20% B/M + F-Score ≥ 8 = very restricted universe (probably 30-50 stocks vs 500+ of the SP500). Monthly rebalance over 12 years × ~30 trades = ~360 trades = high mechanical Sharpe variance (95% confidence interval of Sharpe ≈ ±0.5 for N=360, which would make a true Sharpe of 1.6 indistinguishable from 2.6).

**Cumulative effect of the 3 factors**: a library Sharpe of 2.09 could mask a true Sharpe of **1.2-1.6** on the same strategy with `PointInTimeFundamentals`, a priori fixed OOS window, and broadened universe. This is **NOT** a live deployment signal without independent empirical verification.

Cf. **c.1282-L2 ★★** (LeveragedETFMomentum): a Sharpe > 2× the base on lev. ETFs bull-only backtest = SUSPECT structural overfit. Here the same mechanics apply: the **strategy is profitable on the backtest but vulnerable to methodological pathologies** (look-ahead + data mining + small-universe). **NEVER** deploy live without a QC Cloud backtest with `PointInTimeFundamentals` + walk-forward OOS.

**Library claim verification**: QC Strategy Library #343 (Louis Szeto, `https://www.quantconnect.com/strategies/343`) is a public strategy with **pedagogical** purpose on the mechanics of **value+quality systematic screen** — **NOT a live deployment signal**. The `QC Project ID 29687591` (cloned 2026-04-05) **was never deployed in QC Cloud** (legacy README confirmed "Not yet deployed").

**Reproducibility**: the library claim is **locally reproducible** via Lean CLI (`lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/HighBookToMarketFScore-QC"`) — the Piotroski F-Score universe is built from fundamentals data via `universe.py` and `piotroski_score.py`. **This PR does not run the local reproduction** (out of scope, separate future action); the legacy README note "Metrics from original library, not locally reproduced" remains true.

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/HighBookToMarketFScore-QC"`
**QC Cloud:** QC Project ID `29687591` cloned 2026-04-05, **not deployed in Cloud**. Copy `main.py` + `piotroski_score.py` + `piotroski_factors.py` + `universe.py` + `symbol_data.py` into a new QC Cloud project to run. Note: local Docker Lean reproduction should reproduce the library claim (with dividends/fees) — expected variations ~10-20% on MaxDD, ~5-15% on CAGR (Interactive Brokers fees + dividends). For a more rigorous backtest (anti-SUSPECT), add `self.set_data_normalization_mode(DataNormalizationMode.POINT_IN_TIME_FUNDAMENTALS)` before `set_start_date()` in `main.py:18-19` and compare the measures.

## Files

- `main.py` - Strategy (QC Strategy Library #343 clone, Piotroski F-Score value screen monthly rebalance)
- `piotroski_score.py` - F-Score computation (Profitability + Leverage/Liquidity + Operating Efficiency, 9 binary signals)
- `piotroski_factors.py` - Individual fundamental factors (ROA, CFO, ΔROA, ACCRUAL, ΔLEVER, ΔLIQUID, EQ_OFFER, ΔMARGIN, ΔTURN)
- `universe.py` - PiotroskiScoreUniverseSelectionModel (universe selection + F-Score ≥ 8 filter)
- `symbol_data.py` - Helpers to load fundamentals data

## References

- QuantConnect Strategy Library #343 — *High Book-to-Market High F-Score Quality Value* by Louis Szeto: `https://www.quantconnect.com/strategies/343`
- `main.py:5-10` docstring: library source + URL + QC Project ID 29687591 + author Louis Szeto
- Piotroski (2000), "Value Investing: The Use of Historical Financial Statement Information to Separate Winners from Losers", *Journal of Accounting Research* 38(suppl.) — founding paper of the F-Score
- c.1282-L2 ★★ (LeveragedETFMomentum-QC) — SUSPECT structural overfit pattern on lev. ETFs bull-only backtest; same mechanics applicable here for value+quality on OOS 1Y window
- c.1281-L3 ★★ (DynamicVIXSpyRegime-QC) — library claim misattribution pattern, reproducible arche to drain the other QC library clone READMEs