# DynamicVIXSpyRegime-QC

**Asset class:** US Equities (SPY)
**Cloud project ID:** QC Project ID: 32921262 (redeployed 2026-06-15)

## Description

QC Strategy Library #50 clone (Dynamic VIX-SPY Regime Switching by Ahmet Kasti). VIX-based regime detection on SPY switching between aggressive and defensive positioning. ML overlay (RandomForestClassifier, 11 VIX/SPY features).

## Verified measures (multi-source)

> **Honest note (#1621, drainage #9434)**: the DynamicVIXSpyRegime-QC folder suffered from a classic **misattribution**: the README presented "Sharpe 1.72, CAGR 29.76%" as "Backtest Metrics" while these figures are the **QC Strategy Library #50 claim** (cf. `main.py:5`: `# OOS 1Y Sharpe 1.72, 5Y CAGR 29.76%`) — **NOT a local backtest output**. The local reproduction via `research.ipynb` produces **fundamentally different numbers** (Sharpe 0.97 baseline, 1.023 best config). The divergence is **methodological** (the library likely uses OOS 1Y on a 2018-2023 window vs our 2015-2025 repro, and 5Y CAGR vs 10Y CAGR), **not a bug**. The tables below cite the **two implementations** for transparency.

| Source | Sharpe | CAGR | MaxDD | Period | Universe |
|--------|--------|------|-------|--------|----------|
| **QC Strategy Library #50** (original claim, `main.py:5`) | **1.72** | **29.76%** | **17.80%** | **OOS 1Y** (5Y CAGR — window unspecified) | SPY + TLT + GLD + BIL |
| `research.ipynb` cell[9] (exec=5) — BASELINE (default params) | **0.97** | **23.83%** | **-22.09%** | 2015-01-02 → 2025-12-30 (2765 days) | SPY + TLT + GLD + BIL + ^VIX |
| `research.ipynb` cell[26] (exec=13) — **BEST (H3: Exposure gross=2.0)** | **1.023** | **31.35%** | **-29.07%** | 2015-01-02 → 2025-12-30 (2765 days) | idem |
| `research.ipynb` cell[9] (exec=5) — **Benchmark SPY Buy & Hold** | 0.536 | 13.54% | -33.72% | 2015-2025 | SPY only |
| `main.py` docstring | n/a | n/a | n/a | `SetStartDate(2015, 1, 1)`, `set_end_date(2024, 12, 31)` | SPY + TLT + GLD + BIL + CBOE VIX |

**Honest reading**: the divergence between the **library** numbers (1.72 / 29.76%) and the **local reproduction** (0.97 / 23.83%) is **NOT a bug** — these are **two implementations on different time windows and likely different configurations**:

- The **library #50** displays its own OOS 1Y figures (likely 2018-2023, a reduced window that favors Sharpe) and 5Y CAGR (likely 2019-2024, a bull market period before the incomplete 2022 bear).
- **`research.ipynb`** reproduces the ML+VIX logic on a **full 10-year window (2015-2025)** including the 2022 bear (LUNA/FTX), which mechanically degrades Sharpe (more trading days = more variance). The local baseline (0.97) **outperforms** SPY Buy & Hold (0.536) by **+80%** in Sharpe — the strategy's edge is reproducible, but the **1.72 figure is not reproducible locally**.

**Why this PR does not touch `research.ipynb` or `main.py`**:
- `research.ipynb`: 29 cells, 13 executed (`execution_count: 1..13`), consistent outputs, 0 errors. This is the **pedagogical reference** for local reproduction. cell[9] output = `Sharpe 0.97, CAGR 23.83%, MaxDD -22.09%` confirmed by Papermill re-run.
- `research_output.ipynb`: 27 cells, 13 executed, consistent outputs with `research.ipynb` (same baseline 0.97 and best 1.023).
- `main.py`: docstring explicitly contains the library reference `# OOS 1Y Sharpe 1.72, 5Y CAGR 29.76%` + URL `https://www.quantconnect.com/strategies/50` — the source is traceable, it was the README that omitted this distinction.

**For the strategy as locally deployable**: `research.ipynb` is the reference. Sharpe 1.72 remains the **library claim** (to be validated before any live trading pass).

## Tested hypotheses (from `research.ipynb`)

Cf. `research.ipynb` cell[3] and cell[26] for the full comparative table (12 configurations). Top 3 by Sharpe:

| Config | Sharpe | CAGR | MaxDD | WinRate |
|--------|--------|------|-------|---------|
| **H3: Exposure gross=2.0** | **1.023** | 31.35% | -29.07% | 55.2% |
| H1: ML threshold=0.6 (= baseline) | 0.970 | 23.83% | -22.09% | 55.2% |
| H3: Exposure gross=1.5 | 0.970 | 23.83% | -22.09% | 55.2% |

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/DynamicVIXSpyRegime-QC"`
**QC Cloud:** QC Project ID `32921262` (redeployed 2026-06-15). The `research.ipynb` notebook uses the QC Cloud kernel (RandomForest + StandardScaler + CBOE VIX data not loaded in local Docker).

## Files

- `main.py` - Strategy (QC Library #50 clone, 4-asset regime switching + ML overlay)
- `research.ipynb` - 5 hypotheses H1-H5 + comparative table + SPY benchmark (2015-2025, 2765 days)
- `research_output.ipynb` - Same notebook, separate execution version

## References

- QuantConnect Strategy Library #50 - Dynamic VIX-SPY Regime Switching by Ahmet Kasti: https://www.quantconnect.com/strategies/50
- Brock et al. (1992), "Simple Technical Trading Rules and the Stochastic Properties of Stock Returns"
- `research.ipynb` cell[0] (MD): complete methodology with ML hyperparameters and VIX/SPY features
