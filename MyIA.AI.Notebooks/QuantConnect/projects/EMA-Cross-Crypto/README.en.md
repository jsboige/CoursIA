# EMA-Cross-Crypto

**Asset class:** Crypto (BTC, ETH)
**Cloud project ID:** None (local only)

## Description

Dual EMA crossover on cryptocurrency. Goes long when EMA(20) > EMA(50) on BTC/ETH.

> **Introductory note**: the previous description said EMA 20/60 — the **implemented strategy is EMA 20/50** (cf `main.py:32-33` and `research.ipynb` cell[7] BASELINE). The sweet spot validated on the 2020-2025 window remains EMA 20/50; no slow_period > 50 beats the baseline on the MaxDD criterion (see H1 below).

## Verified measures (multi-source)

> **Honest note (#1621, drainage #9434)**: the EMA-Cross-Crypto folder contains **two notebooks that study two different universes** — `research.ipynb` works on **BTC-USD** (the strategy as implemented in `main.py`), while `quantbook.ipynb` works on **SPY/QQQ/IWM as a substitute** (cell[3] line 2 explicit: « Equity universe (substitute for crypto in Docker research environment) ») because the local Docker environment does not load Binance crypto data. The numbers produced by the two notebooks are **fundamentally divergent** and **CANNOT be combined into a single canonical measure**: different period (2020-2025 vs 2010-2025), different universe (BTC vs US equities), different mechanism. The H1-H5 tables below cite **only `research.ipynb` (BTC)**; the table below cites the **two distinct implementations** for transparency.

| Source | Sharpe | CAGR | Max DD | Period | Universe |
|--------|--------|------|--------|--------|----------|
| [`research.ipynb`](research.ipynb) cell[7] (exec=3) — BASELINE EMA 20/50, 95% position | **0.939** | **30.5%** | **-47.3%** | 2020-2025 (2192 d) | **BTC-USD** (yfinance) |
| [`research.ipynb`](research.ipynb) cell[22] (exec=9) — + SMA200 filter (main MaxDD lever) | **1.016** | **31.7%** | **-41.7%** | 2020-2025 (2192 d) | **BTC-USD** (yfinance) |
| [`research.ipynb`](research.ipynb) cell[34] (exec=14) — recommended config SMA200+Cap80+Trail10% | **0.983** | **25.6%** | **-34.1%** | 2020-2025 (2192 d) | **BTC-USD** (yfinance) |
| [`quantbook.ipynb`](quantbook.ipynb) cell[12] (exec=6) — best EMA period 25/55 (substitute environment) | **0.436** | **8.4%** | **-19.0%** | 2010-2025 (4024 d) | **SPY/QQQ/IWM** (Docker substitute) |
| [`quantbook.ipynb`](quantbook.ipynb) cell[20] (exec=10) — optimal config vs Buy & Hold | **0.377** | **7.6%** | **-22.1%** | 2010-2025 (4024 d) | **SPY/QQQ/IWM** (Docker substitute) |
| [`main.py`](main.py) docstring — research synthesis | n/a | n/a | n/a | 2015-2024 (code start/end) | BTCUSDT (Binance Cash) |

**Honest reading**: the divergence between the two notebooks **is not a bug** — these are **two implementations on two distinct universes**:

- `research.ipynb` uses `yfinance` to load **real BTC-USD**; it is the **pedagogical reference** for the crypto strategy as coded in `main.py` (BTCUSDT on Binance Cash).
- `quantbook.ipynb` loads **SPY/QQQ/IWM as a substitute** because the Docker Lean Engine research environment does not provide Binance crypto data — the Sharpe 0.377 / CAGR 7.6% it produces are **NOT** a measurement of the EMA-Cross-Crypto strategy, but a measurement of an analogous EMA strategy applied to a 15-year US equities universe.

**For the crypto strategy itself** (as deployable on QC Cloud with BTCUSDT Binance): **`research.ipynb`** is the reference. **`quantbook.ipynb`** serves only as a methodological test bench (testing the EMA mechanics on a liquid universe loaded in Docker), not as a performance evaluation of the EMA-Cross-Crypto strategy.

Provenance detail: [`MANIFEST.md`](assets/readme/MANIFEST.md).

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/EMA-Cross-Crypto"`
**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics

| Metric | Value |
|--------|-------|
| Method | EMA 20/50 crossover |
| Universe | BTC, ETH |
| Rebalance | Daily |

### Recommended configuration metrics (from research.ipynb)

| Configuration | Sharpe | CAGR | Max DD | Verdict |
|---------------|--------|------|--------|---------|
| EMA 20/50, 95% (legacy v1) | 0.939 | 30.5% | -47.3% | LIVE (legacy) |
| **EMA 20/50 + Cap 80% + Trail 10% + SMA200 (v2)** | **0.983** | **25.6%** | **-34.1%** | **RECOMMENDED** |
| SMA200 only (filter only) | 1.016 | 31.7% | -41.7% | Alternative live candidate |

## Files

- `main.py` — Strategy v2 (EMA 20/50, cap 80%, trail 10%, SMA200 filter)
- `research.ipynb` — 5 hypotheses H1-H5 + optimal combination + regime analysis (BTC-USD 2020-2025)
- `quantbook.ipynb` — Docker-substitute environment on SPY/QQQ/IWM 2010-2025 (methodological test bench, NOT a measure of the crypto strategy)
