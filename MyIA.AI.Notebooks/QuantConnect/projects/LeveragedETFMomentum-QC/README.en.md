# LeveragedETFMomentum-QC

**Asset class:** US Equities (Leveraged ETFs)
**Cloud project ID:** QC Project ID: 29687520 (cloned 2026-04-04, **not redeployed in QC Cloud**)

## Description

Clone of **QC Strategy Library #60** (*Leveraged ETF Momentum Allocator* by **Grant Forman**). Momentum strategy on leveraged ETFs with aggressive rotation between SPY/QQQ/TQQQ/UVXY/TECL/SPXL/SQQQ/TECS/BSV based on RSI + SMA regime detection (bull > 200 SMA, bear/volatility branches).

## Verified measures (multi-source)

> **Honest note (#1621, drainage #9434)**: the LeveragedETFMomentum-QC folder suffered from a **library-claim misattribution**: the README presented "Sharpe 1.80, CAGR 101.03%, MaxDD 47.50%" as "Backtest Metrics" while these figures are the **QC Strategy Library #60 claim** (cf. `main.py:6`: `# OOS 1Y Sharpe 1.80, 5Y CAGR 101.03%, 5Y Drawdown 47.50%, 54% Win Rate`) — **NOT a local backtest output**. The folder **does not contain a `research.ipynb`** unlike other clones (#9530 DualMomentum, #9537 EMA-Cross-Crypto, #9542 DynamicVIXSpyRegime-QC) — local reproduction **never happened**. The tables below cite the **library claim with explicit traceability** + a **SUSPECT bull-market overfit flag** (leveraged ETFs + aggressive rotation on 2015-2024 window covering 85% bull market).

| Source | Sharpe | CAGR | MaxDD | Period | Universe |
|--------|--------|------|-------|--------|----------|
| **QC Strategy Library #60** (original claim, `main.py:6`) | **1.80** | **101.03%** | **47.50%** | **OOS 1Y** (5Y CAGR — window unspecified) | 9 leveraged ETFs (SPY/QQQ/TQQQ/UVXY/TECL/SPXL/SQQQ/TECS/BSV) |
| `main.py` docstring (`main.py:6-8`) | n/a | n/a | n/a | `SetStartDate(2015, 1, 1)`, `set_end_date(2024, 12, 31)` | idem |
| Local reproduction | **NOT REPRODUCED** | n/a | n/a | n/a | n/a |

**Honest reading — SUSPECT BULL-MARKET OVERFIT (c.1277-L4 ★★)** : a CAGR of **101.03%** over 5 years with a Sharpe 1.80 on **leveraged ETFs** (TQQQ = 3× QQQ, TECL = 3× Technology, SPXL = 3× S&P500) **rotating aggressively** between Bull (TQQQ) and Bear (UVXY/TECS/SQQQ) is **structurally aligned with a bull market**. The 2015-2024 window includes:
- 6 years of quasi-continuous bull market (2015-2019, 2020-2021, 2023-2024) where the triple leverage TQQQ multiplied gains
- Only 2 notable bear quarters (Q4 2018, Q1 2020) and the 2022 drawdown (shallow for QQQ/TQQQ)
- **A sustained true bear (e.g. 2008-2009 or 2022 inflation bear)** could produce a MaxDD **far above 47.50%** because triple leverage amplifies drawdowns

Cf. **c.1277-L4 ★★** (AllWeather): a Sharpe > 2× the base on SMA crossover = SUSPECT structural overfit on uptrend universe. The same mechanics apply here: the **strategy is profitable on the backtest but vulnerable to a sustained true bear** (leveraged ETF decay + bear whipsaw).

**Library claim verification**: QC Strategy Library #60 (Grant Forman, `https://www.quantconnect.com/strategies/60`) is a public strategy with **pedagogical** purpose on the mechanics of **conditional sector rotation** — **NOT a live deployment signal**. The `QC Project ID 29687520` (cloned 2026-04-04) was **never deployed in QC Cloud** (legacy README confirmed "Copy files to a new QC Cloud project to run").

**Reproducibility**: the library claim is **locally reproducible** via Lean CLI (`lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/LeveragedETFMomentum-QC"`) — the 9 tickers are liquid ETFs running 2015-2024. **This PR does not run the local reproduction** (out of scope, separate future action); the legacy README note "Metrics from original library, not locally reproduced" remains true.

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/LeveragedETFMomentum-QC"`
**QC Cloud:** QC Project ID `29687520` cloned 2026-04-04, **not redeployed in Cloud**. Copy `main.py` into a new QC Cloud project to run. Note: local Docker Lean reproduction should reproduce the library claim (with dividends/fees) — expected variations ~10-20% on MaxDD, ~5-15% on CAGR (Interactive Brokers fees + dividends).

## Files

- `main.py` - Strategy (QC Strategy Library #60 clone, conditional sector rotation on 9 leveraged ETFs)

## References

- QuantConnect Strategy Library #60 — *Leveraged ETF Momentum Allocator* by Grant Forman: `https://www.quantconnect.com/strategies/60`
- `main.py:6-8` docstring: library source + URL + QC Project ID 29687520 + author Grant Forman
- c.1277-L4 ★★ (AllWeather) — SUSPECT overfit on SMA crossover > 2× base; same mechanics applicable here for lev. ETFs on bull-only backtest
- c.1281-L1 ★★ (DynamicVIXSpyRegime-QC) — library claim misattribution pattern
