# Framework_Composite_TrendWeather

**Asset class:** US Equities (ETF + stocks)
**Cloud project ID:** None (local only)

> 🇫🇷 **Version française** : voir [`README.md`](README.md) (FR primary)
> 🇬🇧 **EN golden set** : [`README.en.md.legacy`](README.en.md.legacy) (preserved before c.1284 fix)
> 🇫🇷 **FR golden set** : [`README.fr.md`](README.fr.md) (preserved before c.1284 fix)

## Description

Composite framework combining TrendStocks (75%) with AllWeather (25%) via QuantConnect's Algorithm Framework. The trend component uses SMA200+EMA20/EMA50 on 15 large-caps (AAPL/MSFT/GOOGL/AMZN/NVDA/JPM/V/MA/UNH/JNJ/XOM/CVX/HD/PG/KO), AllWeather provides static diversification (SPY 30% / IEF 30% / GLD 30% / XLP 10%).

## Verified measures (multi-source)

> **Honest note (#1621, drainage #9434)**: the Framework_Composite_TrendWeather folder suffered from a **"sweep-comment" methodological misattribution**: the README presented "Sharpe 1.155, CAGR 27.4%, MaxDD 27.7%" as "Backtest Metrics" while these figures come from the **`FrameworkCompositeStrategy` class docstring in `main.py`** (`Allocation sweep results (2015-2026)` v1.3/v1.4b/v1.4c/v1.4d/v1.4e — an allocation sweep **without traced backtest**) **NOT from a persistent execution** in the repo: **no `lean-workspace/`, no `create_backtest` artifact**, no JSON cloud output. The strategy was added in commit `fa122ae7e` (2026-03-09, jsboige + Claude Opus) which declared "Iterated from v1.0 (Sharpe 0.622) to v1.5 (Sharpe 1.155)" — so the 1.155 value is **plausibly** from a one-shot cloud backtest at initial commit time, **not preserved** in the repo. The `quantbook.ipynb` (local Docker + yfinance research) uses a **different default 50/50** and **explicitly warns** (cf. `iter4_research.py:176`: "Simulation Sharpe is typically 2-3x cloud Sharpe"). The tables below cite each source with explicit traceability + a **SUSPECT "sweep-comment" overfit flag**.

| Source | Sharpe | CAGR | MaxDD | Allocation | Period | Methodology |
|--------|--------|------|-------|-----------|---------|-------------|
| **`main.py` docstring, `Allocation sweep results` block** (claim from original commit `fa122ae7e`) | **1.155** | **27.4%** | **27.7%** | T75 / AW25 (v1.4d selected) | **2015-2026** | Internal allocation sweep (5 tranches T60→T80), **no backtest traced in repo** |
| `iter4_research.py` yfinance local | n/a (script) | n/a | n/a | grid 5×5×3 | 2014-2026 | yfinance local, **WARNS** "Simulation Sharpe typically 2-3× cloud Sharpe" |
| `quantbook.ipynb` `In [5]` (research default 50/50) | **0.680** | **10.88%** | **-23.53%** | T50 / AW50 (default research) | 2015-2026 | Lean CLI Docker research, **default 50/50 ≠ main.py T75/AW25** |
| `quantbook.ipynb` `In [8]` (allocation sweep) | 0.382 → 0.738 | 7.22% → 14.02% | -33.72% → -17.29% | grid T0/T10/.../T100 (NO T75) | 2015-2026 | Lean CLI Docker, **T75 absent from grid (jumps T70→T80)** |
| `quantbook.ipynb` `In [9]` (stop-loss sweep) | **0.684 → 2.124** ⚠️ | 10.93% → 21.29% | -23.53% → -4.86% | T50/AW50 + stop-loss | 2015-2026 | Lean CLI Docker, **Stop 5% Sharpe 2.124 = STRUCTURAL SUSPECT overfit** |
| `quantbook.ipynb` `In [11]` (rebalance freq sweep) | 0.619 → 1.070 | 9.92% → 16.13% | -23.53% → -23.94% | T50/AW50 weekly/bi-weekly/monthly | 2015-2026 | Lean CLI Docker, **monthly > weekly by 35-40% Sharpe** |
| `quantbook.ipynb` `In [12]` (T×freq grid, 5bps fees) | 0.544 → 1.239 | 8.90% → 19.60% | -27.88% → -19.43% | T30→T70 × W/2W/M | 2015-2026 | Lean CLI Docker, **T70/Monthly Sharpe 1.239, closest to main.py T75** |
| **Production cloud backtest (one-shot, fa122ae7e)** | **1.155** | **27.4%** | **27.7%** | T75 / AW25 (v1.4d) | 2015-2026 | **NOT PERSISTED in repo** — claim from initial commit only |

**Honest reading — SUSPECT "SWEEP-COMMENT MISATTRIBUTION" (c.1284-L1 ★★)**: a Sharpe of **1.155** claimed over 11 years (2015-2026) with **T75/AW25 allocation**, cited from the **`main.py` docstring** (`Allocation sweep results`) **without any cloud backtest traceable in the repo**, is exposed to **3 methodological sources of overestimation** distinct from the library clones (c.1281-L2/82-L2/83-L2):

1. **Sweep-comment structural overfitting**: the `main.py` docstring cites 5 tranches (T60/T65/T70/**T75**/T80) that vary **monotonously** (Sharpe 1.130→1.141→1.149→**1.155**→1.163, CAGR 23.8%→25.0%→26.2%→**27.4%**→28.7%, MaxDD 24.5%→25.6%→26.6%→**27.7%**→28.7%) — **+0.033 Sharpe between T70 and T75 over 11 years = 0.003/year, in statistical noise**. The choice "T75/AW25 selected" is a **middle of a monotonous grid** (not a discriminating optimum), with a comment "best risk/return balance before beta exceeds 0.80 and MaxDD approaches 29%" that is **not backed by any beta measure in the repo**. The grid is **regular** (T60→T65→T70→T75→T80, step 5), **not discriminating**.

2. **`quantbook.ipynb` 50/50 ≠ `main.py` T75/AW25**: the repo's local research uses a **default 50/50** (cf. the `quantbook.ipynb` header: "TrendStocks (50%)", "AllWeather (50%)") **different from the T75/AW25 production**. The allocation grid `quantbook.ipynb` `In [8]` shows **T70/T30 = Sharpe 0.728** and **T80/T20 = Sharpe 0.737** — so **interpolation toward T75 ≈ Sharpe 0.732**, **not 1.155**. The gap **1.155 - 0.732 = +0.42** is not explained by allocation change alone; it likely comes from **substantial methodological differences** (Interactive Brokers fees via `set_brokerage_model` in `main.py` vs 0 fees in the `In [5]` simulation, `trend_tickers` 15 names vs 15 identical names OK, **BUT** momentum-weighted `TrendStocksAlpha` (`alpha_models.py`) vs equal-weight in `build_composite_weights` (`In [4]`), **AND** monthly `rebalance=timedelta(days=31)` in `main.py` vs weekly default (`W-MON`) in the `In [11]` sweep). Without **complete retro-engineering**, the gap remains unallocated.

3. **`iter4_research.py` WARNS 2-3× overstate**: the local research script explicitly displays (line 176) "Simulation Sharpe is typically 2-3× cloud Sharpe". So the **simulated Sharpe 0.732 (interpolated between T70 and T80 in `In [8]`)** could mask a **cloud Sharpe ≈ 0.24-0.37**, **not 1.155**. Conversely, the **cloud Sharpe 1.155** could correspond to a **simulation ≈ 2.3-3.5** (never observed in the quantbook grid, where max = 2.124 on Stop 5% — but this 2.124 is itself SUSPECT). **The gap between 1.155 (production) and 0.732 (local sim 50/50) remains unresolved**.

**Cumulative effect of the 3 factors**: the Sharpe 1.155 / CAGR 27.4% / MaxDD 27.7% cited in README could mask a true Sharpe of **0.6-0.9** on the same strategy with (a) real IBKR fees + dividends + quantified slippage, (b) a priori fixed OOS window (not a posteriori sweep), (c) documented broadened or restricted TrendStocks universe. This is **NOT** a live deployment signal without **complete methodological retro-engineering** or **fresh QC Cloud backtest** with preserved JSON output.

Cf. **c.1281-L3 / c.1282-L3 / c.1283-L3 ★★** (library clones): the "misattribution" pattern applies here with a **3rd archetype**: library clones (claim OOS 1Y without local repro, c.1281/82/83) + **sweep-comment (c.1284) = `main.py:N` comment block cited as "backtest metrics" without traceable backtest**. The constant mechanic remains: **explicit provenance + mandatory SUSPECT pedagogy warning**.

**Provenance verification**: the commit `fa122ae7e` (2026-03-09, jsboige + Claude Opus) declares "Iterated from v1.0 (Sharpe 0.622) to v1.5 (Sharpe 1.155)" in its message — **the 1.155 is therefore a commit author claim, not a reproducible measure** from the repo. **No QC Cloud Project ID tag**, **no `lean-workspace/`, no backtest JSON preserved**. To reproduce, one would have to **re-create a QC Cloud project, copy `main.py` and `alpha_models.py`, attach the `SharedPCM` library, and run `lean backtest` or `create_compile` + `create_backtest`** — operation **out of scope** for this PR (markdown-only PR).

**Reproducibility**: the sweep-comment claim is **not reproducible** from the current repo (no artifacts). Local research **is reproducible**: `python iter4_research.py` (yfinance local, 2-3× overstate) or `jupyter nbconvert --execute quantbook.ipynb` (Lean CLI Docker, default 50/50). The table above cites **both sources** for transparency.

## How to Run

**Lean CLI (local research, default 50/50):** `lean research "MyIA.AI.Notebooks/QuantConnect/projects/Framework_Composite_TrendWeather" --notebook quantbook.ipynb`
**Lean CLI (production T75/AW25 backtest):** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Framework_Composite_TrendWeather"` runs `main.py`, which fixes `alpha_allocations={"TrendStocks": 0.75, "AllWeather": 0.25}`; the 50/50 default exists only in the quantbook. **But expect ~±30-50% variation on Sharpe** vs the 1.155 docstring because of (a) `INTERACTIVE_BROKERS_BROKERAGE` (`set_brokerage_model`) vs 0 fees in research, (b) `trend_tickers` (15 names) vs 15 identical names OK, (c) momentum-weighted TrendStocks vs equal-weight, (d) monthly 31d vs weekly default.
**QC Cloud:** not deployed. Create a QC Cloud project, attach the `SharedPCM` project to it as a library ("Add Library", see the `SharedPCM` README), then copy `main.py + alpha_models.py` to run and preserve outputs in `lean-workspace/<project>/backtests/<timestamp>/`. **Anti-SUSPECT recommendation**: **re-execute** the cloud backtest with exact T75/AW25, **preserve the JSON output** in the worktree, and **compare** to the 1.155 docstring — the expected gap (cf. `iter4_research.py:176` 2-3× overstate) should bring Sharpe back to ~0.4-0.6 in the worst case (local overestimation) or confirm 1.155 (original one-shot backtest correct).

**Note on Docker Lean variations**: `quantbook.ipynb` `In [11]` shows the same strategy run **monthly vs weekly** gives Sharpe **1.064** vs **0.674** (5bps fees) — the "less-frequent-rebalance" effect reduces turnover and preserves trends. `main.py` uses `rebalance=timedelta(days=31)` (monthly) — so **in the same vein as the 1.064**, **not 0.674**.

## Files

- `main.py` — Composite strategy v1.5 production (T75/AW25, monthly rebalance, IBKR fees). **Its class docstring contains the `Allocation sweep results (2015-2026)` block, source of 1.155/27.4%/27.7%** ⚠️
- `alpha_models.py` — TrendStocksAlpha (momentum-weighted) + AllWeatherAlpha (static)
- `SharedPCM/pouches_pcm.py` (QC project library) — `MultiStrategyPouchesPCM`, the canonical pouch PCM imported by `main.py` (extraction #19821 brick 1)
- `iter4_research.py` — Local yfinance research (warns 2-3× overstate cloud Sharpe, line 176)
- `quantbook.ipynb` — Lean CLI Docker research: 50/50 default + sweeps (allocation, stop-loss, rebalance freq, T×freq) with preserved outputs

## Shared module non-regression (#20188)

Since #21134, `main.py` imports `MultiStrategyPouchesPCM` from `SharedPCM/pouches_pcm.py` instead of the local copy `portfolio_construction.py`. Two QC Cloud backtests run on 2026-10-26, with the default parameters and the window 2015-01-01 → 2025-12-31, check that this change alters no order:

- **A**: the `main` code at commit `54f9b9eec1`, with the shared module;
- **B**: the same `main.py` and `alpha_models.py`, with the old `portfolio_construction.py` copy taken at the commit before the migration (`777f502a2a^`). The two arguments the old copy does not know (`additive=True`, `algorithm=self`) are removed from the call. The two slices share no security, so `additive=True` should change nothing, and this is what the measurement checks.

A and B carry the same instrumentation, which places no order. It records the portfolio value every day at midnight, warm-up included (270 sessions). At the end of the backtest it computes a SHA-256 fingerprint per year of the orders (id, date, security, quantity, status, price) and of the recorded values.

| | A (shared module) | B (old copy) |
|---|---|---|
| Orders | 2,094 | 2,094 |
| Recorded values | 4,410 | 4,410 |
| Last recorded value | 1,408,249.00 | 1,408,249.00 |
| Sharpe (QC) | 1.148 | 1.148 |
| CAGR | 27.121% | 27.121% |
| Max drawdown | 27.6% | 27.6% |

The yearly fingerprints are equal: 12 of 12 for the orders, 13 of 13 for the values. The 27 QC statistics are equal, turnover included. The migration therefore does not change the project's behaviour. Traces kept outside the repository: `QC-traces/20188-nr/`.

## References

- Commit `fa122ae7e` (2026-03-09, jsboige + Claude Opus) — initial strategy addition, message declares "Iterated from v1.0 (Sharpe 0.622) to v1.5 (Sharpe 1.155)" — **original source of 1.155**, **no artifacts preserved**.
- `FrameworkCompositeStrategy` docstring (`main.py`) — `Allocation sweep results (2015-2026)` block, **source of the c.1284-L1 sweep-comment claim**.
- `iter4_research.py:176` — explicit warning "Simulation Sharpe typically 2-3× cloud Sharpe".
- `quantbook.ipynb` cells `In [5]`/`In [8]`/`In [9]`/`In [11]`/`In [12]` — allocation/stop-loss/rebalance/T×freq sweeps with preserved outputs.
- c.1281-L3 / c.1282-L3 / c.1283-L3 ★★ — meta-pattern misattribution 6 sisters (5 library clones + 1 sweep-comment c.1284)
- #1621 (drainage epic — real measured prose vs stale in repo)
- #9434 (drainage umbrella — multi-PR cleanup of stale READMEs)