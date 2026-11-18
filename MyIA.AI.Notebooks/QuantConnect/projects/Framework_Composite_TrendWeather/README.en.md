# Framework_Composite_TrendWeather

**Asset class:** US Equities (ETF + stocks)
**Cloud project ID:** 38458884 (course backtest space, measures of 2026-11-09)

> 🇫🇷 **Version française** : voir [`README.md`](README.md) (FR primary)
> 🇬🇧 **EN golden set** : [`README.en.md.legacy`](README.en.md.legacy) (preserved before c.1284 fix)
> 🇫🇷 **FR golden set** : [`README.fr.md`](README.fr.md) (preserved before c.1284 fix)

## Description

Composite framework combining TrendStocks (75%) with AllWeather (25%) via QuantConnect's Algorithm Framework. The trend component uses SMA200+EMA20/EMA50 on 15 large-caps (AAPL/MSFT/GOOGL/AMZN/NVDA/JPM/V/MA/UNH/JNJ/XOM/CVX/HD/PG/KO), AllWeather provides static diversification (SPY 30% / IEF 30% / GLD 30% / XLP 10%).

## QC Cloud measure (#19393, 2026-10-06)

The [#19393](https://github.com/jsboige/CoursIA/issues/19393) evaluation replayed this code in the [`TrendWeatherPointInTime`](../TrendWeatherPointInTime/) project, which keeps the signal and the construction; with `universe=fixed`, it runs this folder's rule.

- **The published figure reproduces on its window.** Over 2015-01-01 → 2025-12-31, QC Cloud returns Sharpe 1.15, CAGR 27.1% and max drawdown 27.6%. The PSR is 55.7%, not 77.9% as in the comparative register. The hypothesis of an effective Sharpe of 0.6 to 0.9, which this README used to put forward, is refuted.
- **The flaw is the list.** The 15 stocks were picked in 2026. When they are replaced each month by the 15 largest market caps known at that date, the rule loses 0.18 of Sharpe over 2018-01-01 → 2026-09-25 (1.05 against 1.22, shadow-replay series, zero risk-free rate). NVDA, in the list from 2018, carries 49% of the closed-position result of the trend pocket.
- **Pre-registered verdict: `NO BEATS`.** Against SPY held and 60/40, the Sharpe differences are positive but not significant (Holm p 0.31), and negative over 2024 → 2026-09.

Tables, diagnostics and traces: [evaluation README](../TrendWeatherPointInTime/README.md#résultats).

## Allocation sweep (#25533, 2026-11-09)

`main.py` reads the share of the trend pocket from the QC parameter `trend_alloc` (default 0.75); the AllWeather pocket takes the rest. The T60 → T80 sweep of the docstring was replayed on QC Cloud, in the course backtest space, over 2015-01-01 → 2025-12-31. The control is SPY held, with the same window, the same broker and the same starting cash (QC project 39161857).

| Allocation | Sharpe | CAGR | Max drawdown | Beta | Annual volatility | PSR |
|---|---|---|---|---|---|---|
| T60 / AW40 | 1.120 | 23.4% | 24.5% | 0.683 | 0.127 | 53.5% |
| T65 / AW35 | 1.131 | 24.7% | 25.6% | 0.711 | 0.134 | 54.5% |
| T70 / AW30 | 1.140 | 25.9% | 26.6% | 0.740 | 0.140 | 55.2% |
| **T75 / AW25 (default)** | **1.148** | **27.1%** | **27.6%** | **0.769** | **0.148** | **55.7%** |
| T80 / AW20 | 1.156 | 28.4% | 28.7% | 0.798 | 0.155 | 56.1% |
| SPY held (control, same window 2015-01-01 → 2025-12-31) | 0.537 | 13.4% | 33.5% | 0.994 | 0.147 | 2.5% |

- **The default is unchanged.** The backtest without a parameter returns the 27 statistics of the T75 backtest. It also reproduces the 2026-10-26 measure (section "Shared module non-regression" below) and the #19393 one.
- **The original docstring holds, within a small margin.** Commit `fa122ae7e` (2026-03-09) announced the same max drawdown within 0.1 point, a Sharpe higher by 0.007 to 0.010 and a CAGR higher by 0.3 to 0.4 point. Its code set no end date, so the backtest ran up to its run date. This difference of window is the likely cause of the gap; no replay has checked it.
- **These figures were first published without a traced backtest.** Before the #19393 measure and this sweep, this README treated the docstring's Sharpe of 1.155 as a claim that nothing in the repository could reproduce (drainage #9434). The backtest identifiers of the sweep are recorded in PR #25541.
- **The sweep is monotonic.** Each 5-point step toward the trend pocket adds about 0.009 of Sharpe, 1.1 point of max drawdown and 0.029 of beta. The range holds no optimum: T75 is a risk choice. The original docstring justified it by a beta that would exceed 0.80 beyond it; the measure does not confirm this, the beta stays below 0.80 up to T80 (0.798).
- **At T75, the annual volatility matches SPY held** (0.148 against 0.147). At equal volatility, the composite returns 27.1% a year against 13.4%, for a max drawdown of 27.6% against 33.5%.
- **The #19393 bias is untouched.** The list of 15 stocks was picked in 2026, and the sweep does not correct this look-ahead. The verdict against SPY held and 60/40 stays `NO BEATS`.

## Local research (different construction)

`quantbook.ipynb` (Lean CLI Docker) and `iter4_research.py` (yfinance) explore another construction than `main.py`: a 50/50 default, equal weights among rising stocks in `build_composite_weights` (`In [4]`) instead of the 3-month momentum weighting of `TrendStocksAlpha`, a weekly rebalance by default instead of 31 days, and no fees in §3. Their figures do not compare with the previous table.

| Source | Sharpe | CAGR | Max drawdown | Allocation | Period and remark |
|--------|--------|------|-------|-----------|---------|
| `iter4_research.py` (yfinance) | n/a (script) | n/a | n/a | grid 5×5×3 | 2014-2026; the script warns itself (line 176): "Simulation Sharpe is typically 2-3x cloud Sharpe" |
| `quantbook.ipynb` `In [5]` (default 50/50) | 0.680 | 10.88% | -23.53% | T50 / AW50 | 2015-2026 |
| `quantbook.ipynb` `In [8]` (allocation sweep) | 0.382 → 0.738 | 7.22% → 14.02% | -33.72% → -17.29% | T0/T10/.../T100, no T75 | 2015-2026 |
| `quantbook.ipynb` `In [9]` (stop-loss sweep) | 0.684 → 2.124 ⚠️ | 10.93% → 21.29% | -23.53% → -4.86% | T50/AW50 + stop-loss | 2015-2026; the 5% stop (2.124) is suspected of overfitting |
| `quantbook.ipynb` `In [11]` (rebalance frequency) | 0.619 → 1.070 | 9.92% → 16.13% | -23.53% → -23.94% | T50/AW50, weekly / bi-weekly / monthly | 2015-2026 |
| `quantbook.ipynb` `In [12]` (allocation × frequency, 5bps fees) | 0.544 → 1.239 | 8.90% → 19.60% | -27.88% → -19.43% | T30→T70 × W/2W/M | 2015-2026; monthly wins at every allocation |

In `In [11]`, the same strategy rebalanced monthly or weekly gives a Sharpe of 1.064 or 0.674, 5bps fees included: a less frequent rebalance reduces turnover and lets trends run. `main.py` rebalances every 31 days.

## How to Run

**Lean CLI (local research, default 50/50):** `lean research "MyIA.AI.Notebooks/QuantConnect/projects/Framework_Composite_TrendWeather" --notebook quantbook.ipynb`
**Lean CLI (`main.py` backtest):** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Framework_Composite_TrendWeather"` runs the composite at T75/AW25; `--parameter trend_alloc 0.6` changes the share of the trend pocket. The 50/50 default exists only in the quantbook.
**QC Cloud:** project 38458884 of the course backtest space, with the `SharedPCM` library attached ("Add Library", see the `SharedPCM` README). Elsewhere: create a project, attach `SharedPCM` to it, copy `main.py` and `alpha_models.py`. The `trend_alloc` parameter is set per backtest (project parameters, or the `parameters` argument of the API).

## Files

- `main.py` — Composite strategy v1.5 (T75/AW25 by default, share of the trend pocket set by the `trend_alloc` parameter, rebalance every 31 days, IBKR fees). Its class docstring carries the sweep measured on 2026-11-09.
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

- Commit `fa122ae7e` (2026-03-09, jsboige + Claude Opus) — initial strategy addition; its message declares "Iterated from v1.0 (Sharpe 0.622) to v1.5 (Sharpe 1.155)". Its sweep, with no end date, is replayed by #25533.
- `FrameworkCompositeStrategy` docstring (`main.py`) — T60 → T80 sweep measured on QC Cloud on 2026-11-09, with the SPY held control.
- [#19393](https://github.com/jsboige/CoursIA/issues/19393) — point-in-time list evaluation ([`TrendWeatherPointInTime`](../TrendWeatherPointInTime/)), verdict `NO BEATS`.
- `iter4_research.py:176` — explicit warning "Simulation Sharpe typically 2-3× cloud Sharpe".
- `quantbook.ipynb` cells `In [5]`/`In [8]`/`In [9]`/`In [11]`/`In [12]` — allocation/stop-loss/rebalance/T×freq sweeps with preserved outputs.
- #1621 (drainage epic — measured prose vs stale prose in the repo)
- #9434 (drainage umbrella — multi-PR cleanup of stale READMEs)
