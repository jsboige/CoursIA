# Markov-Regime-Detection

**Asset class:** US Equities/ETF (SPY, TLT, GLD)
**Cloud project ID:** `36387308`

## Description

Markov regime detection using statsmodels MarkovRegression. Identifies 2-regime (bull/bear) states on SPY returns, rotates monthly between SPY (calm regime) and TLT (turbulent regime), with a constant 10% GLD sleeve.

**Consolidated from ML-HMM-Regime** (near-identical copy with same class name, same k_regimes=2, same allocation logic).

## Fear & Greed overlay (v1.2, #15534)

The project consolidates QuantConnect research article [#19465](https://www.quantconnect.com/research/19465/filtering-trades-with-the-fear-and-greed-index/) as an **optional overlay**, gated by the `use_feargreed` parameter (default `0` = v1.1 behavior strictly unchanged).

**Primary source**: Huang, Jiang, Tu & Zhou (2015), "Investor Sentiment Aligned: A Powerful Predictor of Stock Returns", *Review of Financial Studies* 28(3), 791-837 — aligned investor sentiment as a powerful return predictor. The QuantConnect article remains the operational entry point; this reference is its primary academic source.

**Mechanism**: the same tool as the main regime (`MarkovRegression`, `k_regimes=2`) is fit on the trailing Fear & Greed history, and SPY exposure is **halved** when the SPY regime asks for risk but the index regime sits in its greedy state (the remainder stays in cash — never TLT, which would blend two regime signals). The greedy state is identified by its **higher fitted mean**, never by a hardcoded regime number, so a regime renumbering across fits cannot silently flip the filter.

**Dataset**: `FearGreedIndex`, exposed by the `AlgorithmImports` wildcard (no explicit import), ticker `"FG"`. Availability probed on QC Cloud 2026-09-11: >= 2500 daily rows delivered through Dec 2025, coverage from July 2014, not gated.

**Seeds**: the article's seed sweep (30-50) has no object here — the article drew random trades, whereas this strategy is a deterministic monthly rotation whose `MarkovRegression` fit depends on no seed. Robustness is therefore tested by **market sub-periods** instead.

## How to Run

**QC Cloud:** project `36387308` (public). v1.2 strategy parameters: `use_feargreed` (0/1), `start_year`/`end_year`, `lookback_years` (default 3).
v1.3 arm parameters: `arm` (`markov` by default, `article`, `fixed`, `static`, `spy`), `seed` (default 0), `start_date`/`end_date` (default: the article's window), `static_gld` (default 0.545), `history_lookback` (default 50 weeks), `drawdown_lookback` (default 20 weeks).
**v1.3 measurements:** `python bench_drawdown_hmm.py fetch|stats|markdown` (QC credentials read from the `QC_API_USER_ID` and `QC_API_ACCESS_TOKEN` environment variables).
**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Markov-Regime-Detection"`

## Backtest Metrics

Measured 2026-09-11 on QC Cloud, Interactive Brokers fees kept in both arms (unlike the article, which removed them via `ConstantFeeModel(0)`), monthly rebalance. Arm A is the baseline (`use_feargreed=0`), arm B the variant (`use_feargreed=1`); each window is an independent run (not a slice of the full run), since the 3-year warm-up and the regime state are not carried across windows.

| Window | Arm | Sharpe | CAGR | MaxDD | Net profit | Net profit ($) | PSR | Orders |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| 2015-2026 | A — baseline | 0.290 | 7.182% | 23.700% | 114.572% | 74,574.09 | 0.197% | 103 |
| 2015-2026 | B — variant | 0.019 | 3.318% | 26.300% | 43.243% | 23,093.34 | 0.004% | 105 |
| IS 2015-2020 | A — baseline | 0.229 | 4.735% | 16.700% | 26.038% | 14,496.06 | 1.859% | 44 |
| IS 2015-2020 | B — variant | 0.051 | 2.653% | 14.500% | 13.996% | 7,532.51 | 0.526% | 45 |
| OOS 2021-2026 | A — baseline | 0.297 | 8.991% | 23.700% | 53.825% | 26,626.13 | 2.596% | 41 |
| OOS 2021-2026 | B — variant | -0.123 | 3.278% | 22.500% | 17.510% | 2,344.36 | 0.121% | 42 |

**Verdict: NO BEATS in all three windows.** The overlay degrades Sharpe (to negative out-of-sample), CAGR and net profit everywhere. The one metric where B does better is IS drawdown (14.500% against 16.700%), a mechanical consequence of halved exposure rather than a better signal. The order count is nearly identical within each window (103/105, 44/45, 41/42), the expected behavior of an overlay that only changes the **exposure weight** and never the decision frequency — turnover is not exposed by the reading tool (qc-mcp-lite maps six statistics), so the order count is the declared proxy.

## Drawdown-regime gold hedge (v1.3, #17589)

The project consolidates QuantConnect research article [#18811](https://www.quantconnect.com/research/18811/optimizing-a-gold-spy-portfolio-using-hidden-markov-models-for-market-downtime/) (Louis Szeto) as **optional arms**, selected by the `arm` parameter. The default `arm=markov` runs the v1.2 strategy unchanged: the v1.3 branch leaves `initialize` before the v1.2 setup, and the `main.py` diff contains insertions only.

**Article mechanism**: at the start of each week, a `GMMHMM` (hmmlearn) with 2 states, 3 mixture components per state and `tied` covariance is fit on two inputs drawn from 50 weeks of SPY closes: the 20-week rolling drawdown and its first difference. The GLD weight is the probability that next week is in the "high" state, and SPY takes the rest. $1M account, minute data, default platform fees (Interactive Brokers model), kept in every arm.

**Primary sources**:

- Rabiner, L. R. (1989). *A tutorial on hidden Markov models and selected applications in speech recognition*. Proceedings of the IEEE 77(2), 257-286: hidden Markov model, forward-backward algorithm.
- McLachlan, G. J. & Peel, D. (2000). *Finite Mixture Models*. Wiley: finite Gaussian mixtures, cited by the article to approximate a non-Gaussian distribution.
- Balkema, A. A. & de Haan, L. (1974). *Residual life time at great age*. Annals of Probability 2(5), 792-804; Pickands, J. (1975). *Statistical inference using extreme order statistics*. Annals of Statistics 3(1), 119-131. The Pickands-Balkema-de Haan theorem motivates a generalized Pareto law for threshold exceedances, hence a non-Gaussian tail for drawdowns. It motivates the shape of the law, not the SPY/GLD allocation, which remains the article's own contribution.
- Ledoit, O. & Wolf, M. (2008). *Robust performance hypothesis testing with the Sharpe ratio*. Journal of Empirical Finance 15(5), 850-859: autocorrelation-robust (HAC) test of a Sharpe ratio difference, used for the comparisons below.

**Four arms**, to isolate what each piece contributes:

| `arm` | What it measures |
|---|---|
| `article` | faithful port, state labeling included |
| `fixed` | same model and sizing; the "high" state is the one whose mixture-weighted mean drawdown is the lowest (the deepest) |
| `static` | constant GLD weight (`static_gld`) on the same weekly schedule. Two controls: 0.545, the mean GLD weight realized by the `article` arm, and 0.450, that of the `fixed` arm (means over 5 seeds, full window). At equal mean exposure, the control separates *timing* from a plain gold allocation |
| `spy` | SPY buy-and-hold, same account and schedule |

The HMM arms run on seeds 0, 1, 7, 42 and 99 (`seed`, which replaces the article's `random_state=0`; seed 0 is the article).

**State labeling in the article's code**: `high_regime = 1 if model.means_[0][1][0] < model.means_[1][1][0] else 0`. `means_` has shape `(states, components, features)`: the comparison reads **mixture component 1** of each state, whose order is arbitrary at each fit, and keeps the state with the **higher** mean. Since a drawdown is negative or zero, that state is the one with the **shallower** drawdown. The `fixed` arm corrects both points; at each fit `main.py` counts whether the two labels agree (runtime statistic `Label agreement`).

### Measurement protocol

- **Reproduction**: with its default parameters (the article's window, 2019-01-03 to 2025-01-01), the `article` arm returns a QC Sharpe of 0.824, against 0.823 published in the article.
- **Extended window**: each arm then runs from 2008-01-01 to 2026-09-01. The article's window becomes a sub-period (in-sample, since the method was presented on it), framed by two out-of-sample periods: 2008-2018, which covers the 2008 crisis, and 2025-2026.
- **Monthly returns**: every month `main.py` plots the portfolio, SPY and GLD returns, along with the mean net exposure and GLD weight; `bench_drawdown_hmm.py fetch` reads them back from the platform. LEAN pays no interest on cash: the excess return is `R − net exposure × rf`, with rf the 3-month Treasury bill rate (FRED series TB3MS).
- **Tests**: annualized Sharpe difference against SPY and against the static control of the same family, Ledoit-Wolf HAC test per seed; CAPM alpha with Newey-West standard errors; five chronological folds of equal length (descriptive walk-forward: the model is refit every week on a rolling window, no parameter is calibrated on the tested period).
- **Verdict rule**: BEATS requires a positive mean difference larger than two cross-seed standard deviations **and** differences significant at 5%; NO BEATS when the difference is negative or null across seeds; INCONCLUSIVE otherwise.

### Results

Platform statistics, one backtest per row:

| QC backtest | parameters | Sharpe | CAGR | MaxDD | orders | fees |
|---|---|---:|---:|---:|---:|---:|
| `repro_article_s0` | arm=article, seed=0 | 0.824 | 19.751% | 27.100% | 414 | $4118.01 |
| `spy` | arm=spy, end_date=2026-09-01, start_date=2008-01-01 | 0.451 | 11.418% | 51.300% | 3 | $51.55 |
| `article_s0` | arm=article, end_date=2026-09-01, seed=0, start_date=2008-01-01 | 0.42 | 10.392% | 44.900% | 1297 | $17972.98 |
| `article_s1` | arm=article, end_date=2026-09-01, seed=1, start_date=2008-01-01 | 0.405 | 10.147% | 47.700% | 1281 | $14108.70 |
| `article_s7` | arm=article, end_date=2026-09-01, seed=7, start_date=2008-01-01 | 0.351 | 8.594% | 35.200% | 1749 | $27101.77 |
| `article_s42` | arm=article, end_date=2026-09-01, seed=42, start_date=2008-01-01 | 0.441 | 10.593% | 30.000% | 1651 | $34640.75 |
| `article_s99` | arm=article, end_date=2026-09-01, seed=99, start_date=2008-01-01 | 0.379 | 9.701% | 47.700% | 1109 | $10440.29 |
| `fixed_s0` | arm=fixed, end_date=2026-09-01, seed=0, start_date=2008-01-01 | 0.491 | 10.637% | 48.700% | 1284 | $18882.27 |
| `fixed_s1` | arm=fixed, end_date=2026-09-01, seed=1, start_date=2008-01-01 | 0.466 | 10.253% | 37.600% | 1268 | $20639.31 |
| `fixed_s7` | arm=fixed, end_date=2026-09-01, seed=7, start_date=2008-01-01 | 0.45 | 9.931% | 46.600% | 1748 | $28059.23 |
| `fixed_s42` | arm=fixed, end_date=2026-09-01, seed=42, start_date=2008-01-01 | 0.434 | 9.690% | 45.500% | 1645 | $25270.37 |
| `fixed_s99` | arm=fixed, end_date=2026-09-01, seed=99, start_date=2008-01-01 | 0.483 | 10.670% | 38.400% | 1100 | $15354.37 |
| `static_article` | arm=static, end_date=2026-09-01, start_date=2008-01-01, static_gld=0.545 | 0.535 | 10.666% | 32.100% | 1456 | $1562.34 |
| `static_fixed` | arm=static, end_date=2026-09-01, start_date=2008-01-01, static_gld=0.45 | 0.545 | 10.937% | 34.100% | 1457 | $1563.25 |

Annualized excess Sharpe, computed on monthly returns; mean differences over the 5 seeds, ± cross-seed standard deviation, and number of seeds whose difference is positive and significant at 5%:

| Window | months | SPY/GLD corr. | spy | static 0.545 | static 0.450 | article (mean of 5 seeds) | fixed (mean of 5 seeds) | Δ article − spy (mean ± σ across seeds) | Δ article − static 0.545 (mean ± σ) | Δ fixed − static 0.450 (mean ± σ) |
|---|---:|---:|---:|---:|---:|---:|---:|---|---|---|
| 2008-01 → 2026-08 (all) | 224 | 0.08 | 0.69 | 0.79 | 0.82 | 0.61 | 0.66 | −0.08 ± 0.04 (0/5 p<0.05) | −0.18 ± 0.04 (0/5 p<0.05) | −0.16 ± 0.03 (0/5 p<0.05) |
| 2008-01 → 2018-12 (out-of-sample, before the article) | 132 | 0.01 | 0.53 | 0.51 | 0.56 | 0.29 | 0.52 | −0.24 ± 0.09 (0/5 p<0.05) | −0.22 ± 0.09 (0/5 p<0.05) | −0.03 ± 0.08 (0/5 p<0.05) |
| 2019-01 → 2024-12 (article window, in-sample) | 72 | 0.23 | 0.86 | 1.02 | 1.02 | 0.98 | 0.70 | 0.12 ± 0.21 (0/5 p<0.05) | −0.04 ± 0.21 (0/5 p<0.05) | −0.33 ± 0.12 (0/5 p<0.05) |
| 2025-01 → 2026-08 (out-of-sample, after the article) | 20 | 0.03 | 1.10 | 1.69 | 1.73 | 1.36 | 1.63 | 0.27 ± 0.27 (0/5 p<0.05) | −0.34 ± 0.27 (0/5 p<0.05) | −0.11 ± 0.39 (0/5 p<0.05) |

Five chronological folds of equal length (excess Sharpe, mean of the 5 seeds for the HMM arms):

| Fold | spy | static 0.545 | static 0.450 | article | fixed |
|---|---:|---:|---:|---:|---:|
| 2008-01 → 2011-09 | −0.11 | 0.61 | 0.48 | 0.33 | 0.60 |
| 2011-10 → 2015-06 | 1.80 | 0.38 | 0.65 | 0.46 | 0.29 |
| 2015-07 → 2019-03 | 0.85 | 0.69 | 0.81 | 0.24 | 0.72 |
| 2019-04 → 2022-12 | 0.54 | 0.73 | 0.71 | 0.78 | 0.36 |
| 2023-01 → 2026-08 | 1.32 | 1.64 | 1.70 | 1.34 | 1.61 |

Exposure and CAPM alpha over the full window:

| Arm (full window) | mean GLD weight | CAGR | monthly MaxDD | annualized CAPM alpha (NW t) | SPY beta |
|---|---:|---:|---:|---:|---:|
| `article_s0` | 0.56 | 10.6% | 39.1% | 3.2% (1.09) | 0.64 |
| `article_s1` | 0.54 | 10.3% | 42.3% | 2.7% (0.96) | 0.67 |
| `article_s42` | 0.54 | 10.8% | 22.3% | 4.0% (1.32) | 0.57 |
| `article_s7` | 0.54 | 8.8% | 26.4% | 3.0% (1.17) | 0.48 |
| `article_s99` | 0.55 | 9.9% | 45.5% | 2.7% (0.92) | 0.62 |
| `fixed_s0` | 0.44 | 10.7% | 42.1% | 5.2% (1.68) | 0.44 |
| `fixed_s1` | 0.46 | 10.3% | 33.5% | 5.1% (1.74) | 0.41 |
| `fixed_s42` | 0.46 | 9.7% | 37.9% | 3.7% (1.28) | 0.50 |
| `fixed_s7` | 0.45 | 10.0% | 43.3% | 3.9% (1.34) | 0.50 |
| `fixed_s99` | 0.45 | 10.7% | 34.4% | 5.0% (1.52) | 0.46 |
| `spy` | 0.00 | 11.5% | 46.1% | 0.2% (1.05) | 0.99 |
| `static_article` | 0.54 | 10.8% | 24.7% | 4.4% (2.14) | 0.50 |
| `static_fixed` | 0.45 | 11.0% | 25.8% | 3.7% (2.17) | 0.58 |

Regime-model diagnostics (identical for `article` and `fixed`, which fit the same model with the same seed):

| Seed | fits | swallowed failures | article label = deep-drawdown state |
|---|---:|---:|---:|
| 0 | 970 | 4 | 6.7% |
| 1 | 973 | 1 | 5.1% |
| 7 | 972 | 2 | 20.1% |
| 42 | 956 | 18 | 13.8% |
| 99 | 967 | 7 | 1.2% |

**Verdicts**:

- **Full window (2008-2026): NO BEATS**, against SPY as against static gold. All ten HMM backtests have a lower excess Sharpe than their static control: from −0.13 to −0.22 for `article`, from −0.12 to −0.19 for `fixed`. No individual difference is significant at 5% (p from 0.07 to 0.43), but the sign does not depend on the seed. Against SPY, the differences are negative or null (−0.08 ± 0.04 and −0.03 ± 0.03).
- **Article window (2019-2024): INCONCLUSIVE** against SPY for `article` (+0.12 ± 0.21, from −0.23 to +0.29 depending on the seed, none significant): the published edge reproduces with the article's seed but does not survive a change of seed. Against the static control the mean difference is −0.04: on its own window, the strategy's edge comes from the gold share, not from the timing.
- **Out-of-sample before the article (2008-2018): NO BEATS** (`article` −0.24 ± 0.09 against SPY, negative on all five seeds).
- **Out-of-sample after the article (2025-2026, 20 months): INCONCLUSIVE** against SPY (+0.27 ± 0.27 for `article`, +0.54 ± 0.39 for `fixed`, no seed significant over such a short period), and negative against the static control (−0.34 and −0.11 on average).

**What the article's labeling measures**: the article's label designates the deep-drawdown state in only 1.2% to 20.1% of the fits depending on the seed. In the vast majority of weeks, the GLD weight is therefore the probability of the **shallow**-drawdown state: the strategy buys gold in calm markets, the opposite of the stated intent. Fixing the label (`fixed`) improves the full-window excess Sharpe (0.66 against 0.61 on average) without catching up with the static control.

**Where the return comes from**: the CAPM alpha of the HMM arms (2.7% to 5.2% per year, Newey-West t below 1.8) is of the same order as that of the two static controls (4.4% and 3.7%, the only ones with t > 2). Holding gold, weakly correlated with SPY over the period (monthly correlation 0.08), carries the performance. The timing costs: nearly binary weights from one week to the next raise the monthly MaxDD (22% to 45% against 25% to 26% for the controls) and multiply fees ($10k to $35k against $1.6k for static gold). The lower SPY beta of the `fixed` arm (0.41 to 0.50 against 0.58 for its control) is the expected effect of retreating to gold during drawdowns, but it does not offset the added volatility.

**Limits**: the difference tests run on monthly returns (224 months); at most 18 fits per backtest fail and are swallowed as in the article, which then keeps the previous week's positions ("swallowed failures" column).

## Files

- `main.py` - Strategy (v1.3: Markov regime + optional Fear & Greed overlay + drawdown-regime gold hedge arms)
- `bench_drawdown_hmm.py` - Reads the v1.3 backtests back, computes the statistics and the tables of this page
- `measures/` - Backtest IDs, QC statistics, monthly returns and test summary
- `README.md` - French version
