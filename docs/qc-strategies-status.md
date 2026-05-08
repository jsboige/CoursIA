# QC Strategies Status — Classification & Priorities

Generated: 2026-05-07 | Source: issue #29, cycle 5 Track G analysis

## Categories

### BROKEN_PEDAGOGICAL — Intentional failure demonstrations

Strategies that fail for structural/structural reasons. Kept as teaching tools.

| # | Strategy | Sharpe | Reason | Lesson |
|---|----------|--------|--------|--------|
| 17 | ForexCarry | -0.654 | FX carry dead post-2008 ZIRP/QE | Structural regime failure |
| 18 | VIX-TermStructure | -0.27 | SVXY ETN terminated 2018 | Structural product risk |

Label: `pedagogical:broken-intentional`

### BROKEN_TO_FIX — Genuine bugs requiring diagnosis

| # | Strategy | Issue | Fix effort | Status |
|---|----------|-------|------------|--------|
| 34 | Crypto-MultiCanal | `find_envelope_line` import error, 0 trades | LOW | Open |
| — | Trend-Following | Timeout: 200 stocks x 11yr hourly | MEDIUM | Not yet issued |
| — | Stoploss-Volatility-ML | CBOE data unavailable (#233) | MEDIUM | Not yet issued |
| — | Clustering-Fundamentals-ML | Runtime error | LOW | Not yet issued |

Label: `bug`, `priority-medium`

### NEEDS_IMPROVEMENT (Sharpe 0-0.5)

| # | Strategy | Sharpe v0 | Sharpe v1 | Status |
|---|----------|-----------|-----------|--------|
| 19 | MeanReversion | -0.042 | 0.294 | IMPROVED |
| 20 | FuturesTrend | 0.019 | 0.280 | IMPROVED |
| 21 | TurnOfMonth | 0.127 | 0.127 | CEILING |
| 22 | MomentumStrategy | 0.216 | 0.411 | IMPROVED |
| 23 | AllWeather | 0.25 | 0.365 | IMPROVED |
| 25 | FamaFrench | 0.365 | 0.471 | IMPROVED |

### HEALTHY (Sharpe > 0.5)

| # | Strategy | Sharpe | Status |
|---|----------|--------|--------|
| 24 | OptionsIncome | 0.747 | HEALTHY |
| 26 | Sector-Momentum | 0.554 | HEALTHY |
| 32 | BTC-MACD-ADX | 1.224 | HEALTHY |
| 33 | Multi-Layer-EMA | 1.891 | HEALTHY |

### NO_BACKTEST — Never evaluated

6 ML projects + 10 ESGF course projects. Require initial backtest before categorization.

## Actions taken (Cycle 6 Track B)

- Created `pedagogical:broken-intentional` label (color: #FFCC00)
- Applied to #17 (ForexCarry), #18 (VIX-TermStructure)
- Applied `bug` + `priority-medium` to #34 (Crypto-MultiCanal)
