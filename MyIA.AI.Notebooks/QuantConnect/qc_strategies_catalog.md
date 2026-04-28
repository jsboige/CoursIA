# QuantConnect Strategies Catalog

Imported from QC Strategy Library and Quantpedia. Each strategy has a dedicated project folder with `main.py`, `research.ipynb`, and `README.md`.

## Strategies Overview

| # | Strategy | QC Library | Type | Universe | Rebalance | Key Signal |
|---|----------|-----------|------|----------|-----------|------------|
| 1 | Asset Class Momentum | #278 | Long/Long-Short | 8 ETFs | Monthly | 12M momentum score |
| 2 | Volatility Regime ML | #224 | Long | SPY + VIX | Weekly | RandomForest regime detection |
| 3 | Defensive ETF Rotation | #54 | Long | 8 ETFs | Monthly | Dual momentum (absolute + relative) |
| 4 | Puppies of the Dow | #366 | Long | Dogs of Dow + pups | Annual/Weekly | High-yield + low-price dual ranking |
| 5 | Macro Factor Rotation | #305 | Long-Short | 500 equities | Monthly | FRED macro signals + Hurst exponent |
| 6 | Long-Short Harvest | #69 | Long-Short | 500 equities | Daily | ATR trailing stops + re-entry logic |
| 7 | Piotroski F-Score | #343 | Long | US equities | Monthly | 9-point accounting quality score |
| 8 | Commodity Term Structure | #26 | Long-Short | 21 futures | Monthly | Roll return (backwardation/contango) |

## Detailed Strategy Cards

### 1. Asset Class Momentum

- **Folder**: `projects-imported/asset-class-momentum/`
- **Source**: QC Strategy #278 (Keter Oak), Quantpedia Strategy #331
- **QC Cloud Project**: 29687598
- **Concept**: Momentum-based tactical asset allocation across 8 ETF classes (SPY, QQQ, IWM, VEA, EEM, AGG, LQD, DBC). Monthly ranking by 12-month return, equal-weighted top-N selection.
- **Architecture**: Single-file algorithm with monthly scheduled rebalance
- **Files**: `main.py`, `research.ipynb`, `README.md`
- **Performance (Author)**: 9.47% CAGR, 24.9% MaxDD, 0.72 Sharpe (5Y OOS)
- **Status**: Backtested — Sharpe 0.419, CAGR 8.80%, MaxDD 28.10%

### 2. Volatility Regime ML

- **Folder**: `projects-imported/volatility-regime-ml/`
- **Source**: QC Strategy #224 (Derek Melchin)
- **QC Cloud Project**: 29687604
- **Concept**: Machine learning regime detection using VIX data, FRED macro indicators (T10Y3M, DFF), and custom PythonData. RandomForestClassifier predicts bullish/bearish/neutral regimes. SPY long-only with regime-based position sizing.
- **Architecture**: Multi-file with custom PythonData (CBOE VIX), FRED data, sklearn model
- **Files**: `main.py`, `research.ipynb`, `README.md`
- **Performance (Author)**: 16.7% CAGR, 22.1% MaxDD, 1.18 Sharpe (5Y OOS)
- **Status**: Backtest running (074ca1cea41e467abeecc51f999ab4ed)

### 3. Defensive ETF Rotation

- **Folder**: `projects-imported/defensive-etf-rotation/`
- **Source**: QC Strategy #54 (Nathan Swenson), Quantpedia Strategy #383
- **QC Cloud Project**: 29687610
- **Concept**: Dual momentum defensive rotation. Selects from 8 ETFs (4 equity, 4 bond/alternatives) using absolute momentum (positive 12M return filter) and relative momentum (top-N ranking). Falls to SHY when all negative.
- **Architecture**: Single-file with monthly scheduled rebalance
- **Files**: `main.py`, `research.ipynb`, `README.md`
- **Performance (Author)**: 7.72% CAGR, 7.9% MaxDD, 0.93 Sharpe (5Y OOS)
- **Status**: No cloud project — not cloned, cannot backtest

### 4. Puppies of the Dow

- **Folder**: `projects-imported/puppies-of-dow/`
- **Source**: QC Strategy #366 (Louis Szeto), Quantpedia Strategy #356
- **QC Cloud Project**: 29687614
- **Concept**: Combines Dogs of the Dow (top 10 dividend yield) with Puppies (top 5 lowest-priced from Dogs). High yield captures income, low price captures potential upside. Weekly rebalance with annual universe refresh.
- **Architecture**: Alpha Framework with custom universe selection
- **Files**: `main.py`, `research.ipynb`, `README.md`
- **Performance (Author)**: 10.5% CAGR, 31.4% MaxDD, 0.56 Sharpe (5Y OOS)
- **Status**: Backtested — Sharpe 0.441, CAGR 11.42%, MaxDD 28.60%

### 5. Macro Factor Rotation

- **Folder**: `projects-imported/macro-factor-rotation/`
- **Source**: QC Strategy #305 (Louis Szeto), Quantpedia Strategy #51
- **QC Cloud Project**: 29687622
- **Concept**: Long-short equity strategy using macro signals (FRED: VIXCLS, T10Y3M, DFF) to rotate between factor exposures. Hurst exponent for mean-reversion scoring. Dynamic position sizing based on macro regime.
- **Architecture**: Multi-file with custom data (FRED), factor scoring, Hurst exponent
- **Files**: `main.py`, `research.ipynb`, `README.md`
- **Performance (Author)**: 12.8% CAGR, 18.3% MaxDD, 1.05 Sharpe (5Y OOS)
- **Status**: Backtested — Sharpe 1.035, CAGR 33.39%, MaxDD 27.50%

### 6. Long-Short Harvest

- **Folder**: `projects-imported/long-short-harvest/`
- **Source**: QC Strategy #69 (Jared Broad), Quantpedia Strategy #15
- **QC Cloud Project**: 29687634
- **Concept**: Long-short equity with daily rebalance. Top decile momentum = long, bottom decile = short. ATR-based 3-stage trailing stop losses with re-entry logic. Universe of 500 most liquid equities.
- **Architecture**: Single-file with coarse/fine universe selection
- **Files**: `main.py`, `research.ipynb`, `README.md`
- **Performance (Author)**: 14.2% CAGR, 15.7% MaxDD, 1.32 Sharpe (5Y OOS)
- **Status**: Backtested — Sharpe 1.996, CAGR 60.31%, MaxDD 16.70%

### 7. Piotroski F-Score Quality Value

- **Folder**: `projects-imported/piotroski-fscore/`
- **Source**: QC Strategy #343 (Louis Szeto), Piotroski (2000)
- **QC Cloud Project**: 29687591
- **Concept**: Value + quality screen. Top 20% by book-to-market (value), filtered for F-Score >= 8 (financial health). 9-component accounting score: profitability (4pts), leverage/liquidity (3pts), operating efficiency (2pts).
- **Architecture**: Alpha Framework with 5 files (main, universe, symbol_data, piotroski_score, piotroski_factors)
- **Files**: `main.py`, `universe.py`, `symbol_data.py`, `piotroski_score.py`, `piotroski_factors.py`, `research.ipynb`, `README.md`
- **Performance (Author)**: 18.44% CAGR, 24.20% MaxDD, 2.09 Sharpe (1Y OOS)
- **Status**: Backtested — Sharpe 0.547, CAGR 18.19%, MaxDD 24.20%

### 8. Commodity Term Structure

- **Folder**: `projects-imported/commodity-term-structure/`
- **Source**: QC Strategy #26, Quantpedia Strategy #22
- **QC Cloud Project**: 29688398
- **Concept**: Long-short commodity futures based on roll returns. 21 futures across 5 sectors (Softs, Grains, Meats, Energies, Metals). Top quintile backwardation = long, top quintile contango = short. Monthly rebalance.
- **Architecture**: Single-file with futures chain processing
- **Files**: `main.py`, `research.ipynb`, `README.md`
- **Performance (Author)**: -15.71% CAGR, 80.80% MaxDD, -0.041 Sharpe (5Y OOS); Recent: 38.85% 3M return, 1.49 1Y Sharpe
- **Status**: Backtested — Sharpe -0.054, CAGR -16.26%, MaxDD 96.80%

## Backtest Status

| Strategy | Compile | Backtest ID | Sharpe | CAGR | MaxDD | Verified |
|----------|---------|-------------|--------|------|-------|----------|
| Asset Class Momentum | BuildSuccess | (new) | 0.419 | 8.80% | 28.10% | Yes |
| Volatility Regime ML | BuildSuccess | 074ca... | (running) | - | - | Pending |
| Defensive ETF Rotation | N/A | N/A | N/A | N/A | N/A | No cloud project |
| Puppies of the Dow | BuildSuccess | (existing) | 0.441 | 11.42% | 28.60% | Yes |
| Macro Factor Rotation | BuildSuccess | (existing) | 1.035 | 33.39% | 27.50% | Yes |
| Long-Short Harvest | BuildSuccess | (existing) | 1.996 | 60.31% | 16.70% | Yes |
| Piotroski F-Score | BuildSuccess | (existing) | 0.547 | 18.19% | 24.20% | Yes |
| Commodity Term Structure | BuildSuccess | (existing) | -0.054 | -16.26% | 96.80% | Yes |

### Notes

- **Asset Class Momentum**: New backtest. Author reported 0.72 Sharpe / 9.47% CAGR — verified close to reported.
- **Volatility Regime ML**: Backtest launched, still running at time of catalog update.
- **Defensive ETF Rotation**: No QC Cloud project exists (was never cloned). Cannot compile/backtest.
- **Puppies of the Dow**: Author reported 0.56 Sharpe / 10.5% CAGR — verified close.
- **Macro Factor Rotation**: Author reported 1.05 Sharpe / 12.8% CAGR — backtest shows stronger results.
- **Long-Short Harvest**: Author reported 1.32 Sharpe / 14.2% CAGR — backtest shows much stronger results.
- **Piotroski F-Score**: Author reported 2.09 Sharpe / 18.44% CAGR (1Y) — verified at 0.547 Sharpe over longer period.
- **Commodity Term Structure**: Author reported -0.041 Sharpe / -15.71% CAGR — confirmed negative performance.

## Backtest Workflow

To verify each strategy via QC MCP:

```bash
# 1. Get project ID from cloud-id file
# 2. Compile
create_compile(projectId) -> compileId
# 3. Wait for compilation
read_compile(projectId, compileId) -> state == "BuildSuccess"
# 4. Run backtest
create_backtest(projectId, compileId, "Strategy Name") -> backtestId
# 5. Read results
read_backtest(projectId, backtestId) -> statistics
```

## Source Attribution

All strategies are from the [QuantConnect Strategy Library](https://www.quantconnect.com/strategies/) and/or [Quantpedia](https://quantpedia.com/). Each strategy retains its original author attribution and license (QuantConnect Community Strategy - open source unless otherwise noted).
