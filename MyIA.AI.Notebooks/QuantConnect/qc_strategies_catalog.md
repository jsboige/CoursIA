# QuantConnect Strategies Catalog

Imported from QC Strategy Library and Quantpedia. Each strategy has a dedicated project folder with `main.py`, `research.ipynb`, and `README.md`.

## Strategies Overview

| # | Strategy | QC Library | Type | Universe | Rebalance | Key Signal |
|---|----------|-----------|------|----------|-----------|------------|
| 1 | Asset Class Momentum | #278 | Long/Long-Short | 8 ETFs | Monthly | 12M momentum score |
| 2 | Volatility Regime ML | #224 | Long | SPY + VIX | Weekly | RandomForest regime detection |
| 3 | Defensive ETF Rotation | #54 | Long | 8 ETFs | Monthly | Dual momentum (absolute + relative) |
| 4 | Puppies of the Dow | #366 | Long | Dogs of Dow + pups | Annual/Weekly | High-yield + low-price dual ranking |
| 5 | Macro Factor Rotation | #72 | Long | 4 assets (SPY/GLD/BND/BTC) | Monthly | DecisionTreeRegressor + FRED macro factors |
| 6 | Long-Short Harvest | #69 | Long-Short | 500 equities | Daily | ATR trailing stops + re-entry logic |
| 7 | Piotroski F-Score | #343 | Long | US equities | Monthly | 9-point accounting quality score |
| 8 | Commodity Term Structure | #26 | Long-Short | 21 futures | Monthly | Roll return (backwardation/contango) |

## Detailed Strategy Cards

### 1. Asset Class Momentum

- **Folder**: `projects-imported/asset-class-momentum/`
- **Source**: QC Strategy #278 (Keter Oak), Quantpedia Strategy #331
- **QC Cloud Project**: 29687233 (harmonized)
- **Concept**: Momentum-based tactical asset allocation across 8 ETF classes (SPY, QQQ, IWM, VEA, EEM, AGG, LQD, DBC). Monthly ranking by 12-month return, equal-weighted top-N selection.
- **Architecture**: Single-file algorithm with monthly scheduled rebalance
- **Files**: `main.py`, `research.ipynb`, `README.md`
- **Performance (Author)**: 9.47% CAGR, 24.9% MaxDD, 0.72 Sharpe (5Y OOS)
- **Harmonized Backtest (2007-2026)**: Sharpe 0.153, CAGR 4.76%, MaxDD 55.3%

### 2. Volatility Regime ML

- **Folder**: `projects-imported/volatility-regime-ml/`
- **Source**: QC Strategy #224 (Derek Melchin)
- **QC Cloud Project**: 29687293 (harmonized)
- **Concept**: Machine learning regime detection using VIX data, FRED macro indicators (T10Y3M, DFF), and custom PythonData. RandomForestClassifier predicts bullish/bearish/neutral regimes. SPY long-only with regime-based position sizing.
- **Architecture**: Multi-file with custom PythonData (CBOE VIX), FRED data, sklearn model
- **Files**: `main.py`, `research.ipynb`, `README.md`
- **Performance (Author)**: 16.7% CAGR, 22.1% MaxDD, 1.18 Sharpe (5Y OOS)
- **Harmonized Backtest (2008-2026)**: Sharpe 1.29, CAGR 24.99%, MaxDD 19.1%

### 3. Defensive ETF Rotation

- **Folder**: `projects-imported/defensive-etf-rotation/`
- **Source**: QC Strategy #54 (Nathan Swenson), Quantpedia Strategy #383
- **QC Cloud Project**: 29687610 (not cloned — cannot backtest)
- **Concept**: Dual momentum defensive rotation. Selects from 8 ETFs (4 equity, 4 bond/alternatives) using absolute momentum (positive 12M return filter) and relative momentum (top-N ranking). Falls to SHY when all negative.
- **Architecture**: Single-file with monthly scheduled rebalance
- **Files**: `main.py`, `research.ipynb`, `README.md`
- **Performance (Author)**: 7.72% CAGR, 7.9% MaxDD, 0.93 Sharpe (5Y OOS)
- **Status**: No cloud project — not cloned, cannot backtest

### 4. Puppies of the Dow

- **Folder**: `projects-imported/puppies-of-dow/`
- **Source**: QC Strategy #366 (Louis Szeto), Quantpedia Strategy #356
- **QC Cloud Project**: 29687759 (harmonized)
- **Concept**: Combines Dogs of the Dow (top 10 dividend yield) with Puppies (top 5 lowest-priced from Dogs). High yield captures income, low price captures potential upside. Annual universe refresh via DIA ETF.
- **Architecture**: ETF universe with fundamental screening, annual rebalance
- **Files**: `main.py`, `research.ipynb`, `README.md`
- **Performance (Author)**: 10.5% CAGR, 31.4% MaxDD, 0.56 Sharpe (5Y OOS)
- **Harmonized Backtest (2005-2026)**: Sharpe 0.386, CAGR 10.86%, MaxDD 54.2%

### 5. Macro Factor Rotation

- **Folder**: `projects-imported/macro-factor-rotation/`
- **Source**: QC Strategy #72 (Derek Melchin)
- **QC Cloud Project**: 29687828 (harmonized)
- **Concept**: Macro factor driven cross-asset rotation: SPY, GLD, BND, BTCUSD. Uses VIX, 10Y-3M yield curve, fed funds rate as ML features. DecisionTreeRegressor with monthly retraining, 150% gross exposure, BTC capped 10%.
- **Architecture**: Single-file with sklearn DecisionTreeRegressor, FRED data
- **Files**: `main.py`, `research.ipynb`, `README.md`
- **Performance (Author)**: 33.45% CAGR, 27.60% MaxDD, 1.23 Sharpe (5Y OOS)
- **Harmonized Backtest (2013-2026)**: Sharpe 0.927, CAGR 27.20%, MaxDD 41.9%

### 6. Long-Short Harvest

- **Folder**: `projects-imported/long-short-harvest/`
- **Source**: QC Strategy #69 (Jared Broad), Quantpedia Strategy #15
- **QC Cloud Project**: 29687399 (harmonized)
- **Concept**: Long-short equity with daily rebalance. Top decile momentum = long, bottom decile = short. ATR-based 3-stage trailing stop losses with re-entry logic. Universe of 500 most liquid equities.
- **Architecture**: Single-file with coarse/fine universe selection
- **Files**: `main.py`, `research.ipynb`, `README.md`
- **Performance (Author)**: 14.2% CAGR, 15.7% MaxDD, 1.32 Sharpe (5Y OOS)
- **Harmonized Backtest (2005-2026)**: Sharpe 1.505, CAGR 40.15%, MaxDD 16.7%

### 7. Piotroski F-Score Quality Value

- **Folder**: `projects-imported/piotroski-fscore/`
- **Source**: QC Strategy #343 (Louis Szeto), Piotroski (2000)
- **QC Cloud Project**: 29687591 (harmonized)
- **Concept**: Value + quality screen. Top 20% by book-to-market (value), filtered for F-Score >= 8 (financial health). 9-component accounting score: profitability (4pts), leverage/liquidity (3pts), operating efficiency (2pts).
- **Architecture**: Alpha Framework with 5 files (main, universe, symbol_data, piotroski_score, piotroski_factors)
- **Files**: `main.py`, `universe.py`, `symbol_data.py`, `piotroski_score.py`, `piotroski_factors.py`, `research.ipynb`, `README.md`
- **Performance (Author)**: 18.44% CAGR, 24.20% MaxDD, 2.09 Sharpe (1Y OOS)
- **Harmonized Backtest (2005-2026)**: Sharpe 0.362, CAGR 11.82%, MaxDD 60.3%

### 8. Commodity Term Structure

- **Folder**: `projects-imported/commodity-term-structure/`
- **Source**: QC Strategy #26, Quantpedia Strategy #22
- **QC Cloud Project**: 29688398 (harmonized)
- **Concept**: Long-short commodity futures based on roll returns. 21 futures across 5 sectors (Softs, Grains, Meats, Energies, Metals). Top quintile backwardation = long, top quintile contango = short. Monthly rebalance.
- **Architecture**: Single-file with futures chain processing
- **Files**: `main.py`, `research.ipynb`, `README.md`
- **Performance (Author)**: -15.71% CAGR, 80.80% MaxDD, -0.041 Sharpe (5Y OOS); Recent: 38.85% 3M return, 1.49 1Y Sharpe
- **Harmonized Backtest (2005-2026)**: Sharpe 0.009, CAGR -11.39%, MaxDD 97.5% (variable scoping bug fixed)

## Backtest Status (Harmonized Periods)

| Strategy | Project ID | Period | Compile | Sharpe | CAGR | MaxDD | Status |
|----------|-----------|--------|---------|--------|------|-------|--------|
| Asset Class Momentum | 29687233 | 2007-2026 | BuildSuccess | 0.153 | 4.76% | 55.3% | Verified |
| Volatility Regime ML | 29687293 | 2008-2026 | BuildSuccess | 1.29 | 24.99% | 19.1% | Verified |
| Defensive ETF Rotation | N/A | N/A | N/A | N/A | N/A | N/A | No cloud project |
| Puppies of the Dow | 29687759 | 2005-2026 | BuildSuccess | 0.386 | 10.86% | 54.2% | Verified |
| Macro Factor Rotation | 29687828 | 2013-2026 | BuildSuccess | 0.927 | 27.20% | 41.9% | Verified |
| Long-Short Harvest | 29687399 | 2005-2026 | BuildSuccess | 1.505 | 40.15% | 16.7% | Verified |
| Piotroski F-Score | 29687591 | 2005-2026 | BuildSuccess | 0.362 | 11.82% | 60.3% | Verified |
| Commodity Term Structure | 29688398 | 2005-2026 | BuildSuccess | 0.009 | -11.39% | 97.5% | Verified |

### Notes

- **Asset Class Momentum**: Author reported 0.72 Sharpe / 9.47% CAGR — harmonized shows lower (0.153 Sharpe) over much longer period (2007-2026 vs 5Y OOS).
- **Volatility Regime ML**: Author reported 1.18 Sharpe / 16.7% CAGR — harmonized confirms strong performance (1.29 Sharpe).
- **Defensive ETF Rotation**: No QC Cloud project exists (was never cloned). Cannot compile/backtest.
- **Puppies of the Dow**: Author reported 0.56 Sharpe / 10.5% CAGR — harmonized close (0.386 Sharpe) over much longer period.
- **Macro Factor Rotation**: Author reported 1.23 Sharpe / 33.45% CAGR — harmonized lower (0.927 Sharpe) but still strong. BTCUSD KeyError fixed, start date 2013 (BTC data constraint).
- **Long-Short Harvest**: Author reported 1.32 Sharpe / 14.2% CAGR — harmonized shows exceptional performance (1.505 Sharpe) over 2005-2026. 500-equity universe with daily rebalance.
- **Piotroski F-Score**: Author reported 2.09 Sharpe / 18.44% CAGR (1Y OOS only) — harmonized over 20 years shows more modest results (0.362 Sharpe, 60.3% MaxDD).
- **Commodity Term Structure**: Author reported -0.041 Sharpe / -15.71% CAGR — harmonized confirms poor performance (0.009 Sharpe, -11.39% CAGR, 97.5% MaxDD). Variable scoping bug fixed before final backtest.

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
