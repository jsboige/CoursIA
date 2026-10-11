# Transition Kit - ML & Framework Strategies

Three progressive QuantConnect strategies for sector rotation, validated on cloud backtests (2015-2024).

## Objective

Provide 3 progressive approaches to sector rotation:

1. **ML RandomForest** (classification) - Introduction to applied ML
2. **ML XGBoost** (regression) - Advanced model with more features
3. **Framework Composite** (alpha models) - Clean QC Framework architecture

Each strategy includes a research notebook (QuantBook) documenting iterations and calibration.

## Strategies

### 01 - ML RandomForest Sector Rotation

| Parameter | Value |
|-----------|-------|
| Universe | 9 sector ETFs (XLK..XLRE) |
| Features | 14 technical indicators |
| Model | RandomForestClassifier |
| Trees / Depth | 200 / 6 |
| Training | 4-year rolling, monthly retrain |
| Bear filter | SPY < SMA200 -> max 2 positions |
| Max positions | 4 (2 in bear market) |
| Allocation | 95% |

**Best backtest** : Sharpe 0.556, CAGR 11.43%, MaxDD 17.2%

### 02 - ML XGBoost Sector Rotation

| Parameter | Value |
|-----------|-------|
| Universe | 9 sector ETFs (XLK..XLRE) |
| Features | 20 technical indicators |
| Model | GradientBoostingRegressor |
| Trees / Depth / LR | 100 / 4 / 0.05 |
| Training | 3-year rolling, bi-weekly train |
| Bear filter | SPY < SMA200 -> max 2 positions |
| Max positions | 5 (2 in bear market) |
| Allocation | 95% |

**Best backtest** : Sharpe 0.521, CAGR 12.81%, MaxDD 39.1%

### 03 - Framework Composite

| Parameter | Value |
|-----------|-------|
| Alpha 1 | SectorMomentum (SMA200 + 126d momentum) |
| Alpha 2 | Defensive (TLT, GLD, XLU when SPY < SMA200) |
| PCM | MultiStrategyPCM (70% momentum / 30% defensive) |
| Risk | MaxDrawdownCircuitBreaker (15%) |
| Execution | ImmediateExecutionModel |

**Best backtest** : Sharpe 0.376, CAGR 7.60%, MaxDD 20.6%, Win Rate 80%

`main.py` accepts two optional parameters, with no effect by default:

| Parameter | Default | Role |
|---|---|---|
| `pcm_mode` | `base` | `base` keeps the original behaviour; `intent` adds both sleeves on `XLU` (see below) |
| `trace` | `0` | `1` plots the portfolio value and the SPY close once per session in a `shadow` chart (interleaved series `e0`..`e4` and `b0`..`b4`, strategy league format #19821); no order changes |

#### `XLU` in both sleeves: QC Cloud measurement (#20188), 2026-10-10

`XLU` belongs to both sleeves: `SectorMomentum` (70%) and `Defensive` (30%). Lean's base portfolio construction model passes only one active insight per symbol to `determine_target_percent`. One sleeve can therefore hide the other on `XLU`.

The measurement shows that the masking always goes the same way. Both models emit at the same instant, and the insight passed for `XLU` is, at every call, the `Defensive` one. In `base` mode, `XLU` therefore receives only the defensive share: 10% of the portfolio when SPY is below its SMA200, nothing otherwise. The `SectorMomentum` vote on `XLU` is never applied, although it is UP in 68% of the calls. Its share does not stay in cash: the sleeve's 70% is spread over the other selected sectors.

The `intent` mode uses the additive fix from #19740: it rebuilds the most recent active insight per (symbol, sleeve) pair, then sums the weights per symbol. The average `XLU` target goes from 1.8% to 10.5% of the portfolio.

The measurement rule was written in #20188 before the first backtest. Three runs cover the kit window, 2015-01-01 to 2024-12-31:
- `orig`: the `main.py` from before these parameters;
- `base` and `intent`: the new `main.py`, with `trace=1`.

**Non-regression.** `base` reproduces `orig` exactly: all 27 QC statistics, turnover included, and the 2149 orders, compared one by one. The kit result is recovered: QC Sharpe 0.377, CAGR 7.59%, MaxDD 20.6%.

| Run | Sharpe | CAGR | Max drawdown | Orders | Cumulative fees, % of starting capital |
|---|---|---|---|---|---|
| `base` | 0.72 | 7.6% | -20.6% | 2149 | 3.0% |
| `intent` | 0.71 | 7.4% | -21.9% | 2320 | 3.3% |
| SPY held (reference, no fees) | 0.78 | 13.0% | -33.7% | - | - |

The Sharpe in this table is computed on daily returns, with a zero risk-free rate, annualised over 252 sessions. The Sharpe shown by QC (0.377 for `base`, 0.366 for `intent`) subtracts a risk-free rate.

| `intent` - `base`, Sharpe difference | Gap | 95% CI | One-sided p | 2015-2018 | 2019-2021 | 2022-2024 |
|---|---|---|---|---|---|---|
| full window | -0.01 | [-0.21; 0.19] | 0.51 | +0.16 | -0.34 | +0.04 |

The test is a circular block bootstrap with 21-session blocks (10,000 draws, seed 18921), given as descriptive only.

**Reading.** The defect is real: in `base` mode, `XLU` is nearly absent from the portfolio although the momentum sleeve selects it. Its effect on the result, however, is not measurable on this window. The Sharpe gap is zero at the scale of its interval, and its sign changes from one sub-period to the next. The fix adds orders and fees. The default stays `pcm_mode=base`; changing the kit default belongs to a kit issue.

The run traces (plans, hashes, charts, orders, statistics, `results.json`) are kept outside the repository, under `QC-traces/20188-kit03-xlu-shared/`.

## Structure

```
kit-transitoire/
  README.md
  01-ML-RandomForest/
    main.py           # QC Cloud strategy
    research.ipynb    # QuantBook research notebook
  02-ML-XGBoost/
    main.py
    research.ipynb
  03-Framework-Composite/
    main.py
    research.ipynb
```

## Execution

### QC Cloud Backtests

Each `main.py` runs directly on QuantConnect Cloud:
1. Create a QC project
2. Upload `main.py`
3. Compile and run backtest (2015-01-01 to 2024-12-31)

### Research Notebooks

The `research.ipynb` notebooks use `QuantBook` and require the QC Lab environment:
1. Open the project in QC Lab
2. Create a notebook in the project
3. Copy the content from research.ipynb
4. Execute cell by cell

## Comparison

| Aspect | RandomForest | XGBoost | Framework |
|--------|-------------|---------|-----------|
| Type | Classification | Regression | Alpha Models |
| Features | 14 | 20 | Simple indicators |
| Complexity | Medium | Medium | High (architecture) |
| Retrain | Monthly | Bi-weekly | N/A (no ML) |
| Max positions | 4 (2 in bear) | 4 (2 in bear) | Dynamic |
| Learning | Model training | Model training | Expert rules |
| Sharpe | 0.556 | 0.521 | 0.376 |
| CAGR | 11.43% | 12.81% | 7.60% |
| MaxDD | 17.2% | 39.1% | 20.6% |
