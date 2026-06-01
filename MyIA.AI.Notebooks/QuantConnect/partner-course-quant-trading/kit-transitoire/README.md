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
