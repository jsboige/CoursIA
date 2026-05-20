# Research-Executor

**Asset class:** Multi-asset (research execution harness)

**Cloud project ID:** N/A

## Description

Framework that executes 8 embedded research notebooks as a QC algorithm within a 2-day backtest window (2024-01-02 to 2024-01-03). Uses a MockQB class to simulate QuantBook environment for notebooks. The embedded research topics include: asset class momentum, commodity term structure, defensive ETF rotation, short harvest, macro factor rotation, Piotroski F-score, puppies of the Dow, and volatility regime ML. Saves executed notebooks to the QC object store.

## How to Run

### Lean CLI
```bash
lean backtest --algorithm Research-Executor/main.py
```

### QC Cloud
Create a new project, upload `main.py` and all research notebooks, compile and run a backtest.

### Research Notebook
```bash
papermill runner.ipynb output.ipynb
```

## Backtest Metrics

| Method | Rebalance | Key Parameters |
|--------|-----------|----------------|
| Research harness (8 notebooks) | N/A (execution framework) | 2-day window, MockQB simulation, Object Store output |

## Files

| File | Description |
|------|-------------|
| `main.py` | Research executor algorithm that runs 8 embedded notebooks via MockQB |
| `runner.ipynb` | Jupyter notebook runner for the research executor |
| `research_asset_class_momentum.ipynb` | Asset class momentum research notebook |
| `research_commodity_term_structure.ipynb` | Commodity term structure research notebook |
| `research_defensive_etf_rotation.ipynb` | Defensive ETF rotation research notebook |
| `research_short_harvest.ipynb` | Short harvest research notebook |
| `research_macro_factor_rotation.ipynb` | Macro factor rotation research notebook |
| `research_piotroski_fscore.ipynb` | Piotroski F-score research notebook |
| `research_puppies_of_dow.ipynb` | Puppies of the Dow research notebook |
| `research_volatility_regime_ml.ipynb` | Volatility regime ML research notebook |

## References

- [QuantConnect Documentation](https://www.quantconnect.com/docs/)
