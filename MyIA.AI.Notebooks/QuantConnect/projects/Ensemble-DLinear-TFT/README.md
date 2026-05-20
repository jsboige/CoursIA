# Ensemble-DLinear-TFT

**Asset class:** Crypto (BTC-USD, ETH-USD)

**Cloud project ID:** N/A (research-only, no deployable algorithm)

## Description

Research notebook exploring an ensemble of DLinear and TFT-Lite neural network architectures for predicting crypto direction (BTC-USD, ETH-USD). Conducts a v2 grid search over ensemble weights {0.4, 0.5, 0.6, 0.7} with walk-forward 5-fold validation across 4 seeds. Applies 10bps transaction costs. Verdict: NO BEATS for all configurations (DLinear z=-6.00, TFT-Lite z=-10.69, ensemble z=-9.28).

## How to Run

### Lean CLI
Not applicable (research-only notebook, no `main.py`).

### QC Cloud
Not applicable. Run the research notebook locally with Python 3.10+ and PyTorch.

### Local
```bash
papermill research.ipynb output.ipynb
```

## Backtest Metrics

| Method | Rebalance | Key Parameters |
|--------|-----------|----------------|
| DLinear + TFT-Lite ensemble | N/A (research) | Walk-forward 5-fold x 4 seeds, weight grid {0.4-0.7}, 10bps T-cost |

## Files

| File | Description |
|------|-------------|
| `research.ipynb` | Research notebook with DLinear + TFT-Lite ensemble grid search and walk-forward validation |
| `_generate_research.py` | Script that generates the research notebook |

## References

- Zeng, A. et al. (2023). *Are Transformers Effective for Time Series Forecasting?* AAAI.
- Lim, B. et al. (2021). *Temporal Fusion Transformers for Interpretable Multi-horizon Time Series Forecasting*. International Journal of Forecasting.
- [QuantConnect Documentation](https://www.quantconnect.com/docs/)
