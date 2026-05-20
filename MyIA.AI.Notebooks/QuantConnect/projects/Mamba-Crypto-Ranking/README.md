# Mamba-Crypto-Ranking

**Asset class:** Crypto (BTC-USD, ETH-USD)

**Cloud project ID:** N/A (research-only, no deployable algorithm)

## Description

Research notebook evaluating Mamba (Selective State Space Model, Gu and Dao 2023) for crypto direction prediction (BTC-USD, ETH-USD). Compares Mamba (d_model=64, d_state=8, 1 layer, 80 epochs) against DLinear and TFT-Lite baselines. Pure PyTorch implementation with walk-forward validation. Verdict: Mamba INCONCLUSIVE (Sharpe 0.000, outputs NaN during training), DLinear NO BEATS, TFT-Lite NO BEATS.

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
| Mamba SSM | N/A (research) | d_model=64, d_state=8, 1 layer, 80 epochs, walk-forward 5-fold x 4 seeds |

## Files

| File | Description |
|------|-------------|
| `research.ipynb` | Research notebook with Mamba model implementation, comparison vs DLinear/TFT-Lite baselines |
| `_generate_research.py` | Script that generates the research notebook |

## References

- Gu, A., Dao, T. (2023). *Mamba: Linear-Time Sequence Modeling with Selective State Spaces*. arXiv.
- [QuantConnect Documentation](https://www.quantconnect.com/docs/)
