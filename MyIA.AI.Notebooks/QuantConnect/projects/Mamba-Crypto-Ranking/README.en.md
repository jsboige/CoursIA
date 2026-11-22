# Mamba-Crypto-Ranking

**Type:** Research (no deployable algorithm, research-only notebook)

**Asset class:** Crypto (BTC-USD, ETH-USD)

**Cloud project ID:** N/A (research-only, no deployable algorithm)

## Description

Research notebook evaluating Mamba (Selective State Space Model, Gu and Dao 2023) for crypto direction prediction (BTC-USD, ETH-USD). Compares Mamba (d_model=64, d_state=8, 1 layer, 80 epochs) against DLinear and TFT-Lite baselines. Pure PyTorch implementation with walk-forward validation. Verdict (re-run of 2026-11-21, #26319): no model beats Buy & Hold on the same test windows (mean Sharpe 1.164). Mamba NO BEATS (test Sharpe 0.625, z -2.49), DLinear NO BEATS (0.375, z -2.03), TFT-Lite INCONCLUSIVE (0.864, z -1.24), the latter often stuck on a single predicted class.

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
