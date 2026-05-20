# TFT-Crypto-Ranking

**Asset class:** Crypto (BTC-USD, ETH-USD)

**Cloud project ID:** N/A (research-only, no deployable algorithm)

## Description

Research notebook applying the Temporal Fusion Transformer (TFT, Lim et al. 2021) for crypto cross-sectional ranking (BTC vs ETH direction prediction). Uses 26 features (11 BTC-specific + 11 ETH-specific + 4 cross-asset). Architecture includes Variable Selection Network (VSN), Gated Residual Network (GRN), LSTM encoder, and multi-head attention. Walk-forward 5-fold validation across 4 seeds with 10bps transaction costs. DLinear baseline achieved Sharpe 0.742. Verdict: INCONCLUSIVE (z=1.33, insufficient for BEATS threshold).

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
| TFT cross-sectional ranking | N/A (research) | 26 features, VSN+GRN+LSTM+attention, walk-forward 5-fold x 4 seeds, 10bps T-cost |

## Files

| File | Description |
|------|-------------|
| `research.ipynb` | Research notebook with TFT model for crypto ranking, feature engineering, and walk-forward validation |
| `_generate_research.py` | Script that generates the research notebook |

## References

- Lim, B. et al. (2021). *Temporal Fusion Transformers for Interpretable Multi-horizon Time Series Forecasting*. International Journal of Forecasting.
- [QuantConnect Documentation](https://www.quantconnect.com/docs/)
