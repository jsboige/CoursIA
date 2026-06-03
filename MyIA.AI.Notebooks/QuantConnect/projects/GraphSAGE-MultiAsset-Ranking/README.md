# GraphSAGE-MultiAsset-Ranking

**Asset class:** Equities (large-cap US stocks)

**Cloud project ID:** N/A (research-only, no deployable algorithm)

## Description

Research notebook applying GraphSAGE (Hamilton, Ying, and Leskovec 2017) graph neural network for cross-asset direction prediction on 8 large-cap US stocks (JPM, JNJ, XOM, PG, UNP, V, HD, BA). Constructs a correlation-based graph with threshold 0.5 to capture inter-asset dependencies. Walk-forward 5-fold validation across 4 seeds with 10bps transaction costs. Verdict: INCONCLUSIVE (insufficient statistical evidence to confirm or reject the approach).

## How to Run

### Lean CLI
Not applicable (research-only notebook, no `main.py`).

### QC Cloud
Not applicable. Run the research notebook locally with Python 3.10+ and PyTorch Geometric.

### Local
```bash
papermill research.ipynb output.ipynb
```

## Backtest Metrics

| Method | Rebalance | Key Parameters |
|--------|-----------|----------------|
| GraphSAGE cross-asset ranking | N/A (research) | Correlation threshold 0.5, walk-forward 5-fold x 4 seeds, 10bps T-cost |

## Files

| File | Description |
|------|-------------|
| `research.ipynb` | Research notebook with GraphSAGE model, correlation graph construction, and walk-forward validation |
| `_generate_research.py` | Script that generates the research notebook |

## References

- Hamilton, W., Ying, Z., Leskovec, J. (2017). *Inductive Representation Learning on Large Graphs*. NeurIPS.
- [QuantConnect Documentation](https://www.quantconnect.com/docs/)
