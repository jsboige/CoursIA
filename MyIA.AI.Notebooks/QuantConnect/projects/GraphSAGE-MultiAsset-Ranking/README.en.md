# GraphSAGE-MultiAsset-Ranking

**Type:** Research (no deployable algorithm, research-only notebook)

**Asset class:** Equities (large-cap US stocks)

**Cloud project ID:** N/A (research-only, no deployable algorithm)

## Description

Research notebook applying GraphSAGE (Hamilton, Ying, and Leskovec 2017) graph neural network for cross-asset direction prediction on 8 large-cap US stocks (JPM, JNJ, XOM, PG, UNP, V, HD, BA). The graph links two stocks whose return correlation exceeds 0.5; it is rebuilt on each fold's training window, and message passing only links stocks of the same date. Five expanding-window temporal folds, 4 seeds; a decision taken at the close earns the next-day return, with 10 basis points of fees on the traded amount; the benchmark is an equal-weight portfolio of the same stocks over the same dates. **Committed verdict: NO BEATS** — out of sample (2289 sessions, late 2015 to late 2024), Sharpe −0.37 for GraphSAGE and −0.05 for a graph-free MLP, against 0.79 for the benchmark; the daily gap is significantly negative (Newey-West t −8.29 for GraphSAGE). Before fees, the MLP roughly matches the benchmark (t = 0.54): the fees of a daily rotation make it lose. The graph degrades the MLP (t = −2.99), and both models' probabilities are worse than plain climatology (Diebold-Mariano, p < 0.01). The notebook documents an **absence** of edge, not a validation.

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
| GraphSAGE cross-asset ranking | N/A (research) | Correlation threshold 0.5, 5 temporal folds x 4 seeds, 10 bps on traded amount |

## Files

| File | Description |
|------|-------------|
| `research.ipynb` | Research notebook with GraphSAGE model, correlation graph construction, and walk-forward validation |
| `_generate_research.py` | Script that generates the research notebook |

## References

- Hamilton, W., Ying, Z., Leskovec, J. (2017). *Inductive Representation Learning on Large Graphs*. NeurIPS.
- [QuantConnect Documentation](https://www.quantconnect.com/docs/)
