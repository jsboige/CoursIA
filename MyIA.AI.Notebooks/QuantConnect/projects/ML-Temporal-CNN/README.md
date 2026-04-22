# ML-Temporal-CNN (HandsOn Ex14)

**Asset class:** US Equities (QQQ top-3)
**Cloud project ID:** None (local only)

## Description

Temporal Conv1D CNN for return prediction. Uses sliding window of past 20 days returns as input to a 1D convolutional network.

## How to Run

**Lean CLI:**

**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics

| Metric | Value |
|--------|-------|
| Model | Conv1D CNN (Keras) |
| Universe | QQQ top-3 |
| Rebalance | Daily |

## Files

- main.py - Strategy (v1.0, temporal CNN)
- research.ipynb - CNN architecture and training
## References

- Hands-On AI Trading, Section 06, Example 14
