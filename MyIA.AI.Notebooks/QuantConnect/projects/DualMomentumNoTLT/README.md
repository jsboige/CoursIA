# DualMomentumNoTLT

**Asset class:** Multi-asset (SPY, QQQ, IEF, GLD, XLP)
**Cloud project ID:** 31244186 (Framework variant)

## Description

Dual momentum rotation excluding long-duration bonds (TLT). Selects top 2 assets by 12-month return among those with positive absolute momentum, with equal-weight allocation. Falls to cash when no asset passes the absolute momentum filter.

Key insight: TLT lost ~40% during 2020-2023 rate hikes. This variant uses IEF (intermediate bonds), GLD, and XLP (consumer staples) as alternatives.

## Strategy Logic

| Component | Parameters | Role |
|-----------|------------|------|
| Universe | SPY, QQQ, IEF, GLD, XLP | 5 diversified assets |
| Lookback | 252 trading days (12 months) | Momentum measurement |
| Absolute filter | 12M return > 0 | Skip negative momentum |
| Selection | Top 2 by 12M return | Relative momentum |
| Weighting | Equal weight | 50% per position |
| Rebalance | Monthly | Calendar rebalance |

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/DualMomentumNoTLT"`
**QC Cloud:** Deployed as project 31244186 (Framework variant with alpha_model.py).

## Backtest Metrics

| Metric | Value |
|--------|-------|
| Method | Dual momentum (no TLT) |
| Universe | SPY, QQQ, IEF, GLD, XLP |
| Rebalance | Monthly |
| Lookback | 12 months |

## Files

- main.py - Strategy (standalone version)
- alpha_model.py - Framework AlphaModel variant
- config_framework.json - QC Framework configuration

## References

- Antonacci (2014), Dual Momentum Investing
