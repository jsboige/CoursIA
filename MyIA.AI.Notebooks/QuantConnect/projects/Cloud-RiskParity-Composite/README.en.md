# Cloud-RiskParity-Composite

**Asset class:** Multi-asset (Equities, Bonds, Commodities)

**Cloud project ID:** 30820857

## Description

Tactical rotation across six asset classes (SPY, TLT, GLD, EFA, EEM, DBC) using a dual filter: price above SMA200 AND positive 6-month momentum. Assets passing both filters receive equal weight. Rebalances every 30 days. Inspired by AQR's Hurst, Ooi, and Pedersen (2014) approach to trend-following with risk parity allocation.

## How to Run

### Lean CLI
```bash
lean backtest --algorithm Cloud-RiskParity-Composite/main.py
```

### QC Cloud
Project 30820857. Upload `main.py`, compile and run a backtest. Hard-coded period: **2018-01-01 → 2025-01-01** (aligned with the cross-strategy baseline #1630). Optional parameter `rebalance_days` (default 30).

## Backtest Metrics

Fresh backtest via QC Cloud MCP, 2026-08-14 (`RiskParity-Composite-2018-2025-aligned-status-2026-08`, project 30820857, compile `BuildSuccess`, 1761 tradeable dates, 297 orders):

| Indicator | Value | Reading |
|---|---|---|
| Sharpe ratio | **0.027** | near zero |
| CAGR | **3.50%** | below buy-and-hold SPY over the period |
| Max drawdown | **24.400%** | high |
| Total net profit | **27.282%** (+$17,435) | over the period |
| PSR (Probabilistic Sharpe Ratio) | **0.094%** | indistinguishable from noise |
| Orders | 297 | real backtest |

**Verdict: NO-BEATS.** Sharpe 0.027, CAGR ~3.5%: the dual-filter rotation does not beat buy-and-hold SPY over this window (double-digit CAGR 2018-2025). The structural ceiling of unlevered equal-weight trend-following is confirmed (see the `qc-strategies-status.md` catalog: "pedagogical counter-example").

| Method | Rebalance | Key Parameters |
|--------|-----------|----------------|
| Dual-filter Risk Parity | 30 days | SMA200 + 6-month momentum, equal weight among passing assets |

## Files

| File | Description |
|------|-------------|
| `main.py` | Risk parity rotation with SMA200 + momentum dual filter on 6 multi-asset ETFs |

## References

- Hurst, B., Ooi, Y.H., Pedersen, L.H. (2014). *A Century of Evidence on Trend-Following Investing*. AQR.
- [QuantConnect Documentation](https://www.quantconnect.com/docs/)
