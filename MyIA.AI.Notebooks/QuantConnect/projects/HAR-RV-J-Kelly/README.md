# HAR-RV-J-Kelly

**Asset class:** Crypto (BTCUSDT, ETHUSDT, LTCUSDT, BCHUSDT on Binance)

**Cloud project ID:** 31650567

## Description

HAR-RV-J (Heterogeneous Autoregressive Realized Variance with Jumps, Corsi 2009 + Andersen, Bollerslev & Diebold 2007) for forecasting 5-day realized variance on crypto assets. Extends HAR Classic with jump component from Huang-Tauchen bipower variation. Kelly 1/4 fraction for position sizing.

Set parameter `use_jumps=1` for HAR-RV-J (6 features) or `use_jumps=0` for HAR Classic (3 features).

## How to Run

### QC Cloud
Open cloud project 31650567, compile and run a backtest.

## Backtest Metrics

Verified on QC Cloud (project 31650567, Binance USDT DAILY):

| Variant | Period | Sharpe | CAGR | Max DD | PSR |
|---------|--------|--------|------|--------|-----|
| HAR-RV-J Kelly (use_jumps=1, aligned) | 2018-01-01 → 2025-06-01 | **0.524** | 14.08% | 37.10% | 10.7% |
| HAR-RV-J Kelly v2 (use_jumps=1) | 2020-01-01 → 2025-06-01 | 0.746 | 23.03% | 48.30% | 24.0% |
| HAR Classic Baseline (use_jumps=0) | 2020-01-01 → 2025-06-01 | 0.642 | 27.0% | 41.1% | 15.8% |

The aligned 2018-2025 row (backtest `df687834`, 2026-06-22) extends the window backward: with `train_window=500` the model accumulates through ~2018-2019 before it can forecast, so the longer period adds early-regime out-of-sample data and lowers Sharpe (0.746 → 0.524) and CAGR (23.0% → 14.1%) versus the 2020-2025 window, while *improving* MaxDD (48.3% → 37.1%) — the different coefficient path through the 2022 crypto bear produces a less-leveraged exposure. PSR 10.7% (non-significant). Promoted Tier 4 (Untested) → Tier 2 (Historique) on the aligned window; the strongest backbone baseline since GlobalMacro-Regime (0.454). See #1630.

The HAR-RV-J v2 row is verified under the current Binance USDT DAILY configuration (2026-06-12, backtest `verify-har-rv-j-real-metrics`). The HAR Classic baseline retains its 2026-05-14 measurement (pre-Binance configuration); a fresh `use_jumps=0` run under the current configuration is pending for an apples-to-apples delta.

> **Note:** The trade-count column was removed because the `read_backtest` MCP method does not parse the `totalOrders` field (always reports 0). The strategy trades actively — a 23% CAGR and 48% drawdown cannot arise from an all-cash book. The real order count is read from the QC Cloud web UI (*Backtests Results* treegrid, "Orders" column). See the Multi-Layer-EMA README for the full diagnostic of this MCP phantom (resolved as part of #2801 Lot 2).

## Files

| File | Description |
|------|-------------|
| `main.py` | HAR-RV-J volatility forecasting with Kelly Criterion sizing on 4 crypto assets |

## References

- Corsi, F. (2009). *A Simple Approximate Long-Memory Model of Realized Volatility*. Journal of Financial Econometrics.
- Andersen, T.G., Bollerslev, T., & Diebold, F.X. (2007). *Roughing It Up: Including Jump Components in the Measurement, Modeling, and Forecasting of Return Volatility*. Review of Economics and Statistics.
