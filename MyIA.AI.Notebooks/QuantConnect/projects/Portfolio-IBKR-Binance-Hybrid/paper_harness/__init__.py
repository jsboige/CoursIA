"""Phase 4 paper-trading harness (Portfolio-IBKR-Binance-Hybrid).

Local execution harness for paper trading the composite portfolio described
in the project README. Distinct from ``main.py`` (the QC Cloud backtest
algorithm): this package talks to live paper venues (Binance Spot Testnet,
IB Gateway paper) instead of the QC Cloud backtester.

Status (2026-06-22):
- Binance sleeve: DONE + SOTA-OK (validated live against the Spot Testnet).
- Risk / circuit breakers: implemented, dry-run validated.
- IBKR sleeve + orchestrator: TODO (next cycle, gated on IB Gateway launch).
"""
