"""Phase 4 paper-trading harness (Portfolio-IBKR-Binance-Hybrid).

Local execution harness for paper trading the composite portfolio described
in the project README. Distinct from ``main.py`` (the QC Cloud backtest
algorithm): this package talks to live paper venues (Binance Spot Testnet,
IB Gateway paper) instead of the QC Cloud backtester.

Status (2026-06-22):
- Binance sleeve: DONE + SOTA-OK (validated live against the Spot Testnet).
- IBKR sleeve: DONE + SOTA-OK (validated live against IB Gateway paper,
  account summary + positions read surface). Order placement gated on the
  gateway's "Read-Only API" being OFF (USER-HAND) + a reviewed orchestrator.
- Risk / circuit breakers: implemented, dry-run validated.
- Orchestrator: TODO (next cycle).
"""
