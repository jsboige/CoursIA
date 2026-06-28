"""Phase 4 paper-trading harness (Portfolio-IBKR-Binance-Hybrid).

Local execution harness for paper trading the composite portfolio described
in the project README. Distinct from ``main.py`` (the QC Cloud backtest
algorithm): this package talks to live paper venues (Coinbase Advanced Trade
API, IB Gateway paper) instead of the QC Cloud backtester.

MiCA migration (2026-06-28, see ../README.md): the ACTIVE crypto venue is now
Coinbase (CAS MiCA France, QC-native). The legacy ``binance_sleeve.py`` is
preserved as a fallback. Binance France services cease 2026-07-01.

Status (2026-06-28):
- Coinbase sleeve: DONE + SOTA-OK code (real ``coinbase-advanced-py`` SDK,
  API surface verified firsthand: RESTClient / get_accounts / get_product /
  market_order_buy / market_order_sell / cancel_orders). Live run gated
  USER-HAND: account opening + CDP API key are user-side (#1027 Phase-B).
  Smoke test reports RECOVERABLE-USER-HAND (exit 2) when creds are absent.
- Binance sleeve: legacy fallback, SOTA-OK when exercised (pre-MiCA).
- IBKR sleeve: DONE + SOTA-OK (validated live against IB Gateway paper,
  account summary + positions read surface). Order placement gated on the
  gateway's "Read-Only API" being OFF (USER-HAND) + a reviewed orchestrator.
- Risk / circuit breakers: implemented, dry-run validated.
- Orchestrator: TODO (next cycle).
"""
