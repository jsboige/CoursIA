"""Read-only smoke test for the IBKR sleeve.

Connects to the local IB Gateway (paper/simulated trading), reports the
managed account + an account snapshot (NetLiq, cash, buying power) and the
open positions, and **dry-runs** the circuit breakers against the live net
liquidation. It never places an order — the order path
(:meth:`~paper_harness.ibkr_sleeve.IBKRSleeve.market_order`) is gated on a
reviewed orchestrator and on the gateway's "Read-Only API" being OFF.

Run from the project root::

    python -m paper_harness.smoke_test_ibkr

Exit code 0 = SOTA-OK (connected to IB Gateway paper, read access works).

Note: if the gateway has "Read-Only API" enabled, account/position queries
still succeed; placing the first paper order later will require that
setting to be turned OFF (IB Gateway -> Configure -> Settings -> API ->
Read-Only).
"""
from __future__ import annotations

import sys

from .config import load_config
from .ibkr_sleeve import IBKRSleeve
from .risk import RiskGate


def main() -> int:
    cfg = load_config()
    print("=" * 64)
    print("Phase 4 paper harness — IBKR sleeve read-only smoke test")
    print("=" * 64)
    print(f"env          : {cfg.env_path}")
    print(f"host:port    : {cfg.ibkr.host}:{cfg.ibkr.port} (clientId {cfg.ibkr.client_id})")
    print(f"trading_mode : {cfg.ibkr.trading_mode}")

    if not cfg.ibkr.is_paper:
        print(f"FAIL: IBKR_TRADING_MODE={cfg.ibkr.trading_mode} (not 'paper') — abort for safety.")
        return 2

    sleeve: IBKRSleeve
    try:
        sleeve = IBKRSleeve(cfg.ibkr).connect()
    except Exception as e:  # noqa: BLE001 - surface any connect failure cleanly
        print(f"FAIL: connect failed: {type(e).__name__}: {e}")
        print("      Is IB Gateway running in paper/simulated mode on the configured port?")
        return 3

    try:
        managed = sleeve.managed_accounts()
        snap = sleeve.account_snapshot()
        positions = sleeve.positions()

        print(f"managed acct : {managed}")
        print(f"config acct  : {cfg.ibkr.account_id or '(not set)'}")
        if cfg.ibkr.account_id and cfg.ibkr.account_id not in managed:
            print(
                f"WARN: IBKR_ACCOUNT_ID in .env ({cfg.ibkr.account_id}) "
                f"!= gateway managed account(s) {managed}"
            )
        print(f"account_type : {snap.account_type or '(n/a)'}")
        print(f"net_liq      : {snap.net_liquidation:,.2f}")
        print(f"total_cash   : {snap.total_cash:,.2f}")
        print(f"equity_loan  : {snap.equity_with_loan:,.2f}")
        print(f"buying_power : {snap.buying_power:,.2f}")
        print(f"positions    : {len(positions)}")

        # --- dry-run circuit breakers against the live net liquidation ---
        capital = snap.net_liquidation or cfg.ibkr.initial_capital_usd
        if capital <= 0:
            print("FAIL: no net liquidation and no IBKR_INITIAL_CAPITAL_USD — cannot dry-run breakers.")
            return 4
        gate = RiskGate(cfg.risk, starting_capital=capital)
        gate.update_equity(capital)  # baseline mark, no drawdown yet

        def check(notional: float, gross: float, label: str) -> None:
            decision = gate.check_order(
                sleeve_capital=capital,
                order_notional=notional,
                gross_exposure_after=gross,
            )
            flag = "ALLOW" if decision.allowed else "BLOCK"
            print(f"  risk[{label:<28}] -> {flag} : {decision.reason}")

        print("risk dry-run (no orders placed):")
        # sane allocation: 20% of capital, within the single-position cap.
        check(capital * 0.20, capital * 0.20, "sane 20% allocation")
        # oversized single order: 40% > max_position_pct (25%) -> must block.
        check(capital * 0.40, capital * 0.40, "oversized 40% (must block)")
        # gross-exposure breach: 120% > max_gross_exposure (100%) -> must block.
        check(capital * 0.20, capital * 1.20, "gross 120% (must block)")
    finally:
        sleeve.disconnect()

    print("=" * 64)
    print("SOTA-OK: connected to IB Gateway paper, read access works.")
    print("Note: first paper order will require Read-Only API OFF on the gateway.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
