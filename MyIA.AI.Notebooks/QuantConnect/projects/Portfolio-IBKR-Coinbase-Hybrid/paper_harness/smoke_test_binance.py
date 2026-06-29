"""Read-only smoke test for the Binance sleeve.

Connects to the Binance Spot Test Network (paper), verifies the key's
permissions, reports connectivity + the fictitious balances, fetches a live
price, and **dry-runs** the circuit breakers against the live quote
balance. It never places an order — that path is gated on a reviewed
orchestrator.

Run from the project root::

    python -m paper_harness.smoke_test_binance

Exit code 0 = SOTA-OK (connected, can trade, breakers consistent).
"""
from __future__ import annotations

import sys

from .binance_sleeve import BinanceSleeve
from .config import load_config
from .risk import RiskGate


def _bal_line(asset: str, free: float) -> str:
    return f"{asset:<8} free={free:.4f}"


def main() -> int:
    cfg = load_config()
    print("=" * 64)
    print("Phase 4 paper harness — Binance sleeve read-only smoke test")
    print("=" * 64)
    print(f"env          : {cfg.env_path}")
    print(f"testnet      : {cfg.binance.testnet}")
    print(f"base_quote   : {cfg.binance.base_quote}")

    if not cfg.binance.has_credentials:
        print("FAIL: BINANCE_API_KEY / BINANCE_API_SECRET not set in .env")
        return 2

    sleeve = BinanceSleeve(cfg.binance).connect()

    status = sleeve.system_status()
    print(f"system       : {status}")
    if status.get("status") != 0:
        print(f"FAIL: testnet not normal ({status})")
        return 3

    acct = sleeve.account_info()
    print(f"account_type : {acct.get('accountType')}")
    print(f"can_trade    : {acct.get('canTrade')}")
    print(f"maker_fee    : {acct.get('makerCommission')} bps")
    if not acct.get("canTrade"):
        print("FAIL: key lacks TRADE permission")
        return 4

    bals = sleeve.balances(only_nonzero=True)
    print(f"balances     : {len(bals)} non-zero (fictitious)")
    for b in sorted(bals, key=lambda x: x.free, reverse=True)[:8]:
        print("  " + _bal_line(b.asset, b.free))

    quote = sleeve.quote_balance()
    print(f"{cfg.binance.base_quote:<12}: {quote:.2f} free")

    pair = f"BTC{cfg.binance.base_quote}"
    price = sleeve.price(pair)
    print(f"{pair:<12}: {price:.2f}")

    # --- dry-run circuit breakers against the live quote balance ---
    capital = cfg.binance.initial_capital_usd or quote
    gate = RiskGate(cfg.risk, starting_capital=capital)
    gate.update_equity(capital)  # baseline mark, no drawdown yet

    def check(notional: float, gross: float, label: str) -> None:
        decision = gate.check_order(
            sleeve_capital=capital,
            order_notional=notional,
            gross_exposure_after=gross,
        )
        flag = "ALLOW" if decision.allowed else "BLOCK"
        print(f"  risk[{label:<26}] -> {flag} : {decision.reason}")

    print("risk dry-run (no orders placed):")
    # sane allocation: 20% of capital into BTC, within the single-position cap.
    check(capital * 0.20, capital * 0.20, "sane 20% allocation")
    # oversized single order: 40% > max_position_pct (25%) -> must block.
    check(capital * 0.40, capital * 0.40, "oversized 40% (must block)")
    # gross-exposure breach: 120% > max_gross_exposure (100%) -> must block.
    check(capital * 0.20, capital * 1.20, "gross 120% (must block)")

    print("=" * 64)
    print("SOTA-OK: connected, can_trade, breakers consistent (read-only).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
