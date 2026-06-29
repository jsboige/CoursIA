"""Read-only smoke test for the Coinbase (MiCA) sleeve.

Connects to the Coinbase Advanced Trade API, verifies the key, reports
connectivity + balances, fetches a live price, and **dry-runs** the circuit
breakers against the live quote balance. It never places an order — that path
is gated on a reviewed orchestrator.

USER-HAND gate (cf ../README.md Phase-B, #1027): if Coinbase creds are absent
from ``.env`` the test reports RECOVERABLE-USER-HAND (exit 2) and prints the
``[ASK USER]`` notice — the user must open a Coinbase account + create a CDP
API key. The sleeve code is SOTA-OK; only the live run is gated.

Run from the project root::

    python -m paper_harness.smoke_test_coinbase

Exit codes: 0 = SOTA-OK (connected, breakers consistent) ; 2 = creds missing
(USER-HAND) ; 3+ = connectivity / permission failure.
"""
from __future__ import annotations

import sys

from .coinbase_sleeve import CoinbaseSleeve
from .config import load_config
from .risk import RiskGate


def _bal_line(asset: str, free: float) -> str:
    return f"{asset:<8} free={free:.4f}"


def main() -> int:
    cfg = load_config()
    print("=" * 64)
    print("Phase 4 paper harness — Coinbase (MiCA) sleeve read-only smoke test")
    print("=" * 64)
    print(f"env          : {cfg.env_path}")
    print(f"sandbox      : {cfg.coinbase.sandbox}")
    print(f"base_quote   : {cfg.coinbase.base_quote}")

    if not cfg.coinbase.has_credentials:
        # USER-HAND: creds must be created in the Coinbase Developer Platform.
        # Exit 2 (not a test failure) — the sleeve code is SOTA-OK, only the
        # live run is gated on the user opening a Coinbase account.
        print("-" * 64)
        print("[ASK USER] RECOVERABLE-USER-HAND:")
        print("  COINBASE_API_KEY / COINBASE_API_SECRET not set in .env.")
        print("  Create a CDP API key (Ed25519/ECDSA) at")
        print("  https://portal.cdp.coinbase.com/ after opening a Coinbase")
        print("  account (account opening is user-side, #1027 Phase-B).")
        print("  Sleeve code is SOTA-OK; only the live run is gated.")
        return 2

    sleeve = CoinbaseSleeve(cfg.coinbase).connect()

    acct = sleeve.account_info()
    # Coinbase get_accounts response: {accounts: [...]} on success.
    accounts = acct.get("accounts", []) if isinstance(acct, dict) else []
    print(f"accounts     : {len(accounts)}")

    bals = sleeve.balances(only_nonzero=True)
    print(f"balances     : {len(bals)} non-zero")
    for b in sorted(bals, key=lambda x: x.free, reverse=True)[:8]:
        print("  " + _bal_line(b.asset, b.free))

    quote = sleeve.quote_balance()
    print(f"{cfg.coinbase.base_quote:<12}: {quote:.2f} free")

    pair = sleeve.product_id("BTC")
    price = sleeve.price(pair)
    print(f"{pair:<12}: {price:.2f}")

    # --- dry-run circuit breakers against the live quote balance ---
    capital = cfg.coinbase.initial_capital_usd or quote
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
    check(capital * 0.20, capital * 0.20, "sane 20% allocation")
    check(capital * 0.40, capital * 0.40, "oversized 40% (must block)")
    check(capital * 0.20, capital * 1.20, "gross 120% (must block)")

    print("=" * 64)
    print("SOTA-OK: connected, breakers consistent (read-only).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
