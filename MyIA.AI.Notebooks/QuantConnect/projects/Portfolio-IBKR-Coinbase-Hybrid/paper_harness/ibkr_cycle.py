"""One rebalancing cycle of the UCITS inverse-volatility sleeve on IB Gateway paper.

Dry run by default: the connection is read-only and nothing is sent. The
sleeve's ledger and breaker state live in ``--state-dir`` (outside the
repository by default).

    # first run: attribute fictitious paper cash to the sleeve
    python -m paper_harness.ibkr_cycle --initial-cash 100000
    # later runs reuse the ledger
    python -m paper_harness.ibkr_cycle --small-lines
    # send paper orders (gateway "Read-Only API" must be OFF)
    python -m paper_harness.ibkr_cycle --send

Exit codes: 0 cycle done, 2 refused (not a paper account / inconsistent
configuration), 3 connection failed, 4 an order was never acknowledged (the
cycle stopped there; fills booked before it stay in the ledger), 5 the sleeve
ledger stopped the cycle: an order still pending, a closed order of an earlier
day not fully booked (``python -m paper_harness.ibkr_ledger``), or the ledger
holding more than the account.
"""
from __future__ import annotations

import argparse
import dataclasses
import sys
from pathlib import Path

from .config import load_config
from .ibkr_broker import (
    SIGNAL_TO_LINE,
    SIGNAL_TO_LINE_SMALL,
    UCITS_LINES,
    IBKRBroker,
    LedgerError,
    OrderNotAcknowledgedError,
    SleeveLedger,
    us_signal_closes,
)
from .orchestrator import CycleConfig, run_cycle


def _parse(argv: list[str] | None) -> argparse.Namespace:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--sleeve", default="inverse-vol", help="sleeve name (ledger key and orderRef prefix)")
    ap.add_argument("--state-dir", type=Path, default=Path.home() / ".paper_harness")
    ap.add_argument("--initial-cash", type=float, default=None,
                    help="cash attributed to the sleeve when its ledger is created")
    ap.add_argument("--small-lines", action="store_true", help="trade SPYL/XNAS instead of SXR8/SXRV")
    ap.add_argument("--budget", type=float, default=0.025, help="volatility budget per line")
    ap.add_argument("--max-weight", type=float, default=0.5)
    ap.add_argument("--band", type=float, default=0.03)
    ap.add_argument("--max-position-pct", type=float, default=None,
                    help="override RISK_MAX_POSITION_PCT (must be >= --max-weight)")
    ap.add_argument("--client-id", type=int, default=None, help="default: IBKR_CLIENT_ID")
    ap.add_argument("--account", default=None, help="account to use when several are managed")
    ap.add_argument("--send", action="store_true", help="send paper orders (read-write connection)")
    return ap.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse(argv)
    cfg = load_config()
    if not cfg.ibkr.is_paper:
        print("refused: IBKR_TRADING_MODE is not 'paper'")
        return 2
    risk = cfg.risk
    if args.max_position_pct is not None:
        risk = dataclasses.replace(risk, max_position_pct=args.max_position_pct)

    from ib_insync import IB

    ib = IB()
    try:
        ib.connect(cfg.ibkr.host, cfg.ibkr.port, clientId=args.client_id or cfg.ibkr.client_id,
                   timeout=15, readonly=not args.send)
    except Exception as exc:  # noqa: BLE001 -- report any connection failure the same way
        print(f"connection failed: {type(exc).__name__}: {exc}")
        return 3
    try:
        state = args.state_dir / args.sleeve
        ledger_path = state / "ledger.json"
        try:
            ledger = SleeveLedger.open(ledger_path, args.sleeve, "EUR", args.initial_cash)
            broker = IBKRBroker(ib, UCITS_LINES, ledger, ledger_path,
                                read_only=not args.send, account=args.account)
        except (LedgerError, ValueError) as exc:
            print(f"refused: {exc}")
            return 2
        if not broker.is_paper:
            print("refused: the connected account is not a paper account")
            return 2

        mapping = SIGNAL_TO_LINE_SMALL if args.small_lines else SIGNAL_TO_LINE
        closes = us_signal_closes(ib, tuple(mapping))
        cycle = CycleConfig(signal_to_line=mapping, budget_per_line=args.budget,
                            max_weight=args.max_weight, band=args.band)
        try:
            report = run_cycle(
                broker, closes, risk, cycle,
                state_path=state / "risk.json", journal_path=state / "journal.jsonl",
                starting_capital=ledger.flows[0]["amount"], dry_run=not args.send,
            )
        except ValueError as exc:
            print(f"refused: {exc}")
            return 2
        except OrderNotAcknowledgedError as exc:
            print(f"order failed: {exc}")
            return 4
        except LedgerError as exc:
            print(f"ledger: {exc}")
            return 5

        print(f"{'DRY RUN' if report.dry_run else 'SENT'}  sleeve={args.sleeve}  gate={report.gate}")
        print(f"sleeve equity {report.equity:,.2f} {ledger.currency}  cash {ledger.cash:,.2f}")
        print("target weights: " + ", ".join(f"{s} {w:.1%}" for s, w in sorted(report.weights.items())))
        print("prices: " + ", ".join(f"{s} {broker.prices([s])[s]:.3f} ({src})"
                                     for s, src in sorted(broker.price_sources.items())))
        for o in report.orders:
            status = o.order_id or ("planned" if o.allowed else "blocked")
            print(f"  {o.symbol:<5} {o.quantity:+6d} @ {o.price:.3f}  {status}  {o.reason}")
        if not report.orders:
            print("  no order: every line is within the band")
        return 0
    finally:
        ib.disconnect()


if __name__ == "__main__":
    sys.exit(main())
