"""Read and reconcile the ledger of an IBKR sleeve by hand, without a gateway.

The gateway forgets the executions of earlier days (see
:mod:`paper_harness.ibkr_broker`). When a cycle stops with
``UnreconciledOrderError``, the executions of the order are read in the
account statement, then booked here:

    # orders not accounted for yet
    python -m paper_harness.ibkr_ledger pending
    # the order executed (in full or in part): shares, average price, total commission
    python -m paper_harness.ibkr_ledger resolve inverse-vol:20261006T072301 --filled 12 --price 6.105 --commission 1.25
    # the order never executed
    python -m paper_harness.ibkr_ledger resolve inverse-vol:20261006T072301 --unfilled

``--filled`` is a number of shares: the side comes from the order. Several
executions of one order are booked as one, at their average price. Whatever
quantity is not booked is settled as never executed.

Exit codes: 0 done, 2 refused (no ledger, unknown order, inconsistent figures).
"""
from __future__ import annotations

import argparse
import sys
from datetime import date
from pathlib import Path

from .ibkr_broker import LedgerError, SleeveLedger, _describe


def resolve(ledger: SleeveLedger, order_ref: str, filled: float, price: float | None,
            commission: float) -> str:
    """Book ``filled`` shares of the pending order ``order_ref``, then settle it.

    Return a one-line account of what was booked.
    """
    order = ledger.pending.get(order_ref)
    if order is None:
        raise LedgerError(f"order {order_ref} is not pending")
    remaining = abs(order["quantity"] - order["filled"])
    if filled < 0 or filled > remaining + 1e-9:
        raise LedgerError(f"order {order_ref} has {remaining:g} shares left to book, not {filled:g}")
    if filled and (price is None or price <= 0):
        raise LedgerError("a booked execution needs its average price")
    if commission < 0:
        raise LedgerError("the commission is a cost: pass it as a positive amount")
    if not filled and commission:
        raise LedgerError("an order that never executed has no commission")
    side = 1.0 if order["quantity"] > 0 else -1.0
    if filled:
        ledger.book(f"manual:{order_ref}", order["symbol"], side * filled, price, commission, order_ref=order_ref)
    note = f"booked by hand from the account statement: {filled:g} of {remaining:g} shares executed"
    if order_ref in ledger.pending:
        ledger.settle(order_ref, note)
    else:  # booking the whole remainder already closed the order
        ledger.settled.append({"order_ref": order_ref, **order, "settled": date.today().isoformat(), "note": note})
    if not filled:
        return f"{order_ref}: never executed, settled without booking"
    return f"{order_ref}: {side * filled:+g} {order['symbol']} booked at {price:g}"


def _parse(argv: list[str] | None) -> argparse.Namespace:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--sleeve", default="inverse-vol")
    ap.add_argument("--state-dir", type=Path, default=Path.home() / ".paper_harness")
    sub = ap.add_subparsers(dest="command", required=True)
    sub.add_parser("pending", help="list the orders not accounted for yet")
    res = sub.add_parser("resolve", help="book a pending order from the account statement")
    res.add_argument("order_ref")
    how = res.add_mutually_exclusive_group(required=True)
    how.add_argument("--filled", type=float, help="shares executed (whatever the side)")
    how.add_argument("--unfilled", action="store_true", help="the order never executed")
    res.add_argument("--price", type=float, default=None, help="average execution price")
    res.add_argument("--commission", type=float, default=0.0, help="total commission, ledger currency")
    return ap.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse(argv)
    path = args.state_dir / args.sleeve / "ledger.json"
    if not path.is_file():
        print(f"refused: no ledger at {path}")
        return 2
    ledger = SleeveLedger.load(path)
    if args.command == "pending":
        if not ledger.pending:
            print("no pending order")
        for ref, order in sorted(ledger.pending.items()):
            print(f"{ref}  {_describe(order)}")
        return 0
    try:
        line = resolve(ledger, args.order_ref, 0.0 if args.unfilled else args.filled,
                       args.price, args.commission)
    except LedgerError as exc:
        print(f"refused: {exc}")
        return 2
    ledger.save(path)
    print(line)
    print(f"cash {ledger.cash:,.2f} {ledger.currency}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
