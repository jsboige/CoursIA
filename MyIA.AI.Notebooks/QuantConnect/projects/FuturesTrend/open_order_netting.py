# -*- coding: utf-8 -*-
"""Pure pending-order netting rule for `_rebalance` (issue #23962).

`main_carver13._rebalance` computes the gap between the target and the
portfolio position. Since #23961 the position side sums every contract of
the instrument, but the order side still ignores orders that were sent and
not yet filled. A close order that stays unfilled through the next
rebalance is therefore sent again, then again, until it fills: measured on
the #23841 runs (project 38722439, `fix=on`, `roll=on`), the close orders
for `SI27F16` sent from 21 January were resubmitted at every rebalance
while the exchange sat in delivery month, until the engine liquidated the
position at expiry on the 28th. Nothing broke on that run; had trading
resumed, each duplicate would have filled and flipped the position
instead of closing it.

Two remedies exist and item 1 of #23962 asks to measure both:

* ``NET`` — subtract each live order's remaining quantity (quantity minus
  filled) from the gap before deciding. Keeps queue priority and never
  resends a live order; the trade-off is that a stale limit price rides
  until the order itself is revisited.
* ``CANCEL`` — cancel the live orders of the instrument first, then
  recompute the gap from holdings alone. Always a fresh decision; the
  trade-off is lost queue position and possible extra fees.

Both are implemented here so the tranche-4 backtests can drive either
behind a parameter and compare them on the same windows.

This module composes with `contract_roll.roll_orders` without overlapping
it: the roll decides **which** contract carries the target (the mapped
one, stale contracts closed), this rule decides **how much** to actually
send once the live orders are accounted for. It is intentionally **pure
Python** (no `AlgorithmImports`), on the same pattern as
`carry_forecast.py` and `breadth_multiplier.py`: contracts are any
hashable keys — QC `Symbol` objects in production, strings in the tests.
The wiring into `main_carver13` (items 1 and 3) deliberately waits for
the merge of #23847 and #23961, which both carry `main_carver13.py`.
"""


class OpenOrder(object):
    """One live order, direction-signed like the rest of the module.

    ``quantity`` is the signed size as submitted (buy > 0, sell < 0) and
    ``filled_quantity`` the signed size already filled, mirroring the QC
    ``OrderTicket`` convention. The remainder
    ``quantity - filled_quantity`` is what the market still owes the
    algorithm from this order. Fills are already reflected in holdings by
    the time ``_rebalance`` runs, so the remainder is the only live-order
    quantity the gap must subtract.
    """

    __slots__ = ("contract", "quantity", "filled_quantity")

    def __init__(self, contract, quantity, filled_quantity=0):
        self.contract = contract
        self.quantity = int(quantity)
        self.filled_quantity = int(filled_quantity)

    @property
    def remaining(self):
        """Signed quantity the market still owes from this order."""
        return self.quantity - self.filled_quantity


# Rebalance modes (item 1 of #23962: both are measured in the tranche-4
# backtests; the module itself stays mode-agnostic).
NET = "net"
CANCEL = "cancel"


def open_order_remainder(open_orders, contract):
    """Signed sum of the remaining quantities of one contract's live orders.

    Parameters
    ----------
    open_orders : iterable of OpenOrder
        The live orders of the instrument, as returned by
        ``self.transactions.get_open_orders(contract)`` in production
        (one call per contract of the instrument, per item 1).
    contract : hashable
        The contract whose orders to sum.

    Cancelled orders simply stop appearing in the live set, so their
    remainder vanishes from the next call — that is the whole "cancelled
    order" case of item 2.
    """
    total = 0
    for order in open_orders:
        if order.contract == contract:
            total += order.remaining
    return total


def naive_gap(target_qty, held_qty):
    """The gap `_rebalance` computes today: target minus holdings.

    Kept as its own function because the resubmission counter of item 3 is
    exactly the number of rebalances where this gap is non-zero while a
    live order of the same sign already carries the same intent.
    """
    return int(target_qty) - int(round(float(held_qty)))


def would_resubmit(naive, remainder):
    """True when sending ``naive`` would duplicate a live remainder.

    The item-3 statistic: an order the current code sends again while the
    market still owes a remainder in the same direction. Same-sign is the
    operative test — a remainder opposite to the naive gap is a
    legitimate partial state the new order actually needs to fight
    through, not a duplicate.
    """
    if naive == 0 or remainder == 0:
        return False
    return (naive > 0) == (remainder > 0)


class RebalanceDecision(object):
    """What `_rebalance` should do at one rebalance, under one mode.

    Attributes
    ----------
    orders : list of (contract, int)
        Orders to send now, stale contracts first (same order convention
        as `contract_roll.roll_orders`), mapped contract last. Empty when
        the live orders already carry the target.
    cancels : list of hashable
        Contracts whose live orders to cancel first (CANCEL mode only).
    resubmissions_avoided : int
        How many orders this decision does not send that the current code
        would have resent while a live order of the same sign existed —
        the passive statistic of item 3, computed from the same values the
        rule uses, before any runtime hook exists.
    """

    __slots__ = ("orders", "cancels", "resubmissions_avoided")

    def __init__(self, orders, cancels=(), resubmissions_avoided=0):
        self.orders = list(orders)
        self.cancels = list(cancels)
        self.resubmissions_avoided = resubmissions_avoided


def reconcile_orders(target_qty, holdings, mapped, open_orders, mode=NET):
    """Orders that bring the instrument to target with live orders netted.

    Parameters
    ----------
    target_qty : int
        Signed target in whole contracts for the instrument, carried by
        the mapped contract alone once the roll has run.
    holdings : dict
        Contract -> signed held quantity, every contract of the
        instrument included (position side summed since #23961).
    mapped : hashable
        The contract currently mapped by the continuous future.
    open_orders : iterable of OpenOrder
        Live orders of the instrument. Orders with a zero remainder are
        ignored (fully filled or cancelled-and-reported).
    mode : NET or CANCEL

    Returns
    -------
    RebalanceDecision
        NET: each contract's order is its naive gap minus its live
        remainder, so an unfilled order suppresses the resend and an
        oversized remainder buys back the excess. CANCEL: every contract
        with a live remainder is listed for cancellation and the orders
        are the naive gaps — a fresh decision that never stacks behind a
        stale price.

    The judged set is the UNION of ``holdings`` and the contracts of the
    live orders, not ``holdings`` alone: a stale contract whose position
    was already liquidated (held 0) but that still carries a live
    remainder is judged too — exactly the state right after a liquidation
    by a previous rebalance, the #23841 scenario once the engine closed
    the delivery-month position on its own. Without the union, such a
    contract is invisible in both modes (no compensator in NET, absent
    from ``cancels`` in CANCEL) and its live order survives every
    decision that claims to supersede it.
    """
    live = [order for order in open_orders if order.remaining != 0]
    orders = []
    cancels = []
    avoided = 0

    def one_contract(contract, target_share, held):
        nonlocal avoided
        naive = naive_gap(target_share, held)
        if mode == CANCEL:
            if any(order.contract == contract for order in live):
                cancels.append(contract)
            gap = naive
        else:
            gap = naive - open_order_remainder(live, contract)
        if naive != 0 and gap == 0:
            avoided += 1
        if gap != 0:
            orders.append((contract, gap))

    judged = list(holdings)
    seen = set(judged)
    for order in live:
        if order.contract not in seen:
            seen.add(order.contract)
            judged.append(order.contract)
    for contract in judged:
        if contract == mapped:
            continue
        held = int(round(float(holdings.get(contract, 0.0))))
        if held != 0 or open_order_remainder(live, contract) != 0:
            one_contract(contract, 0, held)
    one_contract(
        mapped, target_qty, int(round(float(holdings.get(mapped, 0.0))))
    )
    return RebalanceDecision(orders, cancels, avoided)
