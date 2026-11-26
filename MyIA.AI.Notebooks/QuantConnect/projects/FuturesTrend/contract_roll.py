# -*- coding: utf-8 -*-
"""Pure roll rule for continuous futures (Carver #13, issue #23841).

`_rebalance` orders on the MAPPED contract of each continuous future (#16051).
When the mapping moves to the next contract, a position held on the previous
contract is no longer the one `_rebalance` reads: without a roll it stays
open until its expiry ("Liquidate from delisting"), while a second position
is built on the new contract. Measured on run `bcf50b4b` (#23841): a short
on `CL19M20` kept to its expiry on 2020-05-19 and closed there by a margin
call at 70.0, while `CL22N20` filled at 31.88 the same minute.

The rule implemented here:

1. every non-zero holding on a contract that is not the mapped contract is
   closed;
2. the target is then carried by the mapped contract alone, so the order on
   it is the difference between the target and what the mapped contract
   already holds.

After the orders, the sum of the positions over all the contracts of the
instrument equals the target, which is what item 1 of #23841 asks for.

This module is intentionally **pure Python** (no `AlgorithmImports`), on the
same pattern as `notional_sizing.py`, so that `tests/test_contract_roll.py`
exercises the production rule without the QC Cloud runtime. Contracts are
any hashable keys: QC `Symbol` objects in production, strings in the tests.
"""


def roll_orders(target_qty, holdings, mapped):
    """Orders that roll stale contracts and bring the instrument to target.

    Parameters
    ----------
    target_qty : int
        Signed target in whole contracts for the instrument.
    holdings : dict
        Contract -> current quantity, for the contracts of this instrument
        (the mapped contract may or may not be present). Quantities arrive as
        floats and are rounded, never truncated (see `notional_sizing.py`).
    mapped : hashable
        The contract currently mapped by the continuous future.

    Returns
    -------
    list of (contract, int)
        Close orders for the stale contracts first, in the iteration order of
        `holdings`, then the order on the mapped contract if its delta is not
        zero. An empty list means nothing to send.
    """
    orders = []
    for contract, quantity in holdings.items():
        if contract == mapped:
            continue
        held = int(round(float(quantity)))
        if held != 0:
            orders.append((contract, -held))
    held_on_mapped = int(round(float(holdings.get(mapped, 0.0))))
    delta = int(target_qty) - held_on_mapped
    if delta != 0:
        orders.append((mapped, delta))
    return orders


def aggregate_quantity(holdings):
    """Sum of the rounded positions over all the contracts of an instrument."""
    return sum(int(round(float(q))) for q in holdings.values())
