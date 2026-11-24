# -*- coding: utf-8 -*-
"""Pure futures sizing on notional (Carver #13, issue #23824).

`set_holdings` sizes a future on its initial margin, which is 5 to 15 % of
the notional: an order sized that way buys 7 to 20 times the notional the
weight asks for. The `fix` branch of `main_carver13.CarverThirteen._rebalance`
targets whole contracts on notional instead:

    target_contracts = round(target_weight * total_portfolio_value
                             / (price * contract_multiplier))

then sends the difference with the current holding as a market order.

This module is intentionally **pure Python** (no `AlgorithmImports`), on the
same pattern as `breadth_multiplier.py` and `carry_forecast.py`, so that
`tests/test_notional_sizing.py` exercises the production formula without the
QC Cloud runtime.
"""


def target_contracts(target_weight, total_portfolio_value, price, multiplier):
    """Whole contracts whose notional is closest to the target weight.

    Parameters
    ----------
    target_weight : float
        Signed target weight of the instrument (fraction of portfolio value).
    total_portfolio_value : float
        Portfolio value the weight applies to.
    price : float
        Current price of the traded contract.
    multiplier : float
        Contract multiplier (`symbol_properties.contract_multiplier`).

    Returns
    -------
    int
        Signed number of contracts, rounded half to even (Python `round`).
        Returns 0 for a zero weight, or when the price or the multiplier is
        not positive (no notional can be computed).
    """
    if target_weight == 0.0 or price <= 0.0 or multiplier <= 0.0:
        return 0
    return int(round(
        target_weight * total_portfolio_value / (price * multiplier)
    ))


def contract_delta(target_qty, current_holding):
    """Contracts to send to move from the current holding to the target.

    Futures quantities are integral on QC, but the holding arrives as a
    float: it is rounded, not truncated, so that a holding read as
    `2.9999999` counts as 3 contracts and not 2.
    """
    return int(target_qty) - int(round(float(current_holding)))
