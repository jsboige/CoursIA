"""Rebalancing planner for the paper harness: target weights -> whole-share orders.

Two pure steps, no venue call, so both can be unit-tested and dry-run before
the orchestrator sends anything:

1. :func:`inverse_vol_weights` computes the target weights of an
   inverse-volatility sleeve (the ``Cloud-VolTargeting`` v2 rule): each line
   receives ``budget / realized_vol``, capped per line, and the total is scaled
   down to 100 % when it exceeds it. The remainder stays in cash.
2. :func:`plan_orders` turns target weights into signed whole-share orders,
   given the current positions, prices and equity. A tolerance band skips
   trades too small to be worth their fee, a minimum notional skips orders a
   broker would reject or charge disproportionately, and sells are listed
   before buys so the buys are funded.

Volatility convention: simple daily returns, sample standard deviation
(``ddof=1``), annualised with sqrt(252) -- the convention of the research
backtest that selected the rule. ``Cloud-VolTargeting/main.py`` uses log
returns over 20 returns with ``ddof=0``; on daily data the two differ by a few
percent of the weight, well inside the tolerance band.
"""
from __future__ import annotations

import math
from dataclasses import dataclass
from statistics import stdev
from typing import Mapping, Sequence

TRADING_DAYS = 252


def realized_vol(closes: Sequence[float], lookback: int = 21) -> float | None:
    """Annualised volatility of the last ``lookback`` simple daily returns.

    Needs ``lookback + 1`` closes. Returns ``None`` when the history is too
    short or contains a non-positive price, so the caller can leave the line
    out instead of trading on a wrong number.
    """
    if lookback < 2 or len(closes) < lookback + 1:
        return None
    window = [float(c) for c in closes[-(lookback + 1):]]
    if any(not math.isfinite(c) or c <= 0 for c in window):
        return None
    returns = [b / a - 1.0 for a, b in zip(window[:-1], window[1:])]
    return stdev(returns) * math.sqrt(TRADING_DAYS)


def inverse_vol_weights(
    closes: Mapping[str, Sequence[float]],
    budget_per_line: float,
    max_weight: float = 0.5,
    lookback: int = 21,
) -> dict[str, float]:
    """Target weights ``min(budget_per_line / vol, max_weight)``, total capped at 1.

    ``budget_per_line`` is the volatility budget of one line (``0.025`` for the
    v2 rule: a 10 % portfolio target split over four lines). A line whose
    volatility cannot be measured is left out, which leaves its share in cash.
    """
    if budget_per_line <= 0 or max_weight <= 0:
        raise ValueError("budget_per_line and max_weight must be positive")
    weights: dict[str, float] = {}
    for symbol, series in closes.items():
        vol = realized_vol(series, lookback)
        if vol is None or vol <= 0:
            continue
        weights[symbol] = min(budget_per_line / vol, max_weight)
    total = sum(weights.values())
    if total > 1.0:
        weights = {s: w / total for s, w in weights.items()}
    return weights


@dataclass(frozen=True)
class OrderIntent:
    """One planned order. ``quantity`` is signed: positive buys, negative sells."""

    symbol: str
    quantity: int
    price: float
    current_weight: float
    target_weight: float

    @property
    def notional(self) -> float:
        return abs(self.quantity) * self.price

    @property
    def side(self) -> str:
        return "BUY" if self.quantity > 0 else "SELL"


def plan_orders(
    target_weights: Mapping[str, float],
    positions: Mapping[str, float],
    prices: Mapping[str, float],
    equity: float,
    *,
    band: float = 0.0,
    min_notional: float = 0.0,
    cash_reserve: float = 0.0,
) -> list[OrderIntent]:
    """Whole-share orders that move ``positions`` toward ``target_weights``.

    - ``equity``: net liquidation value of the sleeve, in the price currency.
    - ``band``: skip a line when the value to trade is below ``band * equity``
      (``0.03`` = 3 %). This is the rule the selection backtest simulated, so
      the harness reproduces it rather than inventing another one.
    - ``min_notional``: skip an order whose value is below this amount.
    - ``cash_reserve``: fraction of equity kept out of the targets to pay
      commissions, so the buys never overdraw the account.

    Target quantities are rounded down, so the planned holdings never exceed
    the targets. Every symbol held but absent from ``target_weights`` has a
    target of zero. A symbol without a positive price raises ``ValueError``:
    planning blind would be worse than not planning.
    """
    if equity <= 0:
        raise ValueError("equity must be positive")
    if not 0.0 <= cash_reserve < 1.0:
        raise ValueError("cash_reserve must be in [0, 1)")
    investable = equity * (1.0 - cash_reserve)
    orders: list[OrderIntent] = []
    for symbol in sorted(set(target_weights) | {s for s, q in positions.items() if q}):
        price = prices.get(symbol)
        if price is None or not math.isfinite(price) or price <= 0:
            raise ValueError(f"no usable price for {symbol}")
        target_w = max(0.0, float(target_weights.get(symbol, 0.0)))
        held = float(positions.get(symbol, 0.0))
        wanted = math.floor(target_w * investable / price + 1e-9)
        delta = int(round(wanted - held))
        if delta == 0:
            continue
        value = abs(delta) * price
        if value < band * equity or value < min_notional:
            continue
        orders.append(
            OrderIntent(
                symbol=symbol,
                quantity=delta,
                price=price,
                current_weight=held * price / equity,
                target_weight=target_w,
            )
        )
    orders.sort(key=lambda o: (o.quantity > 0, o.symbol))
    return orders
