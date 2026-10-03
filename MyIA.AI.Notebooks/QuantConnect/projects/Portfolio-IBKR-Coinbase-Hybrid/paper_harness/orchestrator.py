"""One rebalancing cycle of the inverse-volatility sleeve, dry-run by default.

:func:`run_cycle` chains the pure pieces of the harness around a broker:

1. restore the persisted :class:`~paper_harness.risk.RiskGate` and mark the
   current equity (a breaker can trip here);
2. compute target weights from the signal closes
   (:func:`~paper_harness.rebalance.inverse_vol_weights`), optionally scaled
   down (``exposure_scale``, e.g. 0.5 after a first loss threshold);
3. map each signal symbol to the line actually traded (a US ETF signal can
   drive a European UCITS line: the weights carry no currency);
4. plan whole-share orders (:func:`~paper_harness.rebalance.plan_orders`);
5. check every order against the gate, sells first; an order that only
   shrinks a holding passes even when the gate is halted;
6. send the allowed orders, unless ``dry_run`` -- the default;
7. append one JSON line to the journal and save the gate state.

The broker is anything that implements :class:`Broker`; prices, positions
and equity must share one currency. The IBKR adapter lives in
:mod:`paper_harness.ibkr_broker`; :mod:`paper_harness.ibkr_cycle` runs one
cycle with it from the command line.
"""
from __future__ import annotations

import json
from dataclasses import asdict, dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Mapping, Protocol, Sequence

from .config import RiskConfig
from .rebalance import inverse_vol_weights, plan_orders
from .risk import RiskGate


class Broker(Protocol):
    def equity(self) -> float: ...

    def positions(self) -> dict[str, float]: ...

    def prices(self, symbols: Sequence[str]) -> dict[str, float]: ...

    def place(self, symbol: str, quantity: int) -> str:
        """Send a marketable order for ``quantity`` shares (signed); return its id.

        Marketable means a market order, or a limit order with a collar: the
        adapter chooses. An adapter that books its fills before returning
        lets the sells of a cycle fund its buys.
        """
        ...


@dataclass(frozen=True)
class CycleConfig:
    signal_to_line: Mapping[str, str]
    budget_per_line: float = 0.025
    max_weight: float = 0.5
    lookback: int = 21
    band: float = 0.03
    min_notional: float = 0.0
    cash_reserve: float = 0.002
    exposure_scale: float = 1.0


@dataclass
class OrderRecord:
    symbol: str
    quantity: int
    price: float
    allowed: bool
    reason: str
    order_id: str | None = None


@dataclass
class CycleReport:
    timestamp: str
    dry_run: bool
    equity: float
    gate: str
    weights: dict[str, float]
    orders: list[OrderRecord] = field(default_factory=list)

    @property
    def sent(self) -> list[OrderRecord]:
        return [o for o in self.orders if o.order_id is not None]


def run_cycle(
    broker: Broker,
    signal_closes: Mapping[str, Sequence[float]],
    risk: RiskConfig,
    cfg: CycleConfig,
    *,
    state_path: Path,
    journal_path: Path,
    starting_capital: float,
    dry_run: bool = True,
    now: datetime | None = None,
) -> CycleReport:
    if cfg.max_weight > risk.max_position_pct:
        raise ValueError(
            f"max_weight {cfg.max_weight:.0%} exceeds RISK_MAX_POSITION_PCT "
            f"{risk.max_position_pct:.0%}: the gate would block every full-size buy"
        )
    if not 0.0 <= cfg.exposure_scale <= 1.0:
        raise ValueError("exposure_scale must be in [0, 1]")
    if set(signal_closes) != set(cfg.signal_to_line):
        raise ValueError("signal_closes and signal_to_line must name the same symbols")

    gate = RiskGate.load(risk, state_path, starting_capital)
    equity = broker.equity()
    mark = gate.update_equity(equity)

    signal_weights = inverse_vol_weights(
        signal_closes, cfg.budget_per_line, cfg.max_weight, cfg.lookback
    )
    weights = {
        cfg.signal_to_line[s]: w * cfg.exposure_scale for s, w in signal_weights.items()
    }
    held = broker.positions()
    symbols = sorted(set(weights) | {s for s, q in held.items() if q})
    prices = broker.prices(symbols)
    plan = plan_orders(
        weights, held, prices, equity,
        band=cfg.band, min_notional=cfg.min_notional, cash_reserve=cfg.cash_reserve,
    )

    report = CycleReport(
        timestamp=(now or datetime.now(timezone.utc)).isoformat(),
        dry_run=dry_run,
        equity=equity,
        gate=mark.reason,
        weights=weights,
    )
    after = {s: float(q) for s, q in held.items()}
    for order in plan:
        current = after.get(order.symbol, 0.0)
        shrinks = current > 0 and order.quantity < 0 and -order.quantity <= current
        trial = dict(after)
        trial[order.symbol] = current + order.quantity
        gross = sum(abs(q) * prices[s] for s, q in trial.items() if q)
        decision = gate.check_order(
            sleeve_capital=equity,
            order_notional=order.notional,
            gross_exposure_after=gross,
            reduces_exposure=shrinks,
        )
        record = OrderRecord(order.symbol, order.quantity, order.price, decision.allowed, decision.reason)
        if decision.allowed:
            after = trial
            if not dry_run:
                record.order_id = broker.place(order.symbol, order.quantity)
        report.orders.append(record)

    journal_path = Path(journal_path)
    journal_path.parent.mkdir(parents=True, exist_ok=True)
    with journal_path.open("a", encoding="utf-8") as fh:
        fh.write(json.dumps(asdict(report)) + "\n")
    gate.save(state_path)
    return report
