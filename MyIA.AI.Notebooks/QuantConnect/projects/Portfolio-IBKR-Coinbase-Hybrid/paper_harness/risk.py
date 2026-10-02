"""Circuit breakers and pre-trade risk checks for the paper harness.

All checks are pure (no side effects) so they can be unit-tested and
dry-run in the smoke test without placing orders. A :class:`RiskGate`
holds the live accounting state (peak equity, day-start equity) and
returns a :class:`RiskDecision` for each proposed action.

Breakers (mirrors ``.env`` RISK_* and the parent README "Circuit-breaker
-10% MaxDD" requirement):
- drawdown: halt when live drawdown from peak equity >= ``max_dd_pct``.
- daily loss: halt when session loss >= ``daily_var_pct``.
- single position: block an order whose notional > ``max_position_pct`` of
  the sleeve capital.
- gross exposure: block an order that would push gross exposure above
  ``max_gross_exposure`` of the sleeve capital.

Persistence: :meth:`RiskGate.save` / :meth:`RiskGate.load` keep the peak
equity, the day-start equity and a halt across restarts. Without them a
restart would reset the drawdown reference and clear a tripped breaker.
"""
from __future__ import annotations

import json
import os
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Optional

from .config import RiskConfig

_STATE_KEYS = ("starting_capital", "peak_equity", "day_start_equity", "halted", "halt_reason")


@dataclass(frozen=True)
class RiskDecision:
    allowed: bool
    reason: str

    def __bool__(self) -> bool:  # convenient ``if gate.check_order(...):``
        return self.allowed


class RiskGate:
    """Stateful circuit-breaker evaluator.

    Tracks peak equity and day-start equity to evaluate the drawdown and
    daily-loss breakers. Call :meth:`update_equity` after each fill/mark,
    and :meth:`check_order` before submitting any order.
    """

    def __init__(self, risk: RiskConfig, starting_capital: float):
        self.risk = risk
        self.starting_capital = starting_capital
        self.peak_equity = starting_capital
        self.day_start_equity = starting_capital
        self.halted = False
        self.halt_reason: Optional[str] = None

    # -- accounting state -------------------------------------------------

    def update_equity(self, equity: float) -> RiskDecision:
        """Record an equity mark and refresh the drawdown / daily breakers.

        Flips to ``halted`` (rejecting all future orders) if either breaker
        trips, until :meth:`reset_day` / :meth:`clear_halt` is called.
        """
        if equity > self.peak_equity:
            self.peak_equity = equity

        dd = 0.0
        if self.peak_equity > 0:
            dd = (self.peak_equity - equity) / self.peak_equity
        daily = 0.0
        if self.day_start_equity > 0:
            daily = (self.day_start_equity - equity) / self.day_start_equity

        if dd >= self.risk.max_dd_pct:
            self._halt(f"max drawdown {dd:.2%} >= {self.risk.max_dd_pct:.2%}")
        elif daily >= self.risk.daily_var_pct:
            self._halt(f"daily loss {daily:.2%} >= {self.risk.daily_var_pct:.2%}")

        if self.halted:
            return RiskDecision(False, self.halt_reason or "halted")
        return RiskDecision(True, f"equity {equity:.2f} dd {dd:.2%} daily {daily:.2%}")

    def reset_day(self, equity: float) -> None:
        """Roll the daily accounting window (call at session/day start)."""
        self.day_start_equity = equity

    def _halt(self, reason: str) -> None:
        if not self.halted:
            self.halted = True
            self.halt_reason = reason

    def clear_halt(self) -> None:
        self.halted = False
        self.halt_reason = None

    # -- persistence ------------------------------------------------------

    def to_state(self) -> dict[str, Any]:
        return {key: getattr(self, key) for key in _STATE_KEYS}

    @classmethod
    def from_state(cls, risk: RiskConfig, state: dict[str, Any]) -> "RiskGate":
        missing = [key for key in _STATE_KEYS if key not in state]
        if missing:
            raise ValueError(f"risk state is missing {missing}")
        gate = cls(risk, float(state["starting_capital"]))
        gate.peak_equity = float(state["peak_equity"])
        gate.day_start_equity = float(state["day_start_equity"])
        gate.halted = bool(state["halted"])
        gate.halt_reason = state["halt_reason"]
        return gate

    def save(self, path: Path) -> None:
        """Write the state atomically (temporary file, then rename)."""
        path = Path(path)
        path.parent.mkdir(parents=True, exist_ok=True)
        tmp = path.with_suffix(path.suffix + ".tmp")
        tmp.write_text(json.dumps(self.to_state(), indent=2), encoding="utf-8")
        os.replace(tmp, path)

    @classmethod
    def load(cls, risk: RiskConfig, path: Path, starting_capital: float) -> "RiskGate":
        """Restore the gate saved at ``path``, or start a fresh one if none exists.

        An unreadable file raises instead of starting fresh: silently
        forgetting a tripped breaker is the failure this method prevents.
        """
        path = Path(path)
        if not path.is_file():
            return cls(risk, starting_capital)
        return cls.from_state(risk, json.loads(path.read_text(encoding="utf-8")))

    # -- pre-trade checks -------------------------------------------------

    def check_order(
        self,
        *,
        sleeve_capital: float,
        order_notional: float,
        gross_exposure_after: float,
        reduces_exposure: bool = False,
    ) -> RiskDecision:
        """Validate a proposed order before submission.

        Parameters are what an execution sleeve can compute just before
        sending: the sleeve's current capital base, the notional of the new
        order, and the resulting gross exposure (sum of abs positions).

        ``reduces_exposure=True`` marks an order that only shrinks an existing
        position (a sell of a long holding). Such an order passes even when the
        gate is halted or the order is large: a breaker exists to cut risk, so
        it must never prevent going back to cash.
        """
        if sleeve_capital <= 0:
            return RiskDecision(False, "sleeve capital <= 0")
        if order_notional < 0:
            return RiskDecision(False, "negative notional")
        if reduces_exposure:
            return RiskDecision(True, "reduces exposure")
        if self.halted:
            return RiskDecision(False, f"halted: {self.halt_reason}")

        single = order_notional / sleeve_capital
        if single > self.risk.max_position_pct:
            return RiskDecision(
                False,
                f"single position {single:.2%} > {self.risk.max_position_pct:.2%}",
            )
        gross = gross_exposure_after / sleeve_capital
        if gross > self.risk.max_gross_exposure + 1e-9:
            return RiskDecision(
                False,
                f"gross exposure {gross:.2%} > {self.risk.max_gross_exposure:.2%}",
            )
        return RiskDecision(True, "ok")
