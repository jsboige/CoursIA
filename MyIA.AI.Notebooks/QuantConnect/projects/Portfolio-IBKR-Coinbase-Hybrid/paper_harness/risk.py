"""Circuit breakers and pre-trade risk checks for the paper harness.

All checks are pure (no side effects) so they can be unit-tested and
dry-run in the smoke test without placing orders. A :class:`RiskGate`
holds the live accounting state (peak equity, day-start equity) and
returns a :class:`RiskDecision` for each proposed action.

Breakers (mirrors ``.env`` RISK_* and the parent README "Circuit-breaker
-10% MaxDD" requirement):
- drawdown (second loss threshold): halt **and liquidate** when live drawdown
  from peak equity >= ``max_dd_pct``; :attr:`RiskGate.exposure_scale` drops to 0.
- first loss threshold (optional, ``alert_dd_pct``): raise an alert when the
  drawdown reaches it. With ``alert_halves`` the exposure is also halved, and
  comes back to 100 % once the drawdown has recovered to half the threshold
  (hysteresis: re-arming at the threshold itself would flip on every wiggle).
- daily loss: halt when session loss >= ``daily_var_pct``. New buys stop; the
  book is not liquidated (a single bad session is an operational signal). The
  session loss is measured from the last mark of the previous session: pass the
  session date to :meth:`RiskGate.update_equity` and the window rolls on its own
  when the date changes. Without a date the window stays where it is.
- single position: block an order whose notional > ``max_position_pct`` of
  the sleeve capital.
- gross exposure: block an order that would push gross exposure above
  ``max_gross_exposure`` of the sleeve capital.

Persistence: :meth:`RiskGate.save` / :meth:`RiskGate.load` keep the peak
equity, the day-start equity, the date and equity of the last dated mark, a
halt, a liquidation and a halved exposure across restarts. Without them a
restart would reset the drawdown reference and clear a tripped breaker.
"""
from __future__ import annotations

import json
import math
import os
from dataclasses import dataclass
from datetime import date, datetime
from pathlib import Path
from typing import Any, Optional

from .config import RiskConfig

_STATE_KEYS = ("starting_capital", "peak_equity", "day_start_equity", "halted", "halt_reason")
# Added after the first state files were written: default to False / None when absent.
_OPTIONAL_STATE_KEYS = ("liquidate", "reduced", "last_mark_date", "last_mark_equity")


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
        self._require_finite(starting_capital, "starting_capital")
        self.risk = risk
        self.starting_capital = starting_capital
        self.peak_equity = starting_capital
        self.day_start_equity = starting_capital
        self.halted = False
        self.halt_reason: Optional[str] = None
        self.liquidate = False   # second threshold tripped: target exposure 0
        self.reduced = False     # first threshold, halving mode: target exposure 0.5
        self.last_mark_date: Optional[str] = None      # ISO date of the last dated mark
        self.last_mark_equity: Optional[float] = None  # equity of that mark
        self.alert: Optional[str] = None   # set by the latest update_equity, not persisted

    @property
    def exposure_scale(self) -> float:
        """Multiplier the strategy applies to its target weights."""
        if self.liquidate:
            return 0.0
        return 0.5 if self.reduced else 1.0

    @staticmethod
    def _require_finite(value: float, name: str) -> None:
        """Refuse une référence non finie avant toute mutation comptable."""
        if not math.isfinite(value):
            raise ValueError(f"{name} must be finite")

    # -- accounting state -------------------------------------------------

    def update_equity(self, equity: float, day: date | None = None) -> RiskDecision:
        """Record an equity mark and refresh the drawdown / daily breakers.

        ``day`` is the session date of the mark. When it differs from the date of
        the previous dated mark, the daily window first rolls to that mark's
        equity, so ``daily`` is the loss since the last mark of the previous
        session. The first dated mark (fresh gate, or a state file written before
        the dates were kept) opens the window on itself: no halt for a loss that
        happened before the window was known. Without ``day`` the window does not
        move; :meth:`reset_day` rolls it by hand.

        Flips to ``halted`` (rejecting all future orders) if either breaker
        trips, until :meth:`clear_halt` is called: a new session rolls the
        window, it does not clear a halt.
        """
        self._require_finite(equity, "equity")
        if day is not None:
            if isinstance(day, datetime):
                day = day.date()
            stamp = day.isoformat()
            if self.last_mark_date is None or self.last_mark_equity is None:
                self.day_start_equity = equity
            elif stamp != self.last_mark_date:
                self.day_start_equity = self.last_mark_equity
            self.last_mark_date = stamp
            self.last_mark_equity = equity

        if equity > self.peak_equity:
            self.peak_equity = equity

        dd = 0.0
        if self.peak_equity > 0:
            dd = (self.peak_equity - equity) / self.peak_equity
        daily = 0.0
        if self.day_start_equity > 0:
            daily = (self.day_start_equity - equity) / self.day_start_equity

        self.alert = None
        if dd >= self.risk.max_dd_pct:
            self._halt(f"max drawdown {dd:.2%} >= {self.risk.max_dd_pct:.2%}")
            self.liquidate = True
        elif daily >= self.risk.daily_var_pct:
            self._halt(f"daily loss {daily:.2%} >= {self.risk.daily_var_pct:.2%}")

        first = self.risk.alert_dd_pct
        if first is not None:
            if dd >= first:
                self.alert = f"first loss threshold: drawdown {dd:.2%} >= {first:.2%}"
                if self.risk.alert_halves:
                    self.reduced = True
            elif self.reduced and dd <= first / 2:
                self.reduced = False

        if self.halted:
            return RiskDecision(False, self.halt_reason or "halted")
        return RiskDecision(True, f"equity {equity:.2f} dd {dd:.2%} daily {daily:.2%}")

    def reset_day(self, equity: float) -> None:
        """Roll the daily accounting window by hand.

        Dated marks roll it on their own (see :meth:`update_equity`); this stays
        for callers that mark without a date. Do not mix both modes: this call
        leaves the last dated mark unchanged, so a subsequent dated mark can
        roll the window back to that mark's equity.
        """
        self._require_finite(equity, "equity")
        self.day_start_equity = equity

    def _halt(self, reason: str) -> None:
        if not self.halted:
            self.halted = True
            self.halt_reason = reason

    def clear_halt(self) -> None:
        """Manual reset after review.

        Clearing a drawdown liquidation also restarts the measure from a new peak, taken at
        the next equity mark: the sleeve goes back to paper, and with the old peak that mark
        would trip the breaker again at once. A daily-loss halt keeps its peak and halving.
        """
        if self.liquidate:
            self.peak_equity = 0.0
            self.reduced = False
            self.alert = None
        self.halted = False
        self.halt_reason = None
        self.liquidate = False

    # -- persistence ------------------------------------------------------

    def to_state(self) -> dict[str, Any]:
        return {key: getattr(self, key) for key in _STATE_KEYS + _OPTIONAL_STATE_KEYS}

    @classmethod
    def from_state(cls, risk: RiskConfig, state: dict[str, Any]) -> "RiskGate":
        missing = [key for key in _STATE_KEYS if key not in state]
        if missing:
            raise ValueError(f"risk state is missing {missing}")
        gate = cls(risk, float(state["starting_capital"]))
        peak_equity = float(state["peak_equity"])
        day_start_equity = float(state["day_start_equity"])
        cls._require_finite(peak_equity, "peak_equity")
        cls._require_finite(day_start_equity, "day_start_equity")
        gate.peak_equity = peak_equity
        gate.day_start_equity = day_start_equity
        gate.halted = bool(state["halted"])
        gate.halt_reason = state["halt_reason"]
        # A file from before the liquidation flag: a drawdown halt meant liquidation.
        default_liq = gate.halted and str(gate.halt_reason or "").startswith("max drawdown")
        gate.liquidate = bool(state.get("liquidate", default_liq))
        gate.reduced = bool(state.get("reduced", False))
        if state.get("last_mark_date") is not None and state.get("last_mark_equity") is not None:
            last_mark_equity = float(state["last_mark_equity"])
            cls._require_finite(last_mark_equity, "last_mark_equity")
            gate.last_mark_date = str(state["last_mark_date"])
            gate.last_mark_equity = last_mark_equity
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
        for name, value in (
            ("sleeve_capital", sleeve_capital),
            ("order_notional", order_notional),
            ("gross_exposure_after", gross_exposure_after),
        ):
            if not math.isfinite(value):
                return RiskDecision(False, f"{name} must be finite")
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
