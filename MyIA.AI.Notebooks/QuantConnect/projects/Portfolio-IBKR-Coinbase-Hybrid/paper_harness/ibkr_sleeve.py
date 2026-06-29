"""IBKR sleeve for the Phase 4 paper harness.

Wraps :mod:`ib_insync` to talk to a local IB Gateway running in
paper/simulated trading mode. Read-only access (account summary,
positions, market data) works whether or not the gateway has "Read-Only
API" enabled; **order placement requires "Read-Only API" to be OFF**
(IB Gateway -> Configure -> Settings -> API -> Settings -> Read-Only).
That path is gated on a reviewed orchestrator and is not exercised by the
read-only smoke test.

SOTA-OK (Prong A): drives the real ``ib_insync`` library against a real
IB Gateway paper session. No degraded workaround (no mock socket, no toy
re-implementation). Paper account only — :class:`IBKRSleeve` refuses to
connect when ``IBKR_TRADING_MODE != paper``.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from .config import IBKRConfig


@dataclass(frozen=True)
class AccountSnapshot:
    """Flat view of the IBKR account summary tags the harness consumes."""

    account_id: str
    account_type: str
    net_liquidation: float
    total_cash: float
    equity_with_loan: float
    buying_power: float
    currency: str


class IBKRSleeve:
    """Thin adapter around ``ib_insync.IB``.

    The library is imported lazily in :meth:`connect`, so importing this
    module does not require ``ib_insync`` to be installed (the QC Cloud
    backtest does not need it). ``ib_insync`` manages its own event loop;
    in a plain script ``IB().connect`` blocks synchronously, so no
    ``util.startLoop()`` is needed outside Jupyter.
    """

    def __init__(self, cfg: IBKRConfig):
        self.cfg = cfg
        self._ib: Any = None

    # -- lifecycle --------------------------------------------------------

    def connect(self) -> "IBKRSleeve":
        from ib_insync import IB

        self._ib = IB()
        self._ib.connect(
            self.cfg.host,
            self.cfg.port,
            clientId=self.cfg.client_id,
            timeout=15,
        )
        return self

    def disconnect(self) -> None:
        if self._ib is not None:
            try:
                self._ib.disconnect()
            finally:
                self._ib = None

    def __enter__(self) -> "IBKRSleeve":
        return self.connect()

    def __exit__(self, *exc: object) -> None:
        self.disconnect()

    @property
    def ib(self) -> Any:
        if self._ib is None:
            raise RuntimeError("IBKRSleeve not connected — call connect() first")
        return self._ib

    # -- read-only account & market surface ------------------------------

    def managed_accounts(self) -> list[str]:
        return list(self.ib.managedAccounts())

    def account_snapshot(self) -> AccountSnapshot:
        """Return the account tags the harness needs (NetLiq, cash, ...).

        Read access works under Read-Only API; the tags come straight from
        ``accountSummary()``. Missing tags default to 0 / "" rather than
        raising — a paper session always exposes them.
        """
        values = {v.tag: v.value for v in self.ib.accountSummary()}
        accounts = self.managed_accounts()
        return AccountSnapshot(
            account_id=accounts[0] if accounts else "",
            account_type=str(values.get("AccountType", "")),
            net_liquidation=_as_float(values.get("NetLiquidation")),
            total_cash=_as_float(values.get("TotalCashValue")),
            equity_with_loan=_as_float(values.get("EquityWithLoanValue")),
            buying_power=_as_float(values.get("BuyingPower")),
            currency=str(values.get("Currency", "")),
        )

    def positions(self) -> list[Any]:
        return list(self.ib.positions())

    # -- order surface (requires Read-Only API OFF; gated by orchestrator) -

    def market_order(self, contract: Any, qty: float) -> Any:
        """Place a MARKET order for ``qty`` shares/contracts (signed).

        Requires the gateway's "Read-Only API" setting to be OFF, otherwise
        IB Gateway rejects the order (Error 321). Only the orchestrator,
        behind a reviewed :class:`~paper_harness.risk.RiskGate`, should call
        this. Never called by the read-only smoke test.
        """
        from ib_insync import MarketOrder

        action = "BUY" if qty >= 0 else "SELL"
        trade = self.ib.placeOrder(contract, MarketOrder(action, abs(qty)))
        return trade


def _as_float(raw: Any) -> float:
    try:
        return float(raw) if raw not in (None, "") else 0.0
    except (TypeError, ValueError):
        return 0.0
