"""IBKR broker adapter for :func:`paper_harness.orchestrator.run_cycle` (paper only).

:class:`IBKRBroker` implements the orchestrator's ``Broker`` protocol on top of
an ``ib_insync.IB`` connection to an IB Gateway **paper** session. It is built
for the inverse-volatility sleeve in UCITS form: European lines quoted in EUR
on Xetra, driven by signals computed on the equivalent US ETFs.

Four choices shape it:

1. **Contracts by conId.** A Xetra ticker is not always the IBKR symbol: the
   iShares $ Treasury 7-10yr (Dist) line trades as ``IUSM`` on Xetra but its
   IBKR symbol is ``BTMA``, and ``Stock("IUSM", "SMART", "EUR")`` resolves to
   nothing. :data:`UCITS_LINES` keys each line by its contract identifier,
   verified on a paper session.
2. **Sleeve accounting, never the account value.** A paper account carries a
   fictitious capital far larger than any sleeve, and several sleeves may share
   one account until each gets its own sub-account. The sleeve's equity is the
   value of *its* lines plus *its* cash, kept in a :class:`SleeveLedger`. The
   ledger is built from executions tagged with the sleeve's ``orderRef``,
   booked once per ``execId`` (commissions included, even when they arrive
   late), and checked against the account positions: the ledger may hold less
   than the account (another sleeve holds the rest), never more.
3. **Prices.** Delayed snapshots (market data type 3) when real-time data is
   not subscribed, then the ticker's previous close, then the last daily bar.
   A symbol with none of the three raises: planning blind would be worse than
   not planning. :attr:`IBKRBroker.price_sources` says which one was used.
4. **Orders.** Marketable limit orders with a collar (``collar=0.005`` buys at
   most 0.5 % above the reference price), refused unless the account is a
   paper account (``D`` prefix) and the connection is read-write. ``place``
   waits for the fills and books them before returning, so the sells of a cycle
   fund its buys.

The module imports ``ib_insync`` lazily: importing it does not require the
library, and the tests drive the adapter with a fake client.
"""
from __future__ import annotations

import json
import math
import os
from dataclasses import asdict, dataclass, field
from datetime import date, datetime, timezone
from pathlib import Path
from typing import Any, Mapping, Sequence

# IBKR paper accounts start with "D" (DU... individual, DF... advisor master).
PAPER_ACCOUNT_PREFIX = "D"

# IB sends this sentinel for a commission it has not computed yet.
_UNSET_DOUBLE = 1.7976931348623157e308


@dataclass(frozen=True)
class LineSpec:
    """One tradable line: harness symbol -> IBKR contract identifier."""

    con_id: int
    currency: str = "EUR"
    exchange: str = "SMART"
    note: str = ""


# UCITS lines of the inverse-volatility sleeve, resolved by conId on an IB
# Gateway paper session (read-only, 2026-10-03). The small-unit-price lines
# (SPYL, XNAS) keep whole-share rounding precise for a small sleeve.
UCITS_LINES: dict[str, LineSpec] = {
    "SXR8": LineSpec(75776072, note="S&P 500, accumulating, Xetra"),
    "SPYL": LineSpec(663368031, note="S&P 500, accumulating, Xetra, small unit price"),
    "SXRV": LineSpec(81910701, note="Nasdaq-100, accumulating, Xetra"),
    "XNAS": LineSpec(468775632, note="Nasdaq-100, accumulating, Xetra, small unit price"),
    "IUSM": LineSpec(100292090, note="US Treasury 7-10y, distributing; IBKR symbol BTMA"),
    "4GLD": LineSpec(50784405, note="physical gold, Xetra"),
    "XEON": LineSpec(46041702, note="EUR overnight rate (money market)"),
}

# US ETF signal -> UCITS line actually traded.
SIGNAL_TO_LINE: dict[str, str] = {"SPY": "SXR8", "QQQ": "SXRV", "IEF": "IUSM", "GLD": "4GLD"}
SIGNAL_TO_LINE_SMALL: dict[str, str] = {"SPY": "SPYL", "QQQ": "XNAS", "IEF": "IUSM", "GLD": "4GLD"}


class LedgerError(RuntimeError):
    """The sleeve ledger cannot be trusted; stop and investigate."""


class LedgerDriftError(LedgerError):
    """The ledger holds more of a line than the account does."""


# -- sleeve ledger ------------------------------------------------------------


@dataclass
class SleeveLedger:
    """Cash and holdings attributed to one sleeve of a shared account.

    ``booked`` maps every execution already booked to the commission booked
    for it, which makes :meth:`book` idempotent and lets a commission report
    that arrives after its execution be added later.
    """

    name: str
    currency: str
    cash: float
    positions: dict[str, float] = field(default_factory=dict)
    booked: dict[str, float] = field(default_factory=dict)
    flows: list[dict[str, Any]] = field(default_factory=list)

    @property
    def order_ref_prefix(self) -> str:
        return f"{self.name}:"

    @classmethod
    def load(cls, path: Path) -> "SleeveLedger":
        data = json.loads(Path(path).read_text(encoding="utf-8"))
        return cls(**data)

    @classmethod
    def open(cls, path: Path, name: str, currency: str, initial_cash: float | None) -> "SleeveLedger":
        """Load the ledger at ``path``, or create it with ``initial_cash``.

        An existing ledger is never reset: its name and currency must match,
        and ``initial_cash`` is ignored. Creating one requires a positive
        ``initial_cash`` -- the cash attributed to the sleeve.
        """
        path = Path(path)
        if path.is_file():
            ledger = cls.load(path)
            if ledger.name != name or ledger.currency != currency:
                raise LedgerError(
                    f"ledger {path} belongs to sleeve {ledger.name!r} in {ledger.currency}, "
                    f"not {name!r} in {currency}"
                )
            return ledger
        if initial_cash is None or initial_cash <= 0:
            raise LedgerError(f"no ledger at {path}: pass the cash attributed to the sleeve")
        ledger = cls(name=name, currency=currency, cash=float(initial_cash))
        ledger.flows.append({"date": date.today().isoformat(), "amount": float(initial_cash), "note": "opening"})
        ledger.save(path)
        return ledger

    def save(self, path: Path) -> None:
        path = Path(path)
        path.parent.mkdir(parents=True, exist_ok=True)
        tmp = path.with_suffix(path.suffix + ".tmp")
        tmp.write_text(json.dumps(asdict(self), indent=2, sort_keys=True), encoding="utf-8")
        os.replace(tmp, path)

    def deposit(self, amount: float, note: str = "") -> None:
        """Attribute more (or, negative, less) cash to the sleeve."""
        if self.cash + amount < 0:
            raise LedgerError("a withdrawal cannot exceed the sleeve's cash")
        self.cash += amount
        self.flows.append({"date": date.today().isoformat(), "amount": float(amount), "note": note})

    def book(self, exec_id: str, symbol: str, quantity: float, price: float, commission: float) -> bool:
        """Book one execution (``quantity`` signed). Return True if the ledger changed."""
        commission = 0.0 if not math.isfinite(commission) or commission >= _UNSET_DOUBLE else commission
        if exec_id in self.booked:
            extra = commission - self.booked[exec_id]
            if extra <= 0:
                return False
            self.cash -= extra
            self.booked[exec_id] = commission
            return True
        held = self.positions.get(symbol, 0.0) + quantity
        if held < -1e-9:
            raise LedgerError(f"execution {exec_id} would leave {symbol} short in the sleeve")
        if abs(held) < 1e-9:
            self.positions.pop(symbol, None)
        else:
            self.positions[symbol] = held
        self.cash -= quantity * price + commission
        self.booked[exec_id] = commission
        return True


# -- broker -------------------------------------------------------------------


class IBKRBroker:
    """``Broker`` for :func:`~paper_harness.orchestrator.run_cycle` on an IBKR paper account."""

    def __init__(
        self,
        ib: Any,
        lines: Mapping[str, LineSpec],
        ledger: SleeveLedger,
        ledger_path: Path,
        *,
        read_only: bool,
        account: str | None = None,
        collar: float = 0.005,
        fill_timeout: float = 60.0,
        snapshot_wait: float = 6.0,
        market_data_type: int = 3,
    ):
        if not 0.0 < collar < 0.05:
            raise ValueError("collar must be in (0, 5 %)")
        self.ib = ib
        self.lines = dict(lines)
        self.ledger = ledger
        self.ledger_path = Path(ledger_path)
        self.read_only = read_only
        self.collar = collar
        self.fill_timeout = fill_timeout
        self.snapshot_wait = snapshot_wait
        self.market_data_type = market_data_type
        self.account = self._select_account(account)
        self.price_sources: dict[str, str] = {}
        self._contracts: dict[str, Any] = {}
        self._ticks: dict[str, float] = {}
        self._prices: dict[str, float] = {}
        self._synced = False
        for spec in self.lines.values():
            if spec.currency != ledger.currency:
                raise ValueError("every line must be quoted in the ledger currency")

    # -- account ----------------------------------------------------------

    def _select_account(self, account: str | None) -> str:
        accounts = list(self.ib.managedAccounts())
        if account:
            if account not in accounts:
                raise ValueError("requested account is not managed by this connection")
            return account
        if len(accounts) != 1:
            raise ValueError("several accounts are managed: name the one the sleeve lives in")
        return accounts[0]

    @property
    def is_paper(self) -> bool:
        return self.account.startswith(PAPER_ACCOUNT_PREFIX)

    # -- contracts --------------------------------------------------------

    def _contract(self, symbol: str) -> Any:
        if symbol not in self._contracts:
            spec = self.lines.get(symbol)
            if spec is None:
                raise KeyError(f"{symbol} is not a line of this sleeve")
            from ib_insync import Contract

            details = self.ib.reqContractDetails(Contract(conId=spec.con_id, exchange=spec.exchange))
            if not details:
                raise LedgerError(f"conId {spec.con_id} ({symbol}) does not resolve")
            contract = details[0].contract
            if contract.currency != spec.currency:
                raise LedgerError(f"{symbol} trades in {contract.currency}, expected {spec.currency}")
            self._contracts[symbol] = contract
            self._ticks[symbol] = float(details[0].minTick or 0.01)
        return self._contracts[symbol]

    def _symbol_of(self, con_id: int) -> str | None:
        for symbol, spec in self.lines.items():
            if spec.con_id == con_id:
                return symbol
        return None

    # -- ledger synchronisation ------------------------------------------

    def _book_fill(self, fill: Any) -> bool:
        execution = fill.execution
        if not execution.orderRef.startswith(self.ledger.order_ref_prefix):
            return False
        if execution.acctNumber and execution.acctNumber != self.account:
            return False
        symbol = self._symbol_of(fill.contract.conId)
        if symbol is None:
            raise LedgerError(f"execution {execution.execId} tagged for this sleeve on an unknown contract")
        report = fill.commissionReport
        commission = 0.0
        if report is not None and report.execId:
            if report.currency and report.currency != self.ledger.currency:
                raise LedgerError(f"commission of {execution.execId} is in {report.currency}")
            commission = report.commission
        side = 1.0 if execution.side == "BOT" else -1.0
        return self.ledger.book(execution.execId, symbol, side * execution.shares, execution.price, commission)

    def sync(self) -> None:
        """Book today's tagged executions, then check the ledger against the account.

        IBKR returns the executions of the current day only: a cycle that
        leaves an order working must be synced again before midnight.
        """
        changed = False
        for fill in self.ib.reqExecutions():
            changed |= self._book_fill(fill)
        if changed:
            self.ledger.save(self.ledger_path)
        held = {p.contract.conId: float(p.position) for p in self.ib.positions(self.account)}
        for symbol, quantity in self.ledger.positions.items():
            in_account = held.get(self.lines[symbol].con_id, 0.0)
            if quantity > in_account + 1e-9:
                raise LedgerDriftError(
                    f"the sleeve holds {quantity:g} {symbol} but the account only {in_account:g}"
                )
        self._synced = True

    def _ensure_synced(self) -> None:
        if not self._synced:
            self.sync()

    # -- Broker protocol --------------------------------------------------

    def positions(self) -> dict[str, float]:
        self._ensure_synced()
        return dict(self.ledger.positions)

    def equity(self) -> float:
        self._ensure_synced()
        held = [s for s, q in self.ledger.positions.items() if q]
        prices = self.prices(held)
        return self.ledger.cash + sum(q * prices[s] for s, q in self.ledger.positions.items() if q)

    def prices(self, symbols: Sequence[str]) -> dict[str, float]:
        todo = [s for s in symbols if s not in self._prices]
        if todo:
            self._fetch_prices(todo)
        return {s: self._prices[s] for s in symbols}

    def _fetch_prices(self, symbols: Sequence[str]) -> None:
        self.ib.reqMarketDataType(self.market_data_type)
        tickers = {s: self.ib.reqMktData(self._contract(s), "", True, False) for s in symbols}
        for _ in range(max(1, int(self.snapshot_wait / 0.25))):
            if all(_usable(_market(t)) for t in tickers.values()):
                break
            self.ib.sleep(0.25)
        for symbol, ticker in tickers.items():
            price, source = _market(ticker), "delayed" if self.market_data_type in (3, 4) else "live"
            if not _usable(price):
                price, source = getattr(ticker, "close", math.nan), "previous close"
            if not _usable(price):
                bars = self.ib.reqHistoricalData(
                    self._contract(symbol), endDateTime="", durationStr="10 D",
                    barSizeSetting="1 day", whatToShow="TRADES", useRTH=True,
                )
                price, source = (bars[-1].close if bars else math.nan), "last daily bar"
            if not _usable(price):
                raise ValueError(f"no usable price for {symbol}")
            self._prices[symbol] = float(price)
            self.price_sources[symbol] = source

    def place(self, symbol: str, quantity: int) -> str:
        """Send a collared limit order for ``quantity`` shares (signed), wait, book the fills."""
        if not self.is_paper:
            raise PermissionError("IBKRBroker only sends orders to a paper account")
        if self.read_only:
            raise PermissionError(
                "read-only connection: disable 'Read-Only API' on the gateway and reconnect with readonly=False"
            )
        quantity = int(quantity)
        if quantity == 0:
            raise ValueError("quantity must be non-zero")
        self._ensure_synced()
        held = self.ledger.positions.get(symbol, 0.0)
        if quantity < 0 and -quantity > held + 1e-9:
            raise LedgerError(f"selling {-quantity} {symbol} exceeds the {held:g} the sleeve holds")
        reference = self.prices([symbol])[symbol]
        if quantity > 0 and quantity * reference > self.ledger.cash:
            raise LedgerError(f"buying {quantity} {symbol} exceeds the sleeve's cash")
        contract = self._contract(symbol)
        limit = self.limit_price(symbol, quantity, reference)

        from ib_insync import LimitOrder

        stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S")
        order = LimitOrder(
            "BUY" if quantity > 0 else "SELL", abs(quantity), limit,
            tif="DAY", account=self.account, orderRef=f"{self.ledger.order_ref_prefix}{stamp}",
        )
        trade = self.ib.placeOrder(contract, order)
        for _ in range(max(1, int(self.fill_timeout / 0.5))):
            if trade.isDone():
                break
            self.ib.sleep(0.5)
        changed = False
        for fill in trade.fills:
            changed |= self._book_fill(fill)
        if changed:
            self.ledger.save(self.ledger_path)
        return str(trade.order.orderId)

    def limit_price(self, symbol: str, quantity: int, reference: float) -> float:
        """Reference price moved by the collar against us, rounded to the tick."""
        self._contract(symbol)
        tick = self._ticks[symbol]
        raw = reference * (1.0 + self.collar if quantity > 0 else 1.0 - self.collar)
        return round(round(raw / tick) * tick, 10)


def _market(ticker: Any) -> float:
    try:
        return float(ticker.marketPrice())
    except (TypeError, ValueError):
        return math.nan


def _usable(price: Any) -> bool:
    return isinstance(price, (int, float)) and math.isfinite(price) and price > 0


# -- signals ------------------------------------------------------------------


def us_signal_closes(
    ib: Any,
    symbols: Sequence[str] = tuple(SIGNAL_TO_LINE),
    *,
    duration: str = "6 M",
    min_closes: int = 22,
    today: date | None = None,
) -> dict[str, list[float]]:
    """Daily adjusted closes of the US ETFs that drive the sleeve.

    ``ADJUSTED_LAST`` bars include dividends, like the research backtest. The
    bar of the current session is dropped: during US hours it is still
    forming, and a monthly rule loses nothing by reading the previous close.
    """
    from ib_insync import Stock

    today = today or datetime.now(timezone.utc).date()
    out: dict[str, list[float]] = {}
    for symbol in symbols:
        contract = Stock(symbol, "SMART", "USD")
        ib.qualifyContracts(contract)
        bars = ib.reqHistoricalData(
            contract, endDateTime="", durationStr=duration,
            barSizeSetting="1 day", whatToShow="ADJUSTED_LAST", useRTH=True,
        )
        closes = [float(b.close) for b in bars if _bar_date(b.date) < today]
        if len(closes) < min_closes:
            raise ValueError(f"{symbol}: {len(closes)} daily closes, need {min_closes}")
        out[symbol] = closes
    return out


def _bar_date(value: Any) -> date:
    return value.date() if isinstance(value, datetime) else value
