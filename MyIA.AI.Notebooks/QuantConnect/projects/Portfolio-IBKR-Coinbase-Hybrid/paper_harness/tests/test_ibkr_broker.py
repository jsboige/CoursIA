import json
import math
from datetime import date, datetime, timezone
from types import SimpleNamespace

import numpy as np
import pytest

ib_insync = pytest.importorskip("ib_insync")
from ib_insync import CommissionReport, Contract, Execution, Fill  # noqa: E402

from paper_harness.config import RiskConfig  # noqa: E402
from paper_harness.ibkr_broker import (  # noqa: E402
    IBKRBroker,
    LedgerDriftError,
    LedgerError,
    LineSpec,
    SleeveLedger,
    us_signal_closes,
)
from paper_harness.orchestrator import CycleConfig, run_cycle  # noqa: E402

LINES = {"SXR8": LineSpec(1), "IUSM": LineSpec(2), "4GLD": LineSpec(3)}
SYMBOL_OF = {1: "SXR8", 2: "IUSM", 3: "4GLD"}
PAPER = "DU0001"


class FakeTicker:
    def __init__(self, market=math.nan, close=math.nan):
        self._market, self.close = market, close

    def marketPrice(self):
        return self._market


class FakeTrade:
    def __init__(self, order, fills, done=True):
        self.order, self.fills, self._done = order, fills, done

    def isDone(self):
        return self._done


class FakeIB:
    """The slice of ``ib_insync.IB`` the adapter uses, with scripted answers."""

    def __init__(self, accounts=(PAPER,), market=None, close=None, history=None,
                 account_positions=None, executions=(), fill_price=None, fill_now=True):
        self.accounts = list(accounts)
        self.market, self.close, self.history = market or {}, close or {}, history or {}
        self.account_positions = account_positions or {}
        self.executions = list(executions)
        self.fill_price, self.fill_now = fill_price or {}, fill_now
        self.orders, self.history_calls, self.data_type = [], [], None

    def managedAccounts(self):
        return self.accounts

    def accountSummary(self):  # the sleeve must never read the account value
        raise AssertionError("NetLiquidation must not be used for a sleeve")

    def reqContractDetails(self, contract):
        symbol = SYMBOL_OF.get(contract.conId)
        if symbol is None:
            return []
        c = Contract(conId=contract.conId, symbol=symbol, currency="EUR", secType="STK")
        return [SimpleNamespace(contract=c, minTick=0.01)]

    def reqMarketDataType(self, t):
        self.data_type = t

    def reqMktData(self, contract, generic, snapshot, regulatory):
        s = contract.symbol
        return FakeTicker(self.market.get(s, math.nan), self.close.get(s, math.nan))

    def sleep(self, _seconds):
        pass

    def reqHistoricalData(self, contract, **kw):
        self.history_calls.append((contract.symbol, kw["whatToShow"]))
        return self.history.get(contract.symbol, [])

    def qualifyContracts(self, *contracts):
        return list(contracts)

    def positions(self, account=""):
        return [SimpleNamespace(account=PAPER, contract=Contract(conId=c), position=q)
                for c, q in self.account_positions.items()]

    def reqExecutions(self):
        return list(self.executions)

    def placeOrder(self, contract, order):
        order.orderId = len(self.orders) + 1
        self.orders.append((contract.symbol, order))
        fills = []
        if self.fill_now:
            fills.append(fill(contract.conId, order.action, order.totalQuantity,
                              self.fill_price.get(contract.symbol, order.lmtPrice),
                              order.orderRef, f"e{order.orderId}", commission=1.25))
            q = order.totalQuantity if order.action == "BUY" else -order.totalQuantity
            self.account_positions[contract.conId] = self.account_positions.get(contract.conId, 0) + q
        return FakeTrade(order, fills, done=self.fill_now)


def fill(con_id, action, shares, price, ref, exec_id, commission=0.0, currency="EUR", acct=PAPER):
    side = "BOT" if action == "BUY" else "SLD"
    execution = Execution(execId=exec_id, side=side, shares=shares, price=price, orderRef=ref, acctNumber=acct)
    report = CommissionReport(execId=exec_id, commission=commission, currency=currency)
    return Fill(Contract(conId=con_id), execution, report, datetime(2026, 10, 5, tzinfo=timezone.utc))


def ledger(tmp_path, cash=10_000.0, positions=None):
    led = SleeveLedger.open(tmp_path / "ledger.json", "sleeve", "EUR", cash)
    led.positions.update(positions or {})
    return led


def broker(tmp_path, ib, led=None, read_only=False, **kw):
    led = led or ledger(tmp_path)
    return IBKRBroker(ib, LINES, led, tmp_path / "ledger.json", read_only=read_only, **kw)


# -- prices -------------------------------------------------------------------


def test_prices_fall_back_from_delayed_to_close_to_daily_bar(tmp_path):
    ib = FakeIB(market={"SXR8": 600.0}, close={"IUSM": 4.5},
                history={"4GLD": [SimpleNamespace(close=90.0), SimpleNamespace(close=91.0)]})
    b = broker(tmp_path, ib)
    assert b.prices(["SXR8", "IUSM", "4GLD"]) == {"SXR8": 600.0, "IUSM": 4.5, "4GLD": 91.0}
    assert b.price_sources == {"SXR8": "delayed", "IUSM": "previous close", "4GLD": "last daily bar"}
    assert ib.data_type == 3 and ib.history_calls == [("4GLD", "TRADES")]


def test_missing_price_raises(tmp_path):
    with pytest.raises(ValueError, match="no usable price for SXR8"):
        broker(tmp_path, FakeIB()).prices(["SXR8"])


def test_unknown_conid_is_refused(tmp_path):
    b = IBKRBroker(FakeIB(), {"XXXX": LineSpec(99)}, ledger(tmp_path), tmp_path / "l.json", read_only=True)
    with pytest.raises(LedgerError, match="does not resolve"):
        b.prices(["XXXX"])


# -- sleeve accounting --------------------------------------------------------


def test_equity_is_the_sleeve_not_the_account(tmp_path):
    # the account holds 500 SXR8 (other sleeves); this sleeve holds 10 of them
    ib = FakeIB(market={"SXR8": 600.0}, account_positions={1: 500})
    b = broker(tmp_path, ib, ledger(tmp_path, cash=4_000.0, positions={"SXR8": 10}))
    assert b.equity() == pytest.approx(4_000.0 + 10 * 600.0)
    assert b.positions() == {"SXR8": 10}


def test_booking_is_idempotent_and_takes_a_late_commission(tmp_path):
    led = ledger(tmp_path, cash=1_000.0)
    assert led.book("e1", "IUSM", 10, 5.0, 0.0)
    assert not led.book("e1", "IUSM", 10, 5.0, 0.0)  # same execution twice
    assert led.book("e1", "IUSM", 10, 5.0, 1.25)  # its commission report arrives
    assert not led.book("e1", "IUSM", 10, 5.0, 1.7976931348623157e308)  # unset sentinel
    assert led.positions == {"IUSM": 10} and led.cash == pytest.approx(1_000.0 - 50.0 - 1.25)


def test_sync_books_only_this_sleeves_executions(tmp_path):
    ib = FakeIB(account_positions={2: 30}, executions=[
        fill(2, "BUY", 10, 5.0, "sleeve:20261005", "e1", commission=1.25),
        fill(2, "BUY", 20, 5.0, "other:20261005", "e2"),  # another sleeve
        fill(2, "BUY", 5, 5.0, "sleeve:20261005", "e3", acct="DU0002"),  # another account
    ])
    b = broker(tmp_path, ib)
    b.sync()
    assert b.ledger.positions == {"IUSM": 10}
    saved = json.loads((tmp_path / "ledger.json").read_text(encoding="utf-8"))
    assert saved["booked"] == {"e1": 1.25} and saved["cash"] == pytest.approx(10_000 - 50 - 1.25)


def test_ledger_holding_more_than_the_account_is_drift(tmp_path):
    ib = FakeIB(account_positions={1: 5})
    b = broker(tmp_path, ib, ledger(tmp_path, positions={"SXR8": 10}))
    with pytest.raises(LedgerDriftError, match="holds 10 SXR8 but the account only 5"):
        b.positions()


def test_commission_in_another_currency_is_refused(tmp_path):
    ib = FakeIB(account_positions={2: 10},
                executions=[fill(2, "BUY", 10, 5.0, "sleeve:x", "e1", commission=1.0, currency="USD")])
    with pytest.raises(LedgerError, match="commission"):
        broker(tmp_path, ib).sync()


def test_existing_ledger_is_never_reset(tmp_path):
    led = ledger(tmp_path, cash=10_000.0)
    led.book("e1", "IUSM", 10, 5.0, 0.0)
    led.save(tmp_path / "ledger.json")
    again = SleeveLedger.open(tmp_path / "ledger.json", "sleeve", "EUR", 99_999.0)
    assert again.cash == pytest.approx(9_950.0)
    with pytest.raises(LedgerError, match="belongs to sleeve"):
        SleeveLedger.open(tmp_path / "ledger.json", "other", "EUR", None)
    with pytest.raises(LedgerError, match="no ledger"):
        SleeveLedger.open(tmp_path / "missing.json", "sleeve", "EUR", None)


# -- orders -------------------------------------------------------------------


def test_place_refuses_a_read_only_connection(tmp_path):
    b = broker(tmp_path, FakeIB(market={"SXR8": 600.0}), read_only=True)
    with pytest.raises(PermissionError, match="read-only"):
        b.place("SXR8", 1)


def test_place_refuses_an_account_that_is_not_paper(tmp_path):
    b = broker(tmp_path, FakeIB(accounts=("U1234",), market={"SXR8": 600.0}))
    assert not b.is_paper
    with pytest.raises(PermissionError, match="paper"):
        b.place("SXR8", 1)


def test_place_sends_a_collared_limit_and_books_the_fill(tmp_path):
    ib = FakeIB(market={"SXR8": 600.0}, fill_price={"SXR8": 600.10})
    b = broker(tmp_path, ib)
    order_id = b.place("SXR8", 5)
    symbol, order = ib.orders[0]
    assert order_id == "1" and symbol == "SXR8"
    assert (order.orderType, order.action, order.totalQuantity, order.tif) == ("LMT", "BUY", 5, "DAY")
    assert order.lmtPrice == pytest.approx(603.0) and order.account == PAPER
    assert order.orderRef.startswith("sleeve:")
    assert b.ledger.positions == {"SXR8": 5}
    assert b.ledger.cash == pytest.approx(10_000 - 5 * 600.10 - 1.25)
    assert json.loads((tmp_path / "ledger.json").read_text(encoding="utf-8"))["positions"] == {"SXR8": 5}


def test_sell_limit_is_below_the_reference(tmp_path):
    b = broker(tmp_path, FakeIB(market={"IUSM": 4.50}))
    assert b.limit_price("IUSM", -10, 4.50) == pytest.approx(4.48)


def test_place_refuses_to_sell_shares_the_sleeve_does_not_hold(tmp_path):
    ib = FakeIB(market={"SXR8": 600.0}, account_positions={1: 100})  # other sleeves' shares
    b = broker(tmp_path, ib, ledger(tmp_path, positions={"SXR8": 2}))
    with pytest.raises(LedgerError, match="exceeds the 2 the sleeve holds"):
        b.place("SXR8", -3)


def test_place_refuses_a_buy_beyond_the_sleeves_cash(tmp_path):
    b = broker(tmp_path, FakeIB(market={"SXR8": 600.0}), ledger(tmp_path, cash=1_000.0))
    with pytest.raises(LedgerError, match="cash"):
        b.place("SXR8", 2)


def test_unfilled_order_is_booked_by_the_next_sync(tmp_path):
    ib = FakeIB(market={"IUSM": 5.0}, fill_now=False)
    b = broker(tmp_path, ib)
    b.place("IUSM", 10)
    assert b.ledger.positions == {}
    ref = ib.orders[0][1].orderRef
    ib.executions = [fill(2, "BUY", 10, 5.0, ref, "e9", commission=1.25)]
    ib.account_positions = {2: 10}
    b.sync()
    assert b.ledger.positions == {"IUSM": 10}


# -- signals and full cycle ---------------------------------------------------


def _bars(n, seed, vol, last_day):
    rng = np.random.default_rng(seed)
    closes = 100 * np.cumprod(1 + rng.normal(0, vol, n))
    days = [date.fromordinal(last_day.toordinal() - (n - 1 - i)) for i in range(n)]
    return [SimpleNamespace(date=d, close=float(c)) for d, c in zip(days, closes)]


def test_signal_closes_drop_the_session_in_progress():
    today = date(2026, 10, 5)
    ib = FakeIB(history={"SPY": _bars(30, 1, 0.01, today)})
    closes = us_signal_closes(ib, ("SPY",), today=today)
    assert len(closes["SPY"]) == 29
    assert ib.history_calls == [("SPY", "ADJUSTED_LAST")]
    with pytest.raises(ValueError, match="need 40"):
        us_signal_closes(ib, ("SPY",), today=today, min_closes=40)


def test_dry_cycle_plans_on_sleeve_equity(tmp_path):
    ib = FakeIB(market={"SXR8": 600.0, "IUSM": 4.5, "4GLD": 90.0}, account_positions={1: 1_000})
    b = broker(tmp_path, ib, ledger(tmp_path, cash=20_000.0))
    today = date(2026, 10, 5)
    ib.history = {"SPY": _bars(60, 1, 0.012, today), "IEF": _bars(60, 2, 0.004, today),
                  "GLD": _bars(60, 3, 0.009, today)}
    closes = us_signal_closes(ib, ("SPY", "IEF", "GLD"), today=today)
    risk = RiskConfig(max_dd_pct=0.25, daily_var_pct=0.05, vol_spike_threshold=2.0, max_position_pct=0.5)
    cfg = CycleConfig(signal_to_line={"SPY": "SXR8", "IEF": "IUSM", "GLD": "4GLD"}, budget_per_line=0.025)
    report = run_cycle(b, closes, risk, cfg, state_path=tmp_path / "risk.json",
                       journal_path=tmp_path / "journal.jsonl", starting_capital=20_000.0)
    assert report.dry_run and report.equity == pytest.approx(20_000.0)
    assert ib.orders == [] and report.orders
    invested = sum(o.quantity * o.price for o in report.orders)
    assert 0 < invested <= 20_000.0
