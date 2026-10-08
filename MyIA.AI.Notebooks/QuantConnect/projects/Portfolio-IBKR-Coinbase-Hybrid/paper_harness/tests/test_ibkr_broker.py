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
    OrderNotAcknowledgedError,
    PendingOrderError,
    SleeveLedger,
    UnreconciledOrderError,
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
    def __init__(self, order, fills, done=True, status=None):
        self.order, self.fills, self._done = order, fills, done
        self.orderStatus = SimpleNamespace(status=status or ("Filled" if done else "Submitted"))

    def isDone(self):
        return self._done


class FakeIB:
    """The slice of ``ib_insync.IB`` the adapter uses, with scripted answers."""

    def __init__(self, accounts=(PAPER,), market=None, close=None, history=None,
                 account_positions=None, executions=(), fill_price=None, fill_now=True,
                 acknowledged=True, venues=None, rules=None):
        self.accounts = list(accounts)
        self.market, self.close, self.history = market or {}, close or {}, history or {}
        self.account_positions = account_positions or {}
        self.executions = list(executions)
        self.fill_price, self.fill_now, self.acknowledged = fill_price or {}, fill_now, acknowledged
        # venues: symbol -> (validExchanges, marketRuleIds); rules: rule id -> [(low edge, increment)]
        self.venues, self.rules = venues or {}, rules or {}
        self.orders, self.history_calls, self.data_type, self.cancelled = [], [], None, []
        self.open_refs = set()  # orderRef of the orders still working

    def managedAccounts(self):
        return self.accounts

    def accountSummary(self):  # the sleeve must never read the account value
        raise AssertionError("NetLiquidation must not be used for a sleeve")

    def reqContractDetails(self, contract):
        symbol = SYMBOL_OF.get(contract.conId)
        if symbol is None:
            return []
        c = Contract(conId=contract.conId, symbol=symbol, currency="EUR", secType="STK")
        venues, rule_ids = self.venues.get(symbol, ("", ""))
        return [SimpleNamespace(contract=c, minTick=0.01, validExchanges=venues, marketRuleIds=rule_ids)]

    def reqMarketRule(self, rule_id):
        return [SimpleNamespace(lowEdge=e, increment=i) for e, i in self.rules.get(rule_id, [])]

    def cancelOrder(self, order):
        self.cancelled.append(order.orderId)
        self.open_refs.discard(order.orderRef)

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

    def reqAllOpenOrders(self):
        return [SimpleNamespace(order=SimpleNamespace(orderRef=r)) for r in sorted(self.open_refs)]

    def placeOrder(self, contract, order):
        order.orderId = len(self.orders) + 1
        self.orders.append((contract.symbol, order))
        fills = []
        if not self.acknowledged:  # e.g. error 110, which ib_insync logs as a warning only
            return FakeTrade(order, fills, done=False, status="PendingSubmit")
        if not self.fill_now:
            self.open_refs.add(order.orderRef)
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


# Market rules read on a paper session (2026-10-05): SMART ladder of a Xetra ETF
# (rule 2077) next to a venue ladder (rule 1906); the contract's minTick is 0.0001.
XETRA_ETF_RULES = {
    2077: [(0.0, 0.0001), (1.0, 0.0002), (2.0, 0.0005), (5.0, 0.001), (10.0, 0.002), (20.0, 0.005), (50.0, 0.01)],
    1906: [(0.0, 0.0001), (5.0, 0.0002), (10.0, 0.0005)],
}


def test_limit_price_sits_on_the_routes_market_rule(tmp_path):
    ib = FakeIB(market={"SXR8": 743.32, "IUSM": 12.0},
                venues={"SXR8": ("SMART,IBIS2", "2077,1906"), "IUSM": ("SMART,AEB", "2077,2077")},
                rules=XETRA_ETF_RULES)
    b = broker(tmp_path, ib)
    # 743.32 x 1.005 = 747.0366: above 50 EUR the SMART step is 0.01, not the venue's 0.0005
    assert b.tick("SXR8", 747.0366) == 0.01
    assert b.limit_price("SXR8", 34, 743.32) == pytest.approx(747.04)
    # 12 x 0.995 = 11.94 sits in the 10-20 EUR rung (step 0.002)
    assert b.tick("IUSM", 11.94) == 0.002
    assert b.limit_price("IUSM", -10, 12.0) == pytest.approx(11.94)


def test_route_missing_from_the_market_rules_is_refused(tmp_path):
    ib = FakeIB(market={"SXR8": 600.0}, venues={"SXR8": ("IBIS2", "1906")}, rules=XETRA_ETF_RULES)
    with pytest.raises(ValueError, match="no market rule for SXR8 on SMART"):
        broker(tmp_path, ib).limit_price("SXR8", 1, 600.0)


def test_order_never_acknowledged_is_cancelled_and_raises(tmp_path):
    ib = FakeIB(market={"SXR8": 600.0}, acknowledged=False)
    b = broker(tmp_path, ib, fill_timeout=1.0)
    with pytest.raises(OrderNotAcknowledgedError, match=r"never acknowledged the order for \+5 SXR8"):
        b.place("SXR8", 5)
    assert ib.cancelled == [1]
    assert b.ledger.positions == {} and b.ledger.cash == pytest.approx(10_000.0)
    (ref,) = b.ledger.pending  # cancelled: the next sync of the day settles it
    nxt = broker(tmp_path, ib, SleeveLedger.load(tmp_path / "ledger.json"))
    nxt.sync()
    assert nxt.ledger.pending == {} and nxt.ledger.settled[0]["order_ref"] == ref


# -- orders left working: the gateway forgets the executions of earlier days --


def _saved(tmp_path):
    return json.loads((tmp_path / "ledger.json").read_text(encoding="utf-8"))


def _ledger_with_pending(tmp_path, placed, ref="sleeve:20261001T070000"):
    led = ledger(tmp_path)
    led.track(ref, "IUSM", 10, placed)
    led.save(tmp_path / "ledger.json")
    return led, ref


def test_order_is_on_the_ledger_before_it_is_sent(tmp_path):
    ib = FakeIB(market={"IUSM": 5.0})
    b = broker(tmp_path, ib)

    def send_then_die(contract, order):
        assert _saved(tmp_path)["pending"][order.orderRef]["quantity"] == 10
        raise KeyboardInterrupt

    ib.placeOrder = send_then_die
    with pytest.raises(KeyboardInterrupt):
        b.place("IUSM", 10)
    (ref, order), = _saved(tmp_path)["pending"].items()
    assert ref.startswith("sleeve:")
    assert order == {"symbol": "IUSM", "quantity": 10, "filled": 0.0, "placed": date.today().isoformat()}


def test_filled_order_leaves_nothing_pending(tmp_path):
    b = broker(tmp_path, FakeIB(market={"SXR8": 600.0}))
    b.place("SXR8", 5)
    assert b.ledger.pending == {} and _saved(tmp_path)["pending"] == {}


def test_working_order_blocks_the_next_order(tmp_path):
    ib = FakeIB(market={"IUSM": 5.0, "SXR8": 600.0}, fill_now=False)
    b = broker(tmp_path, ib)
    b.place("IUSM", 10)
    with pytest.raises(PendingOrderError, match=r"\+10 IUSM placed .*, \+0 booked"):
        b.place("SXR8", 1)
    assert len(ib.orders) == 1


def test_order_closed_the_same_day_settles_its_unexecuted_rest(tmp_path):
    ib = FakeIB(market={"IUSM": 5.0}, fill_now=False)
    broker(tmp_path, ib).place("IUSM", 10)
    ref = ib.orders[0][1].orderRef
    ib.open_refs.discard(ref)  # the order expires after 4 shares
    ib.executions = [fill(2, "BUY", 4, 5.0, ref, "e9", commission=1.25)]
    ib.account_positions = {2: 4}
    nxt = broker(tmp_path, ib, SleeveLedger.load(tmp_path / "ledger.json"))  # next cycle, same day
    assert nxt.positions() == {"IUSM": 4}
    assert nxt.ledger.pending == {}
    (trace,) = nxt.ledger.settled
    assert (trace["order_ref"], trace["quantity"], trace["filled"]) == (ref, 10, 4.0)
    assert _saved(tmp_path)["settled"] == nxt.ledger.settled


def test_order_of_an_earlier_day_still_working_stays_pending(tmp_path):
    led, ref = _ledger_with_pending(tmp_path, date(2026, 10, 1))
    ib = FakeIB(market={"SXR8": 600.0})
    ib.open_refs.add(ref)
    b = broker(tmp_path, ib, led)
    assert b.positions() == {} and ref in b.ledger.pending
    with pytest.raises(PendingOrderError):
        b.place("SXR8", 1)


def test_closed_order_of_an_earlier_day_stops_the_sync(tmp_path):
    led, ref = _ledger_with_pending(tmp_path, date(2026, 10, 1))
    ib = FakeIB(account_positions={2: 10, 1: 1},
                executions=[fill(1, "BUY", 1, 600.0, "sleeve:today", "e1")])  # unrelated, readable
    b = broker(tmp_path, ib, led)
    with pytest.raises(UnreconciledOrderError, match=rf"{ref} \(\+10 IUSM placed 2026-10-01, \+0 booked\)"):
        b.equity()
    saved = _saved(tmp_path)
    assert saved["positions"] == {"SXR8": 1}  # what could be read is saved before stopping
    assert ref in saved["pending"]


def test_execution_beyond_its_order_is_refused(tmp_path):
    led, ref = _ledger_with_pending(tmp_path, date.today())
    with pytest.raises(LedgerError, match="exceeds the quantity"):
        led.book("e1", "IUSM", 11, 5.0, 0.0, order_ref=ref)
    with pytest.raises(LedgerError, match="on SXR8 for order"):
        led.book("e2", "SXR8", 1, 600.0, 0.0, order_ref=ref)


def test_ledger_written_before_pending_orders_still_loads(tmp_path):
    path = tmp_path / "ledger.json"
    path.write_text(json.dumps({"name": "sleeve", "currency": "EUR", "cash": 100.0,
                                "positions": {}, "booked": {}, "flows": []}), encoding="utf-8")
    led = SleeveLedger.load(path)
    assert led.pending == {} and led.settled == []


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
