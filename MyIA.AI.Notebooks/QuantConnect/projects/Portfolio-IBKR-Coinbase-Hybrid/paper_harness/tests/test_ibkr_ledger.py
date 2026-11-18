from datetime import date

import pytest

from paper_harness.ibkr_broker import SleeveLedger
from paper_harness.ibkr_ledger import main

REF = "inverse-vol:20261006T072301"


def _state(tmp_path, quantity=10):
    path = tmp_path / "inverse-vol" / "ledger.json"
    led = SleeveLedger.open(path, "inverse-vol", "EUR", 1_000.0)
    led.positions["IUSM"] = 20.0
    led.track(REF, "IUSM", quantity, date(2026, 10, 6))
    led.save(path)
    return path


def _resolve(tmp_path, *args):
    return main(["--state-dir", str(tmp_path), "resolve", *args])


def test_resolve_books_the_statement_and_settles_the_order(tmp_path):
    path = _state(tmp_path)
    assert _resolve(tmp_path, REF, "--filled", "6", "--price", "5.0", "--commission", "1.25") == 0
    led = SleeveLedger.load(path)
    assert led.positions == {"IUSM": 26.0} and led.cash == pytest.approx(1_000 - 30 - 1.25)
    assert led.pending == {} and f"manual:{REF}" in led.booked
    (trace,) = led.settled
    assert (trace["order_ref"], trace["filled"]) == (REF, 6.0) and "6 of 10 shares" in trace["note"]


def test_resolve_takes_the_side_from_the_order(tmp_path):
    path = _state(tmp_path, quantity=-8)
    assert _resolve(tmp_path, REF, "--filled", "8", "--price", "5.0") == 0
    led = SleeveLedger.load(path)
    assert led.positions == {"IUSM": 12.0} and led.cash == pytest.approx(1_040.0)
    assert led.pending == {} and len(led.settled) == 1


def test_order_that_never_executed_is_settled_without_booking(tmp_path):
    path = _state(tmp_path)
    assert _resolve(tmp_path, REF, "--unfilled") == 0
    led = SleeveLedger.load(path)
    assert led.positions == {"IUSM": 20.0} and led.cash == pytest.approx(1_000.0)
    assert led.pending == {} and led.settled[0]["filled"] == 0.0


@pytest.mark.parametrize("args", [
    [REF, "--filled", "11", "--price", "5"],  # more than the order
    [REF, "--filled", "3"],  # no price
    [REF, "--filled", "3", "--price", "5", "--commission", "-1"],
    [REF, "--unfilled", "--commission", "1"],
    ["inverse-vol:unknown", "--unfilled"],
])
def test_resolve_refuses_inconsistent_figures(tmp_path, args):
    path = _state(tmp_path)
    before = path.read_text(encoding="utf-8")
    assert _resolve(tmp_path, *args) == 2
    assert path.read_text(encoding="utf-8") == before


def test_pending_lists_the_orders(tmp_path, capsys):
    _state(tmp_path)
    assert main(["--state-dir", str(tmp_path), "pending"]) == 0
    assert f"{REF}  +10 IUSM placed 2026-10-06, +0 booked" in capsys.readouterr().out


def test_missing_ledger_is_refused(tmp_path):
    assert main(["--state-dir", str(tmp_path), "pending"]) == 2
