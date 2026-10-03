import json
from datetime import datetime, timezone

import numpy as np
import pytest

from paper_harness.config import RiskConfig
from paper_harness.orchestrator import CycleConfig, run_cycle
from paper_harness.risk import RiskGate

RISK = RiskConfig(max_dd_pct=0.10, daily_var_pct=0.03, vol_spike_threshold=2.0, max_position_pct=0.5)
CFG = CycleConfig(signal_to_line={"SPY": "SXR8", "IEF": "IUSM"}, band=0.0, cash_reserve=0.0)
NOW = datetime(2026, 10, 1, 17, 30, tzinfo=timezone.utc)


class FakeBroker:
    def __init__(self, equity, positions, prices):
        self._equity, self._positions, self._prices = equity, dict(positions), prices
        self.placed = []

    def equity(self):
        return self._equity

    def positions(self):
        return dict(self._positions)

    def prices(self, symbols):
        return {s: self._prices[s] for s in symbols}

    def place(self, symbol, quantity):
        self.placed.append((symbol, quantity))
        return f"id-{len(self.placed)}"


def _closes(daily_vol, seed):
    rng = np.random.default_rng(seed)
    return list(100 * np.cumprod(1 + rng.normal(0, daily_vol, 60)))


SIGNALS = {"SPY": _closes(0.012, 1), "IEF": _closes(0.004, 2)}


def _run(tmp_path, broker, **kw):
    return run_cycle(
        broker, SIGNALS, RISK, kw.pop("cfg", CFG),
        state_path=tmp_path / "risk.json", journal_path=tmp_path / "journal.jsonl",
        starting_capital=10_000.0, now=NOW, **kw,
    )


def test_dry_run_plans_but_sends_nothing(tmp_path):
    broker = FakeBroker(10_000.0, {}, {"SXR8": 50.0, "IUSM": 20.0})
    report = _run(tmp_path, broker)
    assert broker.placed == []
    assert report.dry_run and report.sent == []
    assert {o.symbol for o in report.orders} == {"SXR8", "IUSM"}
    assert all(o.allowed and o.quantity > 0 for o in report.orders)


def test_live_cycle_sends_allowed_orders_sells_first(tmp_path):
    broker = FakeBroker(10_000.0, {"OLD": 10}, {"SXR8": 50.0, "IUSM": 20.0, "OLD": 100.0})
    report = _run(tmp_path, broker, dry_run=False)
    assert broker.placed[0] == ("OLD", -10)
    assert [s for s, _ in broker.placed[1:]] == ["IUSM", "SXR8"]
    assert [o.order_id for o in report.orders] == ["id-1", "id-2", "id-3"]


def test_halted_gate_lets_sells_through_and_blocks_buys(tmp_path):
    gate = RiskGate(RISK, 10_000.0)
    gate.update_equity(12_000.0)
    gate.update_equity(10_000.0)  # -16.7 % from the peak
    gate.save(tmp_path / "risk.json")
    broker = FakeBroker(10_000.0, {"OLD": 10}, {"SXR8": 50.0, "IUSM": 20.0, "OLD": 100.0})
    report = _run(tmp_path, broker, dry_run=False)
    assert broker.placed == [("OLD", -10)]
    blocked = [o for o in report.orders if not o.allowed]
    assert {o.symbol for o in blocked} == {"SXR8", "IUSM"}
    assert all(o.reason.startswith("halted") for o in blocked)


def test_zero_exposure_scale_goes_to_cash(tmp_path):
    cfg = CycleConfig(signal_to_line=CFG.signal_to_line, band=0.0, cash_reserve=0.0, exposure_scale=0.0)
    broker = FakeBroker(10_000.0, {"SXR8": 40, "IUSM": 100}, {"SXR8": 50.0, "IUSM": 20.0})
    report = _run(tmp_path, broker, cfg=cfg, dry_run=False)
    assert sorted(broker.placed) == [("IUSM", -100), ("SXR8", -40)]
    assert all(o.allowed for o in report.orders)


def test_zero_exposure_scale_goes_to_cash_with_the_default_band(tmp_path):
    # Two holdings of 2 % each, under the default 3 % band: an exit sells them anyway.
    cfg = CycleConfig(signal_to_line=CFG.signal_to_line, exposure_scale=0.0)
    assert cfg.band == 0.03
    broker = FakeBroker(10_000.0, {"SXR8": 4, "IUSM": 10}, {"SXR8": 50.0, "IUSM": 20.0})
    _run(tmp_path, broker, cfg=cfg, dry_run=False)
    assert sorted(broker.placed) == [("IUSM", -10), ("SXR8", -4)]


def test_halted_gate_with_zero_exposure_plans_and_sends_every_sale(tmp_path):
    # Breaker tripped and a return to cash asked, default band: allowing sales is not
    # enough, they must also be planned -- including the holding under the band (2 %).
    gate = RiskGate(RISK, 10_000.0)
    gate.update_equity(12_000.0)
    gate.update_equity(10_000.0)
    gate.save(tmp_path / "risk.json")
    cfg = CycleConfig(signal_to_line=CFG.signal_to_line, exposure_scale=0.0)
    broker = FakeBroker(10_000.0, {"SXR8": 40, "IUSM": 10}, {"SXR8": 50.0, "IUSM": 20.0})
    report = _run(tmp_path, broker, cfg=cfg, dry_run=False)
    assert sorted(broker.placed) == [("IUSM", -10), ("SXR8", -40)]
    assert all(o.allowed for o in report.orders)


def test_cycle_appends_to_the_journal_and_persists_the_peak(tmp_path):
    broker = FakeBroker(11_000.0, {}, {"SXR8": 50.0, "IUSM": 20.0})
    _run(tmp_path, broker)
    _run(tmp_path, broker)
    lines = (tmp_path / "journal.jsonl").read_text(encoding="utf-8").splitlines()
    assert len(lines) == 2
    assert json.loads(lines[0])["timestamp"] == NOW.isoformat()
    assert RiskGate.load(RISK, tmp_path / "risk.json", 10_000.0).peak_equity == 11_000.0


def test_inconsistent_position_cap_is_refused(tmp_path):
    risk = RiskConfig(max_dd_pct=0.10, daily_var_pct=0.03, vol_spike_threshold=2.0, max_position_pct=0.25)
    broker = FakeBroker(10_000.0, {}, {"SXR8": 50.0, "IUSM": 20.0})
    with pytest.raises(ValueError, match="RISK_MAX_POSITION_PCT"):
        run_cycle(broker, SIGNALS, risk, CFG, state_path=tmp_path / "r.json",
                  journal_path=tmp_path / "j.jsonl", starting_capital=10_000.0)
