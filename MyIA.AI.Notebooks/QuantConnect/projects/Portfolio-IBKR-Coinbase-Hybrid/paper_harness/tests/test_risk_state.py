import json

import pytest

from paper_harness.config import RiskConfig
from paper_harness.risk import RiskGate

RISK = RiskConfig(max_dd_pct=0.10, daily_var_pct=0.03, vol_spike_threshold=2.0)


def test_missing_file_starts_a_fresh_gate(tmp_path):
    gate = RiskGate.load(RISK, tmp_path / "risk.json", starting_capital=1000.0)
    assert gate.peak_equity == 1000.0
    assert not gate.halted


def test_peak_and_halt_survive_a_restart(tmp_path):
    path = tmp_path / "state" / "risk.json"
    gate = RiskGate(RISK, 1000.0)
    gate.update_equity(1200.0)
    gate.reset_day(1200.0)
    gate.update_equity(1070.0)  # -10.8 % from the peak: breaker trips
    assert gate.halted
    gate.save(path)

    restored = RiskGate.load(RISK, path, starting_capital=1000.0)
    assert restored.peak_equity == 1200.0
    assert restored.halted
    assert "max drawdown" in restored.halt_reason
    assert not restored.check_order(sleeve_capital=1070.0, order_notional=10.0, gross_exposure_after=10.0)


def test_a_halted_gate_still_lets_a_position_shrink():
    gate = RiskGate(RISK, 1000.0)
    gate.update_equity(850.0)
    assert gate.halted
    assert not gate.check_order(sleeve_capital=850.0, order_notional=50.0, gross_exposure_after=900.0)
    assert gate.check_order(
        sleeve_capital=850.0, order_notional=800.0, gross_exposure_after=0.0, reduces_exposure=True
    )


def test_save_leaves_no_temporary_file(tmp_path):
    path = tmp_path / "risk.json"
    RiskGate(RISK, 1000.0).save(path)
    assert [p.name for p in tmp_path.iterdir()] == ["risk.json"]


def test_unreadable_state_raises_instead_of_starting_fresh(tmp_path):
    path = tmp_path / "risk.json"
    path.write_text("{not json", encoding="utf-8")
    with pytest.raises(json.JSONDecodeError):
        RiskGate.load(RISK, path, starting_capital=1000.0)


def test_incomplete_state_raises(tmp_path):
    path = tmp_path / "risk.json"
    path.write_text(json.dumps({"peak_equity": 1.0}), encoding="utf-8")
    with pytest.raises(ValueError, match="missing"):
        RiskGate.load(RISK, path, starting_capital=1000.0)
