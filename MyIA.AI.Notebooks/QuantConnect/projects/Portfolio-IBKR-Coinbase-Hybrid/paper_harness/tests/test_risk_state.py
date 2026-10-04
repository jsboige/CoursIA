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


FIRST = RiskConfig(max_dd_pct=0.25, daily_var_pct=0.5, vol_spike_threshold=2.0, alert_dd_pct=0.11)


def test_first_threshold_alone_only_alerts():
    gate = RiskGate(FIRST, 1000.0)
    assert gate.update_equity(880.0)  # -12 %: alert, orders still allowed
    assert "first loss threshold" in gate.alert
    assert gate.exposure_scale == 1.0 and not gate.halted
    gate.update_equity(900.0)
    assert gate.alert is None


def test_halving_comes_back_at_half_the_threshold_not_at_it():
    risk = RiskConfig(max_dd_pct=0.25, daily_var_pct=0.5, vol_spike_threshold=2.0,
                      alert_dd_pct=0.11, alert_halves=True)
    gate = RiskGate(risk, 1000.0)
    gate.update_equity(880.0)
    assert gate.exposure_scale == 0.5
    gate.update_equity(900.0)  # -10 %: back above the threshold, still halved
    assert gate.exposure_scale == 0.5
    gate.update_equity(950.0)  # -5 %: within half the threshold, full exposure
    assert gate.exposure_scale == 1.0


def test_liquidation_and_halving_survive_a_restart(tmp_path):
    risk = RiskConfig(max_dd_pct=0.25, daily_var_pct=0.5, vol_spike_threshold=2.0,
                      alert_dd_pct=0.11, alert_halves=True)
    gate = RiskGate(risk, 1000.0)
    gate.update_equity(880.0)
    gate.save(tmp_path / "r.json")
    assert RiskGate.load(risk, tmp_path / "r.json", 1000.0).exposure_scale == 0.5
    gate.update_equity(700.0)  # -30 %: second threshold
    gate.save(tmp_path / "r.json")
    restored = RiskGate.load(risk, tmp_path / "r.json", 1000.0)
    assert restored.liquidate and restored.exposure_scale == 0.0
    restored.clear_halt()  # manual reset after review lifts the liquidation
    assert restored.exposure_scale == 1.0


def test_clearing_a_liquidation_restarts_from_a_new_peak():
    gate = RiskGate(RiskConfig(max_dd_pct=0.25, daily_var_pct=0.5, vol_spike_threshold=2.0), 1000.0)
    gate.update_equity(700.0)
    gate.clear_halt()
    assert gate.update_equity(690.0).allowed and gate.exposure_scale == 1.0
    assert not gate.update_equity(500.0).allowed and gate.liquidate  # -27.5 % from the new peak


def test_clearing_a_daily_halt_keeps_the_peak_and_the_halving():
    risk = RiskConfig(max_dd_pct=0.25, daily_var_pct=0.05, vol_spike_threshold=2.0,
                      alert_dd_pct=0.11, alert_halves=True)
    gate = RiskGate(risk, 1000.0)
    gate.reset_day(1000.0)
    gate.update_equity(880.0)  # -12 %: daily halt and first threshold
    assert gate.halted and not gate.liquidate and gate.reduced
    gate.clear_halt()
    assert gate.peak_equity == 1000.0 and gate.exposure_scale == 0.5


def test_state_file_without_the_new_flags_keeps_a_drawdown_halt_liquidating(tmp_path):
    path = tmp_path / "old.json"
    path.write_text(json.dumps({"starting_capital": 1000.0, "peak_equity": 1200.0,
                                "day_start_equity": 1070.0, "halted": True,
                                "halt_reason": "max drawdown 10.83% >= 10.00%"}), encoding="utf-8")
    assert RiskGate.load(RISK, path, 1000.0).exposure_scale == 0.0
