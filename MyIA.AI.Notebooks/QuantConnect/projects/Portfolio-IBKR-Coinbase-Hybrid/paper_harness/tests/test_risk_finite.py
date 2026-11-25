"""Les valeurs non finies ne doivent jamais contourner le coupe-circuit."""

from datetime import date

import pytest

from paper_harness.config import RiskConfig
from paper_harness.risk import RiskGate


RISK = RiskConfig(max_dd_pct=0.10, daily_var_pct=0.05, vol_spike_threshold=2.0)
NON_FINITE = [float("nan"), float("inf"), float("-inf")]


@pytest.mark.parametrize("value", NON_FINITE)
def test_initial_capital_must_be_finite(value: float) -> None:
    with pytest.raises(ValueError, match="starting_capital must be finite"):
        RiskGate(RISK, value)


@pytest.mark.parametrize("value", NON_FINITE)
@pytest.mark.parametrize("method", ["update_equity", "reset_day"])
def test_invalid_mark_preserves_state(value: float, method: str) -> None:
    gate = RiskGate(RISK, 1000.0)
    gate.update_equity(850.0)
    before = vars(gate).copy()
    with pytest.raises(ValueError, match="equity must be finite"):
        getattr(gate, method)(value)
    assert vars(gate) == before


@pytest.mark.parametrize("value", NON_FINITE)
def test_invalid_dated_mark_does_not_roll_the_window(value: float) -> None:
    gate = RiskGate(RISK, 1000.0)
    gate.update_equity(990.0, date(2026, 1, 5))
    before = vars(gate).copy()
    with pytest.raises(ValueError, match="equity must be finite"):
        gate.update_equity(value, date(2026, 1, 6))
    assert vars(gate) == before


@pytest.mark.parametrize("value", NON_FINITE)
def test_non_finite_saved_dated_mark_is_rejected(value: float) -> None:
    gate = RiskGate(RISK, 1000.0)
    gate.update_equity(990.0, date(2026, 1, 5))
    state = gate.to_state()
    state["last_mark_equity"] = value
    with pytest.raises(ValueError, match="last_mark_equity must be finite"):
        RiskGate.from_state(RISK, state)


@pytest.mark.parametrize("value", NON_FINITE)
@pytest.mark.parametrize("field", ["starting_capital", "peak_equity", "day_start_equity"])
def test_non_finite_saved_state_is_rejected(value: float, field: str) -> None:
    state = RiskGate(RISK, 1000.0).to_state()
    state[field] = value
    with pytest.raises(ValueError, match=f"{field} must be finite"):
        RiskGate.from_state(RISK, state)


@pytest.mark.parametrize("value", NON_FINITE)
@pytest.mark.parametrize("field", ["sleeve_capital", "order_notional", "gross_exposure_after"])
@pytest.mark.parametrize("reduces", [False, True])
def test_non_finite_order_is_rejected(value: float, field: str, reduces: bool) -> None:
    gate = RiskGate(RISK, 1000.0)
    inputs = dict(sleeve_capital=1000.0, order_notional=100.0, gross_exposure_after=100.0)
    inputs[field] = value
    before = vars(gate).copy()
    decision = gate.check_order(**inputs, reduces_exposure=reduces)
    assert not decision.allowed
    assert decision.reason == f"{field} must be finite"
    assert vars(gate) == before


def test_valid_reduction_still_passes_a_halted_gate() -> None:
    gate = RiskGate(RISK, 1000.0)
    gate.update_equity(850.0)
    assert gate.check_order(
        sleeve_capital=850.0, order_notional=800.0,
        gross_exposure_after=0.0, reduces_exposure=True,
    ).allowed
