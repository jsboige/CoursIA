from pathlib import Path

import pytest

from paper_harness.config import RiskConfig, _load_env_file, load_config

ALERT_KEYS = ("RISK_MAX_DD_PCT", "RISK_ALERT_DD_PCT", "RISK_ALERT_HALVES")
TEMPLATE = Path(__file__).resolve().parents[2] / ".env.template"


def test_inline_comments_are_not_part_of_the_value(tmp_path):
    path = tmp_path / ".env"
    path.write_text('A=0.25   # comment\nB=true # x\nC="p#ss # kept"\nD=p#ss\nE=\nF=    # empty\n', encoding="utf-8")
    assert _load_env_file(path) == {"A": "0.25", "B": "true", "C": "p#ss # kept", "D": "p#ss", "E": "", "F": ""}


def test_the_template_loads_with_its_safe_defaults(monkeypatch):
    for key in _load_env_file(TEMPLATE):
        monkeypatch.delenv(key, raising=False)
    cfg = load_config(TEMPLATE)
    assert cfg.ibkr.is_paper and cfg.coinbase.sandbox and cfg.binance.testnet
    assert cfg.risk.max_dd_pct == 0.10 and cfg.risk.alert_dd_pct is None and not cfg.risk.alert_halves


@pytest.fixture
def env_file(tmp_path, monkeypatch):
    for key in ALERT_KEYS:
        monkeypatch.delenv(key, raising=False)

    def write(*lines):
        path = tmp_path / ".env"
        path.write_text("\n".join(lines) + "\n", encoding="utf-8")
        return path
    return write


def test_first_threshold_is_off_by_default(env_file):
    risk = load_config(env_file("RISK_MAX_DD_PCT=0.25", "RISK_ALERT_DD_PCT=")).risk
    assert risk.alert_dd_pct is None and not risk.alert_halves


def test_first_threshold_is_read(env_file):
    path = env_file("RISK_MAX_DD_PCT=0.25", "RISK_ALERT_DD_PCT=0.11", "RISK_ALERT_HALVES=true")
    risk = load_config(path).risk
    assert risk.alert_dd_pct == 0.11 and risk.alert_halves


@pytest.mark.parametrize("raw", ["11%", "0", "1.5", "0.25"])
def test_a_malformed_first_threshold_raises(env_file, raw):
    with pytest.raises(ValueError):
        load_config(env_file("RISK_MAX_DD_PCT=0.25", f"RISK_ALERT_DD_PCT={raw}"))


def test_first_threshold_must_sit_below_the_second():
    with pytest.raises(ValueError):
        RiskConfig(max_dd_pct=0.10, daily_var_pct=0.03, vol_spike_threshold=2.0, alert_dd_pct=0.10)
