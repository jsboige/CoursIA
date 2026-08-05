#!/usr/bin/env python3
"""Tests for verify_running_containers.py.

These cover the static (mask, parse, detect) and orchestration logic.
The ``_container_env`` and ``audit_service`` live bits are stubbed
because they shell out to ``docker`` (no docker in the CI runner).
"""
from __future__ import annotations

import importlib
import json
import sys
from pathlib import Path

import pytest

# Make the script importable as a module (it has a dash in the name).
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
mod = importlib.import_module("verify_running_containers")


def test_mask_empty():
    assert mod._mask("") == "<empty>"


def test_mask_short():
    assert mod._mask("abcd") == "****"
    assert mod._mask("ab") == "****"


def test_mask_long():
    masked = mod._mask("HcE_kr3nU22t7HZ3ElQ6wm8Oz9RaRztOzKo4QEDUkG0TUhTJUM8iHwPQilEyicuJ")
    assert masked.endswith("icuJ")
    assert masked.count("*") == len("HcE_kr3nU22t7HZ3ElQ6wm8Oz9RaRztOzKo4QEDUkG0TUhTJUM8iHwPQilEyicuJ") - 4
    assert "HcE" not in masked
    assert "kr3nU22" not in masked


def test_read_master_env_missing(tmp_path, monkeypatch):
    monkeypatch.setattr(mod, "MASTER_ENV", tmp_path / "does-not-exist")
    assert mod._read_master_env() == {}


def test_read_master_env_basic(tmp_path, monkeypatch):
    p = tmp_path / "master.env"
    # NB: keep all fixtures as clearly-fake shapes so this test file can be
    # pushed through GitHub's secret-scanning push protection. The real
    # WHISPER_API_KEY and HF_TOKEN live ONLY in .secrets/master.env
    # (gitignored). Any production-looking prefix triggers push protection.
    p.write_text(
        "WHISPER_API_KEY=fixture-whisper-XXXX-1234\n"
        'HF_TOKEN="hf_fixtureABCDEF1234567890"\n'
        "# this is a comment\n"
        "OPENAI_API_KEY='sk-test-fixture-value'\n"
        "export FOO=bar\n",
        encoding="utf-8",
    )
    monkeypatch.setattr(mod, "MASTER_ENV", p)
    env = mod._read_master_env()
    assert env["WHISPER_API_KEY"].endswith("1234")
    assert env["HF_TOKEN"] == "hf_fixtureABCDEF1234567890"
    assert env["OPENAI_API_KEY"] == "sk-test-fixture-value"
    assert env["FOO"] == "bar"
    assert "this is a comment" not in env


def test_detect_auth_vars_finds_renamed(tmp_path):
    p = tmp_path / "docker-compose.yml"
    p.write_text(
        "services:\n"
        "  whisper-api:\n"
        "    environment:\n"
        "      - API_KEY=${WHISPER_API_KEY:-}\n",
        encoding="utf-8",
    )
    result = mod._detect_auth_vars(p)
    assert result == {"WHISPER_API_KEY": "API_KEY"}


def test_detect_auth_vars_finds_same_name(tmp_path):
    p = tmp_path / "docker-compose.yml"
    p.write_text(
        "services:\n"
        "  comfyui-qwen:\n"
        "    environment:\n"
        "      - COMFYUI_BEARER_TOKEN=${COMFYUI_BEARER_TOKEN}\n",
        encoding="utf-8",
    )
    result = mod._detect_auth_vars(p)
    assert result == {"COMFYUI_BEARER_TOKEN": "COMFYUI_BEARER_TOKEN"}


def test_detect_auth_vars_ignores_non_auth(tmp_path):
    p = tmp_path / "docker-compose.yml"
    # GPU id is non-secret, not in _AUTH_VAR_RENAMES -> never audited
    p.write_text(
        "services:\n"
        "  whisper-api:\n"
        "    environment:\n"
        "      - CUDA_VISIBLE_DEVICES=${CUDA_VISIBLE_DEVICES:-0}\n",
        encoding="utf-8",
    )
    assert mod._detect_auth_vars(p) == {}


def test_audit_service_compose_missing(tmp_path):
    status, _ = mod.audit_service(tmp_path, {})
    assert status == "COMPOSE_MISSING"


def test_audit_service_no_auth_var(tmp_path):
    (tmp_path / "docker-compose.yml").write_text(
        "services:\n  foo:\n    environment:\n      - PORT=1234\n",
        encoding="utf-8",
    )
    status, _ = mod.audit_service(tmp_path, {})
    assert status == "NO_AUTH_VAR"


def test_audit_service_not_running(tmp_path, monkeypatch):
    (tmp_path / "docker-compose.yml").write_text(
        "services:\n  foo:\n    environment:\n      - API_KEY=${WHISPER_API_KEY:-}\n",
        encoding="utf-8",
    )
    monkeypatch.setattr(mod, "_container_env", lambda c: None)
    status, details = mod.audit_service(tmp_path, {"WHISPER_API_KEY": "x"})
    assert status == "NOT_RUNNING"
    assert details[0]["result"] == "container_not_running"


def test_audit_service_ok(tmp_path, monkeypatch):
    (tmp_path / "docker-compose.yml").write_text(
        "services:\n  foo:\n    environment:\n      - API_KEY=${WHISPER_API_KEY:-}\n",
        encoding="utf-8",
    )
    monkeypatch.setattr(mod, "_container_env", lambda c: {"API_KEY": "secret-1lZ0"})
    status, details = mod.audit_service(tmp_path, {"WHISPER_API_KEY": "secret-1lZ0"})
    assert status == "OK"
    assert details[0]["result"] == "OK"
    assert details[0]["container_masked"].endswith("1lZ0")


def test_audit_service_drift(tmp_path, monkeypatch):
    (tmp_path / "docker-compose.yml").write_text(
        "services:\n  foo:\n    environment:\n      - API_KEY=${WHISPER_API_KEY:-}\n",
        encoding="utf-8",
    )
    monkeypatch.setattr(mod, "_container_env", lambda c: {"API_KEY": "stale-XXXX"})
    status, details = mod.audit_service(tmp_path, {"WHISPER_API_KEY": "new-1lZ0"})
    assert status == "DRIFT"
    assert details[0]["result"] == "DRIFT"


def test_audit_service_master_missing_is_not_drift(tmp_path, monkeypatch):
    # COMFYUI_BEARER_TOKEN is intentionally not in master.env (per-instance
    # password per secrets-hygiene.md). The script must NOT report this
    # as DRIFT, only as MASTER_MISSING (informational).
    (tmp_path / "docker-compose.yml").write_text(
        "services:\n  foo:\n    environment:\n"
        "      - COMFYUI_BEARER_TOKEN=${COMFYUI_BEARER_TOKEN}\n",
        encoding="utf-8",
    )
    monkeypatch.setattr(mod, "_container_env", lambda c: {"COMFYUI_BEARER_TOKEN": "$2b$12.abc"})
    status, details = mod.audit_service(tmp_path, {})  # empty master
    assert status == "OK"
    assert details[0]["result"] == "MASTER_MISSING"


def test_audit_service_container_missing_var(tmp_path, monkeypatch):
    (tmp_path / "docker-compose.yml").write_text(
        "services:\n  foo:\n    environment:\n"
        "      - API_KEY=${WHISPER_API_KEY:-}\n",
        encoding="utf-8",
    )
    # container env has no API_KEY at all -> drift
    monkeypatch.setattr(mod, "_container_env", lambda c: {"OTHER": "x"})
    status, details = mod.audit_service(tmp_path, {"WHISPER_API_KEY": "secret"})
    assert status == "DRIFT"
    assert details[0]["result"] == "CONTAINER_MISSING"


def _make_service_tree(tmp_path: Path, name: str, compose_text: str) -> Path:
    """Create a SERVICES_ROOT layout with one service subdir containing compose."""
    svc = tmp_path / name
    svc.mkdir()
    (svc / "docker-compose.yml").write_text(compose_text, encoding="utf-8")
    return svc


_DRIFT_COMPOSE = (
    "services:\n  drifty:\n    environment:\n"
    "      - API_KEY=${WHISPER_API_KEY:-}\n"
)
_OK_COMPOSE = (
    "services:\n  aligned:\n    environment:\n"
    "      - API_KEY=${WHISPER_API_KEY:-}\n"
)


def test_main_drift_returns_1(tmp_path, monkeypatch, capsys):
    """Smoke: a service with drift makes the script exit 1."""
    _make_service_tree(tmp_path, "drifty", _DRIFT_COMPOSE)
    monkeypatch.setattr(mod, "SERVICES_ROOT", tmp_path)
    monkeypatch.setattr(mod, "_container_env", lambda c: {"API_KEY": "stale"})
    monkeypatch.setattr(sys, "argv", ["verify"])
    rc = mod.main()
    assert rc == 1
    out = capsys.readouterr().out
    assert "DRIFT" in out


def test_main_ok_returns_0(tmp_path, monkeypatch, capsys):
    _make_service_tree(tmp_path, "aligned", _OK_COMPOSE)
    monkeypatch.setattr(mod, "SERVICES_ROOT", tmp_path)
    # Use a clearly-fake fixture value (no real WHISPER_API_KEY literal here;
    # see secrets-hygiene.md and GitHub push-protection).
    master_val = "fixture-whisper-XXXX-1234"
    monkeypatch.setattr(mod, "_container_env", lambda c: {"API_KEY": master_val})
    monkeypatch.setattr(sys, "argv", ["verify"])
    # Patch master read too so the test doesn't depend on the real master.env
    monkeypatch.setattr(mod, "_read_master_env", lambda: {"WHISPER_API_KEY": master_val})
    rc = mod.main()
    assert rc == 0
    out = capsys.readouterr().out
    assert "OK" in out


def test_json_output_is_valid_json(tmp_path, monkeypatch, capsys):
    _make_service_tree(tmp_path, "aligned", _OK_COMPOSE)
    monkeypatch.setattr(mod, "SERVICES_ROOT", tmp_path)
    master_val = "fixture-whisper-XXXX-1234"
    monkeypatch.setattr(mod, "_container_env", lambda c: {"API_KEY": master_val})
    monkeypatch.setattr(mod, "_read_master_env", lambda: {"WHISPER_API_KEY": master_val})
    monkeypatch.setattr(sys, "argv", ["verify", "--json"])
    rc = mod.main()
    out = capsys.readouterr().out
    parsed = json.loads(out)
    assert isinstance(parsed, list)
    assert rc == 0


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-v"]))