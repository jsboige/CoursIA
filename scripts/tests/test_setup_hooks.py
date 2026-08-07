"""Tests for scripts/setup_hooks.py and scripts/check_hooks_parity.py.

Issue #9888 — these are the organs the harness called for. Tests focus on:
  * inspect() reports correctly when tools are missing
  * declared-hook extraction matches the actual .pre-commit-config.yaml
  * the parity check exit codes are coherent with the gate state

The install path itself is not exercised here (it would touch the user's
``pip`` and ``~/.git/hooks/``); the verify path is exercised at the end
of the actual install by the issue's acceptance gate.
"""
from __future__ import annotations

import importlib.util
import shutil
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
SETUP_HOOKS = HERE.parent / "setup_hooks.py"
CHECK_HOOKS_PARITY = HERE.parent / "check_hooks_parity.py"


def _load(path: Path):
    spec = importlib.util.spec_from_file_location(path.stem, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def _make_repo(tmp_path: Path) -> Path:
    """Create a fake repo with a .git/hooks/ directory and a config file."""
    repo = tmp_path / "fake_repo"
    (repo / ".git" / "hooks").mkdir(parents=True)
    (repo / ".pre-commit-config.yaml").write_text(
        "repos:\n"
        "  - repo: local\n"
        "    hooks:\n"
        "      - id: fake-hook-a\n"
        "      - id: fake-hook-b\n"
    )
    return repo


def test_inspect_reports_missing_tools(tmp_path, monkeypatch):
    """When pre-commit/gitleaks/hook are absent, inspect() surfaces each KO."""
    mod = _load(SETUP_HOOKS)
    repo = _make_repo(tmp_path)

    monkeypatch.setattr(mod, "REPO_ROOT", repo)
    monkeypatch.setattr(mod, "HOOK_PATH", repo / ".git" / "hooks" / "pre-commit")
    monkeypatch.setattr(mod, "CONFIG_PATH", repo / ".pre-commit-config.yaml")
    # Force shutil.which to return None for both binaries.
    monkeypatch.setattr(shutil, "which", lambda name: None)

    state = mod.inspect()
    assert state.precommit_present is False
    assert state.gitleaks_present is False
    assert state.hook_installed is False
    assert state.config_present is True
    assert state.fully_installed is False
    # Notices must mention both install hints.
    assert any("pre-commit" in n for n in state.notices)
    assert any("gitleaks" in n for n in state.notices)


def test_inspect_reports_all_green(tmp_path, monkeypatch):
    """When everything is installed, fully_installed flips to True."""
    mod = _load(SETUP_HOOKS)
    repo = _make_repo(tmp_path)
    (repo / ".git" / "hooks" / "pre-commit").write_text("#!/bin/sh\nexit 0\n")

    monkeypatch.setattr(mod, "REPO_ROOT", repo)
    monkeypatch.setattr(mod, "HOOK_PATH", repo / ".git" / "hooks" / "pre-commit")
    monkeypatch.setattr(mod, "CONFIG_PATH", repo / ".pre-commit-config.yaml")
    monkeypatch.setattr(shutil, "which", lambda name: f"/usr/bin/{name}")

    state = mod.inspect()
    assert state.fully_installed is True
    assert state.errors == []


def test_check_parity_exit_code_when_misconfigured(tmp_path, monkeypatch, capsys):
    """check_hooks_parity.main returns 1 when at least one gate is KO."""
    mod = _load(CHECK_HOOKS_PARITY)
    repo = _make_repo(tmp_path)

    monkeypatch.setattr(mod, "REPO_ROOT", repo)
    monkeypatch.setattr(mod, "CONFIG_PATH", repo / ".pre-commit-config.yaml")
    monkeypatch.setattr(mod, "HOOK_PATH", repo / ".git" / "hooks" / "pre-commit")
    monkeypatch.setattr(shutil, "which", lambda name: None)
    monkeypatch.setattr(sys, "argv", ["check_hooks_parity"])

    rc = mod.main()
    out = capsys.readouterr().out
    assert rc == 1
    assert "KO" in out
    assert "pre-commit on PATH" in out
    assert "gitleaks on PATH" in out


def test_check_parity_exit_code_when_green(tmp_path, monkeypatch, capsys):
    """check_hooks_parity.main returns 0 when every gate is green."""
    mod = _load(CHECK_HOOKS_PARITY)
    repo = _make_repo(tmp_path)
    (repo / ".git" / "hooks" / "pre-commit").write_text("#!/bin/sh\nexit 0\n")

    monkeypatch.setattr(mod, "REPO_ROOT", repo)
    monkeypatch.setattr(mod, "CONFIG_PATH", repo / ".pre-commit-config.yaml")
    monkeypatch.setattr(mod, "HOOK_PATH", repo / ".git" / "hooks" / "pre-commit")
    monkeypatch.setattr(shutil, "which", lambda name: f"/usr/bin/{name}")

    # Mock subprocess.run for validate-config so the gate succeeds even when
    # pre-commit is not actually launchable from this CI env.
    class _FakeProc:
        returncode = 0
        stdout = ""
        stderr = ""

    monkeypatch.setattr(mod.subprocess, "run", lambda *a, **kw: _FakeProc())
    monkeypatch.setattr(sys, "argv", ["check_hooks_parity"])

    rc = mod.main()
    out = capsys.readouterr().out
    assert rc == 0, f"expected rc=0, got rc={rc}, output={out!r}"
    assert "OK" in out


def test_declared_hook_ids_extract(tmp_path, monkeypatch):
    """declared_hook_ids() pulls the right number of ids from a real config."""
    mod = _load(CHECK_HOOKS_PARITY)
    repo = _make_repo(tmp_path)
    monkeypatch.setattr(mod, "CONFIG_PATH", repo / ".pre-commit-config.yaml")
    ids = mod._declared_hook_ids()
    assert ids == ["fake-hook-a", "fake-hook-b"]


def test_declared_hook_ids_missing_config(tmp_path, monkeypatch):
    """declared_hook_ids() raises FileNotFoundError on missing config."""
    mod = _load(CHECK_HOOKS_PARITY)
    repo = tmp_path / "no_config_here"
    repo.mkdir()
    monkeypatch.setattr(mod, "CONFIG_PATH", repo / ".pre-commit-config.yaml")
    try:
        mod._declared_hook_ids()
    except FileNotFoundError:
        return
    raise AssertionError("expected FileNotFoundError")


def test_real_repo_config_parses():
    """Smoke test: the real .pre-commit-config.yaml yields ≥5 hook ids."""
    mod = _load(CHECK_HOOKS_PARITY)
    if not mod.CONFIG_PATH.exists():
        # The script is relocated in some setups; skip rather than fail.
        import pytest
        pytest.skip("real config not found in test environment")
    try:
        ids = mod._declared_hook_ids()
    except RuntimeError as e:
        import pytest
        pytest.skip(f"PyYAML missing in test environment: {e}")
    assert len(ids) >= 5, f"expected ≥5 hooks in real config, got {len(ids)}: {ids}"