"""Tests for scripts/check_hooks_parity.py (issue #9888, suite of #9895).

These tests cover the PyYAML-aware walker that replaces the regex
pairing in ``scripts/setup_hooks.py --check-parity`` (regex pairs
each id with the FIRST entry that follows, producing false pairings
such as ``gitleaks -> strip_probe_banner.py``).

The previously-shipped test file ``test_setup_hooks.py`` (from my
superseded #9893) targeted an ``inspect()`` / ``class SetupResult``
API that lives in the pre-#9895 codebase. Per C9888-bis-L3, tests
must reflect the API of the target codebase; ``setup_hooks.py`` on
main no longer exposes those symbols, so the tests here cover only
``check_hooks_parity.py`` directly.
"""
from __future__ import annotations

import importlib.util
import shutil
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
CHECK_HOOKS_PARITY = HERE.parent / "check_hooks_parity.py"


def _load(path: Path):
    spec = importlib.util.spec_from_file_location(path.stem, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def _make_repo(tmp_path: Path, config_text: str) -> Path:
    """Create a fake repo with a .git/hooks/ directory and a config file."""
    repo = tmp_path / "fake_repo"
    (repo / ".git" / "hooks").mkdir(parents=True)
    (repo / ".pre-commit-config.yaml").write_text(config_text, encoding="utf-8")
    return repo


# --- Gate 1: config declared -------------------------------------------------

def test_declared_hook_ids_real_config():
    """Smoke test: the real .pre-commit-config.yaml yields >= 5 hook ids."""
    mod = _load(CHECK_HOOKS_PARITY)
    if not mod.CONFIG_PATH.exists():
        import pytest
        pytest.skip("real config not found in test environment")
    try:
        ids = mod._declared_hook_ids()
    except RuntimeError as e:
        import pytest
        pytest.skip(f"PyYAML missing in test environment: {e}")
    # Real config has 6 hooks (gitleaks + 5 local) as of #9895.
    assert len(ids) >= 5, f"expected >= 5 hooks in real config, got {len(ids)}: {ids}"


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


def test_declared_hook_ids_extract(tmp_path, monkeypatch):
    """declared_hook_ids() pulls the right number of ids from a fake config."""
    mod = _load(CHECK_HOOKS_PARITY)
    config_text = (
        "repos:\n"
        "  - repo: local\n"
        "    hooks:\n"
        "      - id: fake-hook-a\n"
        "      - id: fake-hook-b\n"
    )
    repo = _make_repo(tmp_path, config_text)
    monkeypatch.setattr(mod, "CONFIG_PATH", repo / ".pre-commit-config.yaml")
    ids = mod._declared_hook_ids()
    assert ids == ["fake-hook-a", "fake-hook-b"]


def test_declared_hook_ids_mixed_repos(tmp_path, monkeypatch):
    """declared_hook_ids() walks both external and local repos."""
    mod = _load(CHECK_HOOKS_PARITY)
    config_text = (
        "repos:\n"
        "  - repo: https://github.com/gitleaks/gitleaks\n"
        "    rev: v8.21.2\n"
        "    hooks:\n"
        "      - id: gitleaks\n"
        "  - repo: local\n"
        "    hooks:\n"
        "      - id: local-a\n"
        "      - id: local-b\n"
    )
    repo = _make_repo(tmp_path, config_text)
    monkeypatch.setattr(mod, "CONFIG_PATH", repo / ".pre-commit-config.yaml")
    ids = mod._declared_hook_ids()
    assert ids == ["gitleaks", "local-a", "local-b"]


# --- Gate 6: local hook entry scripts (PyYAML-correct pairing) ---------------

def test_local_hook_pairs_pyyaml_not_regex(tmp_path, monkeypatch):
    """_local_hook_pairs() pairs each id with its own entry via PyYAML walk.

    This is the regression test for the regex bug: the OLD regex would
    pair ``gitleaks`` (external, no entry) with the FIRST entry that
    follows (``local-a``). The PyYAML walker yields ``(gitleaks, None)``
    and ``(local-a, "python foo.py")`` separately, so the false pairing
    cannot occur.
    """
    mod = _load(CHECK_HOOKS_PARITY)
    config_text = (
        "repos:\n"
        "  - repo: https://github.com/gitleaks/gitleaks\n"
        "    rev: v8.21.2\n"
        "    hooks:\n"
        "      - id: gitleaks\n"
        "  - repo: local\n"
        "    hooks:\n"
        "      - id: local-a\n"
        "        entry: python scripts/a.py --apply\n"
        "      - id: local-b\n"
        "        entry: python scripts/b.py\n"
    )
    repo = _make_repo(tmp_path, config_text)
    monkeypatch.setattr(mod, "CONFIG_PATH", repo / ".pre-commit-config.yaml")
    pairs = mod._local_hook_pairs()
    # gitleaks (external) -> entry is None, NOT the first local entry.
    assert ("gitleaks", None) in pairs, pairs
    # local-a and local-b are paired with their own entries.
    assert ("local-a", "python scripts/a.py --apply") in pairs, pairs
    assert ("local-b", "python scripts/b.py") in pairs, pairs


def test_local_hook_pairs_extracts_script_path(tmp_path, monkeypatch):
    """_entry_script() extracts the first *.py path from an entry string."""
    mod = _load(CHECK_HOOKS_PARITY)
    assert mod._entry_script("python scripts/notebook_tools/strip_probe_banner.py --apply") \
        == "scripts/notebook_tools/strip_probe_banner.py"
    assert mod._entry_script("python scripts/x.py") == "scripts/x.py"
    assert mod._entry_script("python scripts/x.py --opt val") == "scripts/x.py"
    assert mod._entry_script("python something") is None  # no .py


# --- Gates 2/3/5: pre-commit launchable (PATH or `python -m pre_commit`) ----

def test_pre_commit_launchable_via_path(tmp_path, monkeypatch):
    """_pre_commit_launchable() prefers PATH when shutil.which succeeds."""
    mod = _load(CHECK_HOOKS_PARITY)

    class _FakeProc:
        returncode = 0

    # shutil.which("pre-commit") returns a path; subsequent subprocess.run
    # (the --version probe) succeeds -- the helper should return the bare
    # binary path, not the python -m fallback.
    monkeypatch.setattr(
        shutil, "which", lambda name: f"/usr/bin/{name}" if name == "pre-commit" else None,
    )
    monkeypatch.setattr(mod.subprocess, "run", lambda *a, **kw: _FakeProc())

    launch = mod._pre_commit_launchable()
    assert launch == ["/usr/bin/pre-commit"], launch


def test_pre_commit_launchable_via_module_when_path_missing(tmp_path, monkeypatch):
    """_pre_commit_launchable() falls back to `python -m pre_commit`.

    Reported by ai-01 against #9903: a worker with the pre-commit module
    installed but the binary missing from PATH satisfies H.3 (because
    ``pre-commit install`` writes a hook calling
    ``INSTALL_PYTHON -mpre_commit``) and yet the previous gate KO'd.
    """
    mod = _load(CHECK_HOOKS_PARITY)

    class _FakeProc:
        returncode = 0

    # shutil.which returns None for pre-commit -- the helper must probe
    # `python -m pre_commit --version` and return that argv prefix.
    monkeypatch.setattr(shutil, "which", lambda name: None)
    monkeypatch.setattr(mod.subprocess, "run", lambda *a, **kw: _FakeProc())

    launch = mod._pre_commit_launchable()
    assert launch == [sys.executable, "-m", "pre_commit"], launch


def test_pre_commit_launchable_returns_none_when_both_fail(tmp_path, monkeypatch):
    """_pre_commit_launchable() returns None when neither PATH nor module works."""
    mod = _load(CHECK_HOOKS_PARITY)

    class _FakeFailProc:
        returncode = 1
        stderr = "No module named pre_commit"

    monkeypatch.setattr(shutil, "which", lambda name: None)
    monkeypatch.setattr(mod.subprocess, "run", lambda *a, **kw: _FakeFailProc())

    assert mod._pre_commit_launchable() is None


def test_run_checks_no_gitleaks_on_path_gate(tmp_path, monkeypatch):
    """The 'gitleaks on PATH' gate has been removed (c9888-bis follow-up).

    gitleaks is an external hook; pre-commit downloads it into its cache.
    The old gate KO'd every healthy machine and printed a misleading hint
    (``pip install --user gitleaks`` -- gitleaks is a Go binary, no PyPI
    package by that name). Verified by ai-01 against #9903.
    """
    mod = _load(CHECK_HOOKS_PARITY)
    config_text = (
        "repos:\n"
        "  - repo: local\n"
        "    hooks:\n"
        "      - id: local-a\n"
        "        entry: python scripts/a.py\n"
    )
    repo = _make_repo(tmp_path, config_text)
    (repo / "scripts").mkdir(parents=True)
    (repo / "scripts" / "a.py").write_text("# stub\n")
    monkeypatch.setattr(mod, "REPO_ROOT", repo)
    monkeypatch.setattr(mod, "CONFIG_PATH", repo / ".pre-commit-config.yaml")
    monkeypatch.setattr(mod, "HOOK_PATH", repo / ".git" / "hooks" / "pre-commit")
    monkeypatch.setattr(shutil, "which", lambda name: None)
    monkeypatch.setattr(sys, "argv", ["check_hooks_parity"])

    rows = mod._run_checks()
    gate_names = [g for g, _, _ in rows]
    assert "gitleaks on PATH" not in gate_names, (
        f"gate 'gitleaks on PATH' was removed; found in {gate_names}"
    )
    assert "pre-commit launchable" in gate_names, gate_names


def test_run_checks_local_entry_missing(tmp_path, monkeypatch):
    """local hook entry scripts gate flips to KO when a script is missing."""
    mod = _load(CHECK_HOOKS_PARITY)
    config_text = (
        "repos:\n"
        "  - repo: local\n"
        "    hooks:\n"
        "      - id: local-a\n"
        "        entry: python scripts/does_not_exist.py --apply\n"
    )
    repo = _make_repo(tmp_path, config_text)
    monkeypatch.setattr(mod, "REPO_ROOT", repo)
    monkeypatch.setattr(mod, "CONFIG_PATH", repo / ".pre-commit-config.yaml")
    monkeypatch.setattr(mod, "HOOK_PATH", repo / ".git" / "hooks" / "pre-commit")
    monkeypatch.setattr(shutil, "which", lambda name: None)
    monkeypatch.setattr(sys, "argv", ["check_hooks_parity"])

    rows = mod._run_checks()
    gate_by_name = {g: (s, d) for g, s, d in rows}
    status, detail = gate_by_name["local hook entry scripts"]
    assert status == "KO", f"expected KO, got {status}: {detail}"
    assert "local-a" in detail and "scripts/does_not_exist.py" in detail


def test_run_checks_local_entry_present(tmp_path, monkeypatch):
    """local hook entry scripts gate is OK when each entry script exists."""
    mod = _load(CHECK_HOOKS_PARITY)
    config_text = (
        "repos:\n"
        "  - repo: local\n"
        "    hooks:\n"
        "      - id: local-a\n"
        "        entry: python scripts/a.py --apply\n"
    )
    repo = _make_repo(tmp_path, config_text)
    # Create the entry script so it exists.
    (repo / "scripts").mkdir(parents=True)
    (repo / "scripts" / "a.py").write_text("# stub\n")
    monkeypatch.setattr(mod, "REPO_ROOT", repo)
    monkeypatch.setattr(mod, "CONFIG_PATH", repo / ".pre-commit-config.yaml")
    monkeypatch.setattr(mod, "HOOK_PATH", repo / ".git" / "hooks" / "pre-commit")
    monkeypatch.setattr(shutil, "which", lambda name: None)
    monkeypatch.setattr(sys, "argv", ["check_hooks_parity"])

    rows = mod._run_checks()
    gate_by_name = {g: (s, d) for g, s, d in rows}
    status, detail = gate_by_name["local hook entry scripts"]
    assert status == "OK", f"expected OK, got {status}: {detail}"
    assert "1 local hooks wired" in detail


# --- Main entrypoint exit code ----------------------------------------------

def test_main_returns_1_on_ko(tmp_path, monkeypatch, capsys):
    """main() returns 1 when at least one gate is KO."""
    mod = _load(CHECK_HOOKS_PARITY)
    config_text = (
        "repos:\n"
        "  - repo: local\n"
        "    hooks:\n"
        "      - id: local-a\n"
        "        entry: python scripts/nope.py\n"
    )
    repo = _make_repo(tmp_path, config_text)
    monkeypatch.setattr(mod, "REPO_ROOT", repo)
    monkeypatch.setattr(mod, "CONFIG_PATH", repo / ".pre-commit-config.yaml")
    monkeypatch.setattr(mod, "HOOK_PATH", repo / ".git" / "hooks" / "pre-commit")
    # shutil.which returns None -> _pre_commit_launchable falls through to
    # the python -m probe; mock that to also fail so Gate 2 is KO.
    monkeypatch.setattr(shutil, "which", lambda name: None)

    class _FakeFailProc:
        returncode = 1
        stdout = ""
        stderr = "No module named pre_commit"

    monkeypatch.setattr(mod.subprocess, "run", lambda *a, **kw: _FakeFailProc())
    monkeypatch.setattr(sys, "argv", ["check_hooks_parity"])

    rc = mod.main()
    out = capsys.readouterr().out
    assert rc == 1, f"expected rc=1, got rc={rc}, output={out!r}"
    assert "KO" in out
    # New gate label (post-#9903 follow-up): the binary PATH check is
    # gone, replaced by "pre-commit launchable" which covers both PATH
    # and `python -m pre_commit`.
    assert "pre-commit launchable" in out
    # Old gate removed -- it must not appear.
    assert "gitleaks on PATH" not in out


def test_main_returns_0_when_all_green(tmp_path, monkeypatch, capsys):
    """main() returns 0 when every gate is green."""
    mod = _load(CHECK_HOOKS_PARITY)
    config_text = (
        "repos:\n"
        "  - repo: local\n"
        "    hooks:\n"
        "      - id: local-a\n"
        "        entry: python scripts/a.py --apply\n"
    )
    repo = _make_repo(tmp_path, config_text)
    (repo / ".git" / "hooks" / "pre-commit").write_text("#!/bin/sh\nexit 0\n")
    (repo / "scripts").mkdir(parents=True)
    (repo / "scripts" / "a.py").write_text("# stub\n")
    monkeypatch.setattr(mod, "REPO_ROOT", repo)
    monkeypatch.setattr(mod, "CONFIG_PATH", repo / ".pre-commit-config.yaml")
    monkeypatch.setattr(mod, "HOOK_PATH", repo / ".git" / "hooks" / "pre-commit")
    monkeypatch.setattr(shutil, "which", lambda name: f"/usr/bin/{name}")

    # Mock subprocess.run for BOTH the --version probe (Gate 2) and the
    # validate-config call (Gate 5) so every gate succeeds even when
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
