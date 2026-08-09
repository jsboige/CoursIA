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
    """main() returns 0 when every gate is green.

    Gate 7 (#10139) needs BOTH pinned versions to exist and agree, so the
    fake repo declares a gitleaks hook and a matching workflow. Feeding the
    new gate its inputs is deliberate: exempting it here would make
    "every gate green" quietly mean "every gate but one".
    """
    mod = _load(CHECK_HOOKS_PARITY)
    config_text = (
        "repos:\n"
        "  - repo: https://github.com/gitleaks/gitleaks\n"
        "    rev: v9.9.9\n"
        "    hooks:\n"
        "      - id: gitleaks\n"
        "  - repo: local\n"
        "    hooks:\n"
        "      - id: local-a\n"
        "        entry: python scripts/a.py --apply\n"
    )
    repo = _make_repo(tmp_path, config_text)
    (repo / ".git" / "hooks" / "pre-commit").write_text("#!/bin/sh\nexit 0\n")
    (repo / "scripts").mkdir(parents=True)
    (repo / "scripts" / "a.py").write_text("# stub\n")
    workflow = repo / ".github" / "workflows" / "secret-scan.yml"
    workflow.parent.mkdir(parents=True)
    workflow.write_text(
        "jobs:\n"
        "  gitleaks:\n"
        "    steps:\n"
        "      - uses: gitleaks/gitleaks-action@v2\n"
        "        env:\n"
        "          GITLEAKS_VERSION: 9.9.9\n",
        encoding="utf-8",
    )
    monkeypatch.setattr(mod, "REPO_ROOT", repo)
    monkeypatch.setattr(mod, "CONFIG_PATH", repo / ".pre-commit-config.yaml")
    monkeypatch.setattr(mod, "HOOK_PATH", repo / ".git" / "hooks" / "pre-commit")
    monkeypatch.setattr(mod, "SECRET_SCAN_PATH", workflow)
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


# --- Gate 7: gitleaks version parity (hook rev vs CI GITLEAKS_VERSION) -------
#
# This is the ENFORCING copy of the gate. check_hooks_parity.py is advisory in
# CI by design (a missing local hook is the worker's state to repair), but a
# version divergence is not machine state: it is two files in the repo
# disagreeing, identical on every checkout. It must fail something blocking,
# and that is this test.
#
# What it guards, measured on this repo (#10139): gitleaks 8.21.2 reported 0
# findings on the very files where 8.24.3 reported 2. While the hook pinned
# 8.21.2 and CI resolved 8.24.3, a clean `git commit` was rejected in CI with
# nothing in the repo to explain it.


def _write_pair(tmp_path: Path, hook_rev: str | None, ci_version: str | None):
    """Fake repo pinning ``hook_rev`` locally and ``ci_version`` in CI.

    ``None`` means "pin absent" -- for the hook, no gitleaks repo at all; for
    CI, a workflow step carrying no GITLEAKS_VERSION.
    """
    repos = "repos:\n"
    if hook_rev is not None:
        repos += (
            "  - repo: https://github.com/gitleaks/gitleaks\n"
            f"    rev: {hook_rev}\n"
            "    hooks:\n"
            "      - id: gitleaks\n"
        )
    repos += (
        "  - repo: local\n"
        "    hooks:\n"
        "      - id: local-a\n"
        "        entry: python scripts/a.py\n"
    )
    repo = _make_repo(tmp_path, repos)
    workflow = repo / ".github" / "workflows" / "secret-scan.yml"
    workflow.parent.mkdir(parents=True)
    env_block = f"        env:\n          GITLEAKS_VERSION: {ci_version}\n" if ci_version else ""
    workflow.write_text(
        "jobs:\n  gitleaks:\n    steps:\n"
        "      - uses: gitleaks/gitleaks-action@v2\n" + env_block,
        encoding="utf-8",
    )
    return repo, workflow


def _parity_row(mod, tmp_path, monkeypatch, hook_rev, ci_version):
    repo, workflow = _write_pair(tmp_path, hook_rev, ci_version)
    monkeypatch.setattr(mod, "REPO_ROOT", repo)
    monkeypatch.setattr(mod, "CONFIG_PATH", repo / ".pre-commit-config.yaml")
    monkeypatch.setattr(mod, "SECRET_SCAN_PATH", workflow)
    rows = [r for r in mod._run_checks() if r[0] == "gitleaks version parity"]
    assert rows, "gate 'gitleaks version parity' absent from _run_checks()"
    return rows[0]


def test_parity_ok_when_versions_agree(tmp_path, monkeypatch):
    mod = _load(CHECK_HOOKS_PARITY)
    gate, status, detail = _parity_row(mod, tmp_path, monkeypatch, "v8.24.3", "8.24.3")
    assert status == "OK", f"{gate}: {detail}"


def test_parity_ko_when_versions_diverge(tmp_path, monkeypatch):
    """The exact shape of the #10139 defect: hook 8.21.2 vs CI 8.24.3."""
    mod = _load(CHECK_HOOKS_PARITY)
    _gate, status, detail = _parity_row(mod, tmp_path, monkeypatch, "v8.21.2", "8.24.3")
    assert status == "KO", f"expected KO on divergence, got {status}: {detail}"
    assert "8.21.2" in detail and "8.24.3" in detail, detail


def test_parity_ko_when_ci_pins_nothing(tmp_path, monkeypatch):
    """No GITLEAKS_VERSION is a finding, not an absence of information.

    Unset, the action falls back to a version hard-coded in its own source
    (``GITLEAKS_VERSION || "8.24.3"``, src/index.js) -- an implicit pin owned
    by a third party that any ``@v2`` release can revise with no commit here.
    """
    mod = _load(CHECK_HOOKS_PARITY)
    _gate, status, detail = _parity_row(mod, tmp_path, monkeypatch, "v8.24.3", None)
    assert status == "KO", f"expected KO when CI pins nothing, got {status}: {detail}"
    assert "GITLEAKS_VERSION" in detail, detail


def test_parity_v_prefix_is_not_a_divergence(tmp_path, monkeypatch):
    """``rev: v8.24.3`` vs ``GITLEAKS_VERSION: 8.24.3`` is the CORRECT form.

    The hook tag carries the ``v``; the action's env var must not (its README
    is explicit: "no ``v`` prefix"). A gate that flagged this would push
    someone to "fix" it into a genuinely broken download URL.
    """
    mod = _load(CHECK_HOOKS_PARITY)
    _gate, status, _detail = _parity_row(mod, tmp_path, monkeypatch, "v8.24.3", "8.24.3")
    assert status == "OK"


def test_parity_holds_on_the_real_repo_files(monkeypatch):
    """The live gate: the versions actually shipped in this repo must agree.

    Unlike the fixtures above, this reads the real ``.pre-commit-config.yaml``
    and ``.github/workflows/secret-scan.yml``. It is what turns the rule into
    an organ: bump one file alone and this test goes red.
    """
    mod = _load(CHECK_HOOKS_PARITY)
    if not (mod.CONFIG_PATH.exists() and mod.SECRET_SCAN_PATH.exists()):
        import pytest
        pytest.skip("real config/workflow not present in this environment")
    try:
        hook_v = mod._hook_gitleaks_version()
        ci_v = mod._ci_gitleaks_version()
    except RuntimeError as e:
        import pytest
        pytest.skip(f"PyYAML missing in test environment: {e}")
    assert hook_v is not None, ".pre-commit-config.yaml declares no gitleaks rev"
    assert ci_v is not None, "secret-scan.yml sets no GITLEAKS_VERSION (unpinned CI gate)"
    assert hook_v == ci_v, (
        f"gitleaks version drift: hook pins v{hook_v}, CI pins {ci_v}. "
        "These must be bumped together -- they disagree on real content "
        "(see #10139), so a green pre-commit would stop predicting CI."
    )
