#!/usr/bin/env python3
"""Regression tests for setup_hooks.py --self-test (#9888 functional check).

--self-test stages a probe secret and verifies gitleaks detects it. The
critical regression guard is the CLEANUP guarantee: even if gitleaks crashes
or returns a silent no-op, the probe (which contains a fake secret) MUST be
unstaged and deleted -- never left on disk or in the index. These tests also
lock the probe-choice rationale: the secret is a stripe key, NOT the canonical
AWS EXAMPLE key (gitleaks' default ruleset allowlists the latter, so using it
would make --self-test silently pass even with a broken config -- the exact
no-op #9888 fights).

Verified live on myia-po-2023 before encoding: gitleaks detected 1 staged
leak, probe cleaned, exit 0. These unit tests cover the exit logic + cleanup
guarantee with a mocked gitleaks (CI-portable, no live binary needed).

Executable two ways:
    py scripts/tests/test_setup_hooks_selftest.py
    npx pytest scripts/tests/test_setup_hooks_selftest.py
"""

from __future__ import annotations

import importlib.util
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

SETUP_HOOKS = Path(__file__).resolve().parent.parent / "setup_hooks.py"

GIT = shutil.which("git")
pytestmark = pytest.mark.skipif(
    GIT is None,
    reason="--self-test cleanup tests need git to stage/unstage the probe",
)

PROBE_SECRET = "sk_live_" + "51Hqk2l3f4g5h6j7k" + "8l9n0mN1o2pQ3r4s"  # assembled; mirrors setup_hooks._SELFTEST_SECRET
PROBE_NAME = "_gitleaks_selftest_probe.py"


@pytest.fixture
def hooks_module():
    """Import setup_hooks.py as a module (it lives in scripts/, not a package)."""
    spec = importlib.util.spec_from_file_location("setup_hooks_under_test", SETUP_HOOKS)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


@pytest.fixture
def repo(tmp_path, monkeypatch):
    """A real git repo in tmp_path with one empty commit (so `git reset` resolves
    HEAD cleanly); cwd switched into it."""
    subprocess.run(["git", "init", "-q"], cwd=str(tmp_path), check=True)
    subprocess.run(
        ["git", "commit", "-q", "--allow-empty", "-m", "init"],
        cwd=str(tmp_path), check=True,
        env={**__import__("os").environ, "GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@t",
             "GIT_COMMITTER_NAME": "t", "GIT_COMMITTER_EMAIL": "t@t"},
    )
    monkeypatch.chdir(tmp_path)
    return tmp_path


def _fake_run_factory(simulated_gitleaks):
    """Build a fake _run that delegates git ops (real) but returns canned output
    for the pre_commit/gitleaks invocation."""

    def _fake_run(cmd, cwd):
        # The gitleaks invocation is the only call whose argv contains pre_commit.
        if any("pre_commit" in c for c in cmd):
            return simulated_gitleaks
        # git add / git reset: run for real so staging reflects reality.
        proc = subprocess.run(
            cmd, cwd=str(cwd), capture_output=True, text=True, shell=False,
        )
        return proc.returncode, (proc.stdout + proc.stderr).strip()

    return _fake_run


def _probe_clean(repo):
    """True if the probe is neither on disk nor in the index."""
    on_disk = (repo / PROBE_NAME).exists()
    status = subprocess.run(
        ["git", "status", "--short"], cwd=str(repo),
        capture_output=True, text=True,
    ).stdout
    in_index = PROBE_NAME in status
    return not on_disk and not in_index


def test_probe_secret_is_real_stripe_key(hooks_module):
    """The probe must assemble to a key gitleaks actually flags, not an EXAMPLE key.

    The canonical AWS example access key is allowlisted by gitleaks' defaults
    (AWS documents it) -- using it would mask a silent no-op. The assembled probe
    must be a realistic stripe key (sk_live_ prefix, plausible length) so the
    default ruleset flags it. Guard against a future edit switching to an
    allowlisted/example value.
    """
    secret = hooks_module._SELFTEST_SECRET
    assert secret == PROBE_SECRET, "test PROBE_SECRET drifted from setup_hooks._SELFTEST_SECRET"
    assert secret.startswith("sk_live_"), "probe must be a stripe key (sk_live_ prefix)"
    assert len(secret) >= 30, "probe stripe key too short to be realistic"
    assert not secret.startswith("AKIA"), "AWS example keys are gitleaks-allowlisted"


def test_pass_when_leaks_detected(repo, hooks_module, monkeypatch):
    """gitleaks detects (rc!=0, RuleID in output) -> exit 0 + probe cleaned."""
    fake_out = (
        'Finding: token = "REDACTED"\n'
        "RuleID: stripe-access-token\n"
        "leaks found: 1\n"
    )
    monkeypatch.setattr(hooks_module, "_run", _fake_run_factory((1, fake_out)))
    monkeypatch.setattr(hooks_module, "_pre_commit_available", lambda python: True)

    rc = hooks_module.cmd_self_test(repo, sys.executable)
    assert rc == 0
    assert _probe_clean(repo), "probe leaked (on disk or staged) after a PASS run"


def test_fail_and_cleanup_on_silent_noop(repo, hooks_module, monkeypatch, capsys):
    """Silent no-op (rc=0, no RuleID) -> exit 1, probe cleaned, useDefault hint.

    This is the useDefault-missing regression: gitleaks runs but detects
    nothing. --self-test must FAIL (exit 1), hint the root cause, and leave no
    probe behind.
    """
    monkeypatch.setattr(hooks_module, "_run", _fake_run_factory((0, "")))
    monkeypatch.setattr(hooks_module, "_pre_commit_available", lambda python: True)

    rc = hooks_module.cmd_self_test(repo, sys.executable)
    assert rc == 1, "silent no-op must FAIL the self-test"
    assert _probe_clean(repo)
    assert "useDefault" in capsys.readouterr().err, (
        "FAIL message must hint the [extend] useDefault root cause"
    )


def test_cleanup_when_gitleaks_crashes(repo, hooks_module, monkeypatch):
    """A gitleaks crash (rc != 0, zero RuleID) must still not leak the probe."""
    monkeypatch.setattr(
        hooks_module, "_run", _fake_run_factory((2, "fatal: gitleaks crashed")),
    )
    monkeypatch.setattr(hooks_module, "_pre_commit_available", lambda python: True)

    rc = hooks_module.cmd_self_test(repo, sys.executable)
    assert rc == 1
    assert _probe_clean(repo), "probe leaked after a gitleaks crash"


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-v"]))
