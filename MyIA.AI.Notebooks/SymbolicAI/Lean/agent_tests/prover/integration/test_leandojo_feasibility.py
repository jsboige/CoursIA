"""Tests for leandojo_feasibility (issue #18915, c.76).

These tests assert the **prereq table** the integration work relies on. The
goal is to lock the c.76 verdict (RECOVERABLE-LOCAL) so any future drift in
the installability of lean-dojo 2.2.0 + Lean 4.11.0 surfaces in CI rather
than at integration time.

The tests load the module under test via importlib (file path) to avoid
dragging the parent package's heavy imports (`agent_framework`, etc.) into
this minimal prereq check. The real CI run will exercise both: this test
under the lean_dojo_venv, and the heavier integration tests under the
prover's full venv.
"""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

import pytest


_HERE = Path(__file__).resolve().parent


def _load_module():
    """Load `leandojo_feasibility.py` by file path -- bypass the parent
    package's heavy `agent_framework` import chain."""
    target = _HERE / "leandojo_feasibility.py"
    spec = importlib.util.spec_from_file_location(
        "_leandojo_feasibility_isolated", target,
    )
    assert spec is not None and spec.loader is not None
    mod = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = mod
    spec.loader.exec_module(mod)
    return mod


@pytest.fixture(scope="module")
def feas():
    return _load_module()


def test_lean_dojo_version_pin_matches_leandojo_10(feas):
    """Version pin must match Lean-10 -- silent upgrade invalidates Dojo."""
    assert feas.LEAN_DOJO_VERSION == "2.2.0"


def test_lean_toolchain_pin_matches_leandojo_10(feas):
    """Lean 4.11.0 is the only toolchain where lean-dojo 2.2.0's Dojo works."""
    assert feas.LEAN_TOOLCHAIN == "leanprover/lean4:v4.11.0"


def test_python_version_ok(feas):
    """Python must be in the 3.10-3.12 range per lean-dojo 2.2.0
    Requires-Python (<=3.12,>=3.9). Outside this range the install needs
    --ignore-requires-python and the runtime is not supported.
    """
    r = feas.check_python_version()
    assert r.name == "python 3.10-3.12"
    # 3.10-3.12 are supported; 3.13+ is not. The assertion is conditional
    # on the running interpreter: this test asserts the *plumbing* works,
    # not the verdict.
    import sys
    major, minor = sys.version_info[:2]
    expected_ok = (3, 10) <= (major, minor) <= (3, 12)
    assert r.ok is expected_ok, r.render()


def test_lean_dojo_installed(feas):
    """`pip show lean-dojo` must report 2.2.0 on the test env."""
    pytest.importorskip("lean_dojo")
    r = feas.check_lean_dojo_installed()
    assert r.ok, r.render()


def test_lean_dojo_importable(feas):
    """Dojo, LeanGitRepo, trace must all be exposed by the package."""
    pytest.importorskip("lean_dojo")
    r = feas.check_lean_dojo_importable()
    assert r.ok, r.render()


def test_elan_on_path(feas):
    """elan is the only way this integration installs Lean toolchains."""
    r = feas.check_elan_available()
    assert r.ok, r.render()


def test_lean_toolchain_installed(feas):
    """The Lean 4.11.0 toolchain must be on the host (c.76 install)."""
    r = feas.check_lean_toolchain_pinned()
    assert r.ok, r.render()


def test_lean_default_toolchain_is_4_11(feas):
    """`lean --version` should report 4.11.0 -- not a newer toolchain that
    breaks the lean-dojo 2.2.0 / Dojo runtime pair."""
    r = feas.check_lean_default_toolchain()
    assert r.ok, r.render()


def test_run_all_checks_returns_six_results(feas):
    """Smoke test: the runner covers the full prereq surface."""
    results = feas.run_all_checks()
    assert len(results) == 6
    assert all(isinstance(r, feas.LeanDojoPrereq) for r in results)


# -- Deterministic controls for the prereq logic (c.81 adjoint review) ----
# These tests assert the control surfaces the right verdict for a synthetic
# Python version / pin / elan state, independent of the host. They are what
# CI should run when the real lean_dojo install is not available: the
# *control logic* is what breaks drift, not the host state.


def test_python_version_caps_at_3_12(feas, monkeypatch):
    """Versions 3.13+ are NOT supported by lean-dojo 2.2.0
    (Requires-Python: <=3.12,>=3.9). The control must reject them.
    """
    for fake_minor in (13, 14):
        monkeypatch.setattr(sys, "version_info", (3, fake_minor, 0, "final", 0))
        r = feas.check_python_version()
        assert r.ok is False, f"3.{fake_minor} should be rejected: {r.render()}"
        assert "supported: 3.10-3.12" in r.detail


def test_python_version_accepts_3_10_to_3_12(feas, monkeypatch):
    """The supported range 3.10-3.12 must all be accepted."""
    for fake_minor in (10, 11, 12):
        monkeypatch.setattr(sys, "version_info", (3, fake_minor, 0, "final", 0))
        r = feas.check_python_version()
        assert r.ok is True, f"3.{fake_minor} should be accepted: {r.render()}"


def test_pin_mismatch_detected(feas, monkeypatch):
    """`check_lean_dojo_installed` must FAIL when the installed version
    differs from the pinned version. Mocks pip show to return a wrong
    version string.
    """
    class _FakeProc:
        returncode = 0
        stdout = "Name: lean-dojo\nVersion: 9.9.9\nLocation: /tmp\n"

    def _fake_run(*args, **kwargs):
        return _FakeProc()

    monkeypatch.setattr(feas.subprocess, "run", _fake_run)
    r = feas.check_lean_dojo_installed()
    assert r.ok is False
    assert "want 2.2.0" in r.detail
    assert "have 9.9.9" in r.detail


def test_elan_missing_detected(feas, monkeypatch):
    """`check_elan_available` must FAIL when elan is not on PATH."""
    monkeypatch.setattr(feas.shutil, "which", lambda _: None)
    r = feas.check_elan_available()
    assert r.ok is False
    assert "elan not found" in r.detail


def test_lean_toolchain_pin_mismatch_detected(feas, monkeypatch):
    """`check_lean_toolchain_pinned` must FAIL when the pinned toolchain
    is not in `elan toolchain list` output.
    """
    monkeypatch.setattr(feas.shutil, "which", lambda _: "/usr/bin/elan")
    fake_proc = type("_P", (), {"returncode": 0, "stdout": "stable (default)\nleanprover/lean4:v4.30.0\n", "stderr": ""})()
    monkeypatch.setattr(feas.subprocess, "run", lambda *a, **kw: fake_proc)
    r = feas.check_lean_toolchain_pinned()
    assert r.ok is False
    assert "v4.11.0" in r.detail


def test_lean_default_toolchain_mismatch_detected(feas, monkeypatch):
    """`check_lean_default_toolchain` must FAIL when `lean --version`
    reports a toolchain other than 4.11.0.
    """
    monkeypatch.setattr(feas.shutil, "which", lambda _: "/usr/bin/lean")
    fake_proc = type("_P", (), {"returncode": 0, "stdout": "Lean (version 4.30.0, ...)", "stderr": ""})()
    monkeypatch.setattr(feas.subprocess, "run", lambda *a, **kw: fake_proc)
    r = feas.check_lean_default_toolchain()
    assert r.ok is False
    assert r.name == "lean 4.11.0 active"
    assert "4.30.0" in r.detail  # the actual reported version, not the wanted one


def test_run_all_checks_propagates_python_cap(feas, monkeypatch):
    """Smoke test: with a fake 3.13 Python, `run_all_checks` should
    return at least one FAIL (the python version cap). Reuses the
    fixture-loaded module so sys.modules is correctly populated for
    @dataclass.
    """
    monkeypatch.setattr(sys, "version_info", (3, 13, 0, "final", 0))
    results = feas.run_all_checks()
    python_check = next(r for r in results if r.name == "python 3.10-3.12")
    assert python_check.ok is False
    assert any(not r.ok for r in results), "at least one check must FAIL on 3.13"
