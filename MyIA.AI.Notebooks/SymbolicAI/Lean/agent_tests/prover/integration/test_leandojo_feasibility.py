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
    """Python 3.10+ is the lean-dojo 2.2.0 floor."""
    r = feas.check_python_version()
    assert r.ok, r.render()
    assert r.name == "python>=3.10"


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
