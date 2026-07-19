#!/usr/bin/env python3
"""Pytest suite for `Tweety/scripts/sat_calibration.py` (SAT solver calibration).

Co-located with the module (same convention as `ext_tools/test_sat_solver.py`).
CPU-only, no network, deterministic. Guards on PySAT availability via
`importorskip` so the suite is skipped (not errored) on a machine without
`python-sat`.

The suite pins:
  * `solve_with_timeout` return contract for the three outcomes (success /
    timeout / error), and
  * a regression on `benchmark_config`: an exception raised by a solver used
    to be masked as a TIMEOUT (the error string is truthy, so the old
    `if timed_out:` branch swallowed it before the dead
    `elif isinstance(timed_out, str)` could run). The regression test injects
    a non-existent solver and asserts the error message surfaces verbatim in
    the `times` dict rather than being reported as TIMEOUT.
"""
from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

import pytest

pysat = pytest.importorskip("pysat")  # noqa: F841 — skip suite if PySAT missing
CNF = pytest.importorskip("pysat.formula", reason="needs pysat.formula").CNF

# Load the module by path (it lives under scripts/, no package import path).
_SCRIPTS_DIR = Path(__file__).resolve().parent
_MODULE_PATH = _SCRIPTS_DIR / "sat_calibration.py"
_spec = importlib.util.spec_from_file_location("sat_calibration", _MODULE_PATH)
sat_calibration = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(sat_calibration)


def _trivial_cnf() -> "CNF":
    cnf = CNF()
    cnf.append([1])
    cnf.append([2])
    return cnf


# --------------------------------------------------------------------------
# solve_with_timeout — return contract
# --------------------------------------------------------------------------


def test_solve_with_timeout_success_returns_false_flag():
    cnf = _trivial_cnf()
    # cadical195 / glucose42 / minisat22 are the module's configured solvers;
    # use whichever is actually available on this machine.
    for name in ("cadical195", "glucose42", "minisat22"):
        elapsed, sat, flag = sat_calibration.solve_with_timeout(name, cnf, 10)
        if isinstance(flag, str) and flag.startswith("Error:"):
            continue  # solver not installed here; try the next
        assert flag is False, f"{name} should succeed with flag=False, got {flag!r}"
        assert sat is True, "trivially-SAT CNF (x1) ∧ (x2) must be SAT"
        assert elapsed >= 0
        return
    pytest.skip("none of cadical195/glucose42/minisat22 available locally")


def test_solve_with_timeout_error_returns_string_flag():
    """A non-existent solver must surface as an error STRING, not a timeout.

    The third tuple element is `f"Error: {e}"` (truthy string) on exception,
    `True` on timeout, `False` on success. The error string MUST be kept
    distinct from the boolean timeout flag downstream — see the
    `benchmark_config` regression below.
    """
    cnf = _trivial_cnf()
    elapsed, sat, flag = sat_calibration.solve_with_timeout(
        "DEFINITELY_NOT_A_SOLVER_XYZ", cnf, 5
    )
    assert isinstance(flag, str)
    assert flag.startswith("Error:")
    assert sat is None
    assert elapsed == 0


# --------------------------------------------------------------------------
# benchmark_config — regression: error must not be masked as TIMEOUT
# --------------------------------------------------------------------------


def test_benchmark_config_surfaces_solver_error_not_timeout(monkeypatch):
    """Regression: an exception raised by a solver must be reported as the
    error message, NOT silently relabeled as TIMEOUT.

    Before the fix, `benchmark_config` did `if timed_out:` first, which is
    truthy for both the boolean `True` (real timeout) and a non-empty error
    string. So a crashing solver appeared to time out, corrupting the
    calibration. The `elif isinstance(timed_out, str)` branch that was meant
    to handle errors was dead code.
    """
    # Force the only "solver" considered to be a non-existent one so the
    # exception path is exercised deterministically, regardless of which
    # real solvers are installed on this machine.
    monkeypatch.setattr(sat_calibration, "SOLVERS", ["DEFINITELY_NOT_A_SOLVER_XYZ"])
    monkeypatch.setattr(
        sat_calibration,
        "SOLVER_SHORT",
        {"DEFINITELY_NOT_A_SOLVER_XYZ": "Bogus"},
    )

    cnf = _trivial_cnf()
    result = sat_calibration.benchmark_config("repro", cnf, timeout=5)

    bogus_entry = result["times"]["Bogus"]
    assert isinstance(bogus_entry, str)
    assert bogus_entry.startswith("Error:"), (
        f"solver error should surface verbatim, got {bugus_entry!r} "
        "(would be 'TIMEOUT (5s)' under the buggy branch order)"
    )
    assert "TIMEOUT" not in bogus_entry
    # No winner can be declared from a crashed solver.
    assert result["winner"] is None


def test_benchmark_config_records_vars_and_clauses():
    cnf = _trivial_cnf()
    # Use a real solver if any is available, else skip gracefully.
    for name in ("cadical195", "glucose42", "minisat22"):
        _e, _s, flag = sat_calibration.solve_with_timeout(name, cnf, 10)
        if flag is False:
            monkeypatch_target = None
            break
    else:
        pytest.skip("no configured solver available locally")
    result = sat_calibration.benchmark_config("meta", cnf, timeout=10)
    assert result["vars"] == 2
    assert result["clauses"] == 2
    assert "times" in result and result["times"]
