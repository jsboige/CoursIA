#!/usr/bin/env python3
"""Pytest suite for `ext_tools/sat_solver.py` (PySAT DIMACS wrapper).

Co-located with the module (same convention as `ict/tests/`). CPU-only, no
network, deterministic. Guards on PySAT availability via `importorskip` so the
suite is skipped (not errored) on a machine without `python-sat`.

The suite pins the public API surface (`parse_dimacs_cnf`, `solve_sat`,
`enumerate_solutions`) AND a regression on the `--all-solutions` CLI path:
an UNSAT formula used to print a self-contradictory
`s SATISFIABLE` / `s UNSATISFIABLE` pair because the SAT status line was
emitted before enumeration. The CLI test asserts exactly one status line.
"""
from __future__ import annotations

import os
import subprocess
import sys
import textwrap
from pathlib import Path

import pytest

pysat = pytest.importorskip("pysat")  # noqa: F841 — skip suite if PySAT missing

# Make `sat_solver` importable regardless of pytest rootdir / cwd.
_EXT_TOOLS_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(_EXT_TOOLS_DIR))

import sat_solver  # noqa: E402 — path adjusted above

SAT_SOLVER = Path(__file__).resolve().parent / "sat_solver.py"

# Trivial CNF fixtures (built in a tmp_path so the suite is self-contained).
SAT_CNF = "p cnf 2 2\n1 0\n2 0\n"          # x1 ∧ x2                  → SAT
UNSAT_CNF = "p cnf 1 2\n1 0\n-1 0\n"       # x1 ∧ ¬x1                 → UNSAT
SAT_MULTI_CNF = "p cnf 2 1\n1 2 0\n"       # (x1 ∨ x2)                → SAT, 3 models


def _write_cnf(tmp_path: Path, name: str, content: str) -> Path:
    p = tmp_path / name
    p.write_text(content)
    return p


# --------------------------------------------------------------------------
# parse_dimacs_cnf
# --------------------------------------------------------------------------


def test_parse_dimacs_cnf_basic(tmp_path):
    cnf = _write_cnf(tmp_path, "basic.cnf", SAT_CNF)
    num_vars, clauses = sat_solver.parse_dimacs_cnf(str(cnf))
    assert num_vars == 2
    assert clauses == [[1], [2]]


def test_parse_dimacs_cnf_skips_comments_and_problem_line(tmp_path):
    content = textwrap.dedent(
        """\
        c this is a comment
        p cnf 3 2
        1 2 0
        c another comment
        -1 3 0
        """
    )
    cnf = _write_cnf(tmp_path, "with_comments.cnf", content)
    num_vars, clauses = sat_solver.parse_dimacs_cnf(str(cnf))
    assert num_vars == 3
    assert clauses == [[1, 2], [-1, 3]]


def test_parse_dimacs_cnf_strips_trailing_zero(tmp_path):
    # The trailing ' 0' terminator must not leak into the parsed clause.
    cnf = _write_cnf(tmp_path, "zero.cnf", "p cnf 2 1\n1 -2 0\n")
    _, clauses = sat_solver.parse_dimacs_cnf(str(cnf))
    assert clauses == [[1, -2]]
    assert 0 not in clauses[0]


# --------------------------------------------------------------------------
# solve_sat
# --------------------------------------------------------------------------


def test_solve_sat_satisfiable(tmp_path):
    cnf = _write_cnf(tmp_path, "sat.cnf", SAT_CNF)
    _, clauses = sat_solver.parse_dimacs_cnf(str(cnf))
    is_sat, model, stats = sat_solver.solve_sat(clauses)
    assert is_sat is True
    assert model is not None
    assert stats["status"] == "SAT"
    # Model must satisfy every clause: x1 and x2 both true.
    assert 1 in model and 2 in model


def test_solve_sat_unsatisfiable(tmp_path):
    cnf = _write_cnf(tmp_path, "unsat.cnf", UNSAT_CNF)
    _, clauses = sat_solver.parse_dimacs_cnf(str(cnf))
    is_sat, model, stats = sat_solver.solve_sat(clauses)
    assert is_sat is False
    assert model is None
    assert stats["status"] == "UNSAT"


def test_solve_sat_assumptions_force_unsat(tmp_path):
    # (x1 ∨ x2) is SAT, but assuming x1=False AND x2=False makes it UNSAT.
    cnf = _write_cnf(tmp_path, "multi.cnf", SAT_MULTI_CNF)
    _, clauses = sat_solver.parse_dimacs_cnf(str(cnf))
    is_sat, model, stats = sat_solver.solve_sat(clauses, assumptions=[-1, -2])
    assert is_sat is False
    assert model is None
    # An UNSAT under assumptions must surface an unsat core.
    assert "unsat_core" in stats


# --------------------------------------------------------------------------
# enumerate_solutions
# --------------------------------------------------------------------------


def test_enumerate_solutions_yields_distinct_models(tmp_path):
    # (x1 ∨ x2) has exactly 3 satisfying assignments out of 4.
    cnf = _write_cnf(tmp_path, "multi.cnf", SAT_MULTI_CNF)
    _, clauses = sat_solver.parse_dimacs_cnf(str(cnf))
    models = list(sat_solver.enumerate_solutions(clauses, max_solutions=10))
    # Each model is a full assignment (2 vars); they must be pairwise distinct.
    seen = set()
    for m in models:
        frozen = tuple(sorted(m))
        assert frozen not in seen, f"duplicate model emitted: {m}"
        seen.add(frozen)
    assert len(models) == 3


def test_enumerate_solutions_unsat_yields_nothing(tmp_path):
    cnf = _write_cnf(tmp_path, "unsat.cnf", UNSAT_CNF)
    _, clauses = sat_solver.parse_dimacs_cnf(str(cnf))
    models = list(sat_solver.enumerate_solutions(clauses, max_solutions=5))
    assert models == []


def test_enumerate_solutions_respects_max(tmp_path):
    cnf = _write_cnf(tmp_path, "multi.cnf", SAT_MULTI_CNF)
    _, clauses = sat_solver.parse_dimacs_cnf(str(cnf))
    models = list(sat_solver.enumerate_solutions(clauses, max_solutions=2))
    assert len(models) == 2


# --------------------------------------------------------------------------
# main() CLI — regression on the contradictory UNSAT --all-solutions output
# --------------------------------------------------------------------------


def _run_cli(cnf_path: Path, *extra: str) -> tuple[int, str]:
    proc = subprocess.run(
        [sys.executable, str(SAT_SOLVER), str(cnf_path), *extra],
        capture_output=True,
        text=True,
        timeout=60,
    )
    return proc.returncode, proc.stdout


def test_main_all_solutions_unsat_no_contradictory_output(tmp_path):
    """Regression: UNSAT + --all-solutions must print exactly one status line.

    Before the fix, `s SATISFIABLE` was emitted before enumeration and then
    `s UNSATISFIABLE` after the empty enumeration, producing contradictory
    output. A consumer grepping for `s SATISFIABLE` would have wrongly
    concluded the formula was satisfiable.
    """
    cnf = _write_cnf(tmp_path, "unsat.cnf", UNSAT_CNF)
    rc, out = _run_cli(cnf, "--all-solutions")
    status_lines = [ln for ln in out.splitlines() if ln.startswith("s ")]
    assert rc == 1, "UNSAT must exit non-zero"
    assert status_lines == ["s UNSATISFIABLE"], (
        f"expected exactly one UNSAT status line, got: {status_lines!r} "
        f"(full output: {out!r})"
    )
    assert "s SATISFIABLE" not in out


def test_main_all_solutions_satisfiable_preserved(tmp_path):
    cnf = _write_cnf(tmp_path, "sat.cnf", SAT_CNF)
    rc, out = _run_cli(cnf, "--all-solutions", "--max", "5")
    assert rc == 0
    assert "s SATISFIABLE" in out
    assert any(ln.startswith("v ") for ln in out.splitlines())
    assert "c Found 1 solution(s)" in out


def test_main_single_solution_unsat(tmp_path):
    cnf = _write_cnf(tmp_path, "unsat.cnf", UNSAT_CNF)
    rc, out = _run_cli(cnf)
    assert rc == 1
    assert out.strip().splitlines() == ["s UNSATISFIABLE"]
