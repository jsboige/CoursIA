# -*- coding: utf-8 -*-
"""Tests pour le module examples/sat_solver.py.

Module companion des notebooks SymbolicAI/ext_tools (SAT solving via PySAT,
backends CaDiCaL / CryptoMiniSat / Glucose / ...).

Couvre :
  - parse_dimacs_cnf : parsing DIMACS (p line, commentaires, %, terminateur 0,
    clauses vides skippees).
  - solve_sat : SAT/UNSAT, assumptions + unsat core, stats, gate PYSAT_AVAILABLE.
  - enumerate_solutions : yield de modeles, terminaison sur UNSAT, respect max.
  - main() --all-solutions : **regression dual-status** (UNSAT ne doit PLUS
    afficher "s SATISFIABLE" puis "s UNSATISFIABLE" -- bug jumeau de #7380
    maxsat_solver, fixe dans cette PR).
"""

import subprocess
import sys
from pathlib import Path

import pytest

EXT_DIR = Path(__file__).parent
sys.path.insert(0, str(EXT_DIR))

from sat_solver import (  # noqa: E402
    PYSAT_AVAILABLE,
    RECOMMENDED_SOLVERS,
    enumerate_solutions,
    parse_dimacs_cnf,
    solve_sat,
)

SOLVER = "cadical195"  # default backend, present in every PySAT install
SCRIPT = EXT_DIR / "sat_solver.py"
PYEXE = sys.executable


def _run_cli(cnf_text: str, tmp_path: Path, *extra: str):
    """Run sat_solver.py as a subprocess on a CNF written to tmp_path.

    Returns (returncode, stdout, stderr)."""
    cnf = tmp_path / "p.cnf"
    cnf.write_text(cnf_text)
    proc = subprocess.run(
        [PYEXE, str(SCRIPT), str(cnf), *extra],
        capture_output=True, text=True, timeout=60,
    )
    return proc.returncode, proc.stdout, proc.stderr


# ── parse_dimacs_cnf ────────────────────────────────────────────────────────


class TestParseDimacsCnf:
    """Parsing DIMACS CNF : num_vars + clauses, sans dependre de PySAT."""

    def test_basic_two_clause_cnf(self, tmp_path):
        cnf = tmp_path / "b.cnf"
        cnf.write_text("p cnf 2 2\n1 0\n2 0\n")
        num_vars, clauses = parse_dimacs_cnf(str(cnf))
        assert num_vars == 2
        assert clauses == [[1], [2]]

    def test_skips_comment_and_percent_lines(self, tmp_path):
        cnf = tmp_path / "c.cnf"
        cnf.write_text("c a comment\n%percent-ish not a clause\np cnf 1 1\n1 0\n")
        num_vars, clauses = parse_dimacs_cnf(str(cnf))
        assert num_vars == 1
        assert clauses == [[1]]

    def test_num_vars_from_p_line(self, tmp_path):
        cnf = tmp_path / "v.cnf"
        cnf.write_text("p cnf 5 1\n1 0\n")
        assert parse_dimacs_cnf(str(cnf))[0] == 5

    def test_bare_zero_terminator_not_added_as_empty_clause(self, tmp_path):
        # A line with only "0" parses to [] and is skipped (no empty clause).
        cnf = tmp_path / "e.cnf"
        cnf.write_text("p cnf 1 1\n0\n1 0\n")
        _, clauses = parse_dimacs_cnf(str(cnf))
        assert clauses == [[1]]


# ── solve_sat / enumerate_solutions (PySAT-dependent) ───────────────────────


@pytest.mark.skipif(not PYSAT_AVAILABLE, reason="PySAT not installed")
class TestSolveSat:
    """solve_sat : SAT/UNSAT, assumptions, stats. Backend CaDiCaL."""

    def test_sat_returns_true_and_model(self):
        is_sat, model, stats = solve_sat([[1], [2]], SOLVER)
        assert is_sat is True
        assert model is not None
        assert 1 in model and 2 in model
        assert stats["status"] == "SAT"

    def test_unsat_returns_false_no_model(self):
        is_sat, model, stats = solve_sat([[1], [-1]], SOLVER)
        assert is_sat is False
        assert model is None
        assert stats["status"] == "UNSAT"

    def test_assumptions_force_unsat(self):
        # (x1) is SAT alone, but assumption -1 forces UNSAT.
        is_sat, model, stats = solve_sat([[1]], SOLVER, assumptions=[-1])
        assert is_sat is False
        # Unsat core should be populated when assumptions are used.
        assert "unsat_core" in stats

    def test_assumptions_keep_sat(self):
        is_sat, model, _ = solve_sat([[1], [2]], SOLVER, assumptions=[1])
        assert is_sat is True
        assert 1 in model

    def test_stats_solver_and_counts(self):
        _, _, stats = solve_sat([[1], [2], [-3]], SOLVER)
        assert stats["solver"] == SOLVER
        assert stats["num_clauses"] == 3
        # max(|lit|) over all clauses = 3
        assert stats["num_variables"] == 3

    def test_stats_solve_time_recorded(self):
        _, _, stats = solve_sat([[1]], SOLVER)
        assert "solve_time" in stats and stats["solve_time"] >= 0.0


@pytest.mark.skipif(not PYSAT_AVAILABLE, reason="PySAT not installed")
class TestEnumerateSolutions:
    """enumerate_solutions : generateur de modeles avec blocking clauses."""

    def test_yields_at_least_one_sat_model(self):
        models = list(enumerate_solutions([[1], [2]], SOLVER, max_solutions=5))
        assert len(models) >= 1
        assert all(1 in m and 2 in m for m in models)

    def test_unsat_yields_nothing(self):
        assert list(enumerate_solutions([[1], [-1]], SOLVER, max_solutions=5)) == []

    def test_max_solutions_caps_count(self):
        # 3 free vars -> up to 8 models; cap at 2.
        models = list(enumerate_solutions([[1, -1]], SOLVER, max_solutions=2))
        # Solver may yield fewer than max if it stops, but never more.
        assert 1 <= len(models) <= 2
        assert len({tuple(m) for m in models}) == len(models)  # all distinct

    def test_blocking_clause_excludes_previous(self):
        # Each yielded model must differ from the others (blocking works).
        models = list(enumerate_solutions([[1, -1], [2, -2]], SOLVER, max_solutions=4))
        assert len({tuple(m) for m in models}) == len(models)


# ── Module-level constants ──────────────────────────────────────────────────


class TestRecommendedSolvers:
    def test_recommended_solvers_sane(self):
        assert len(RECOMMENDED_SOLVERS) >= 1
        for name, desc in RECOMMENDED_SOLVERS:
            assert isinstance(name, str) and name
            assert isinstance(desc, str) and desc


# ── main() : regression dual-status (la PR) ─────────────────────────────────


@pytest.mark.skipif(not PYSAT_AVAILABLE, reason="PySAT not installed")
class TestMainAllSolutionsDualStatus:
    """Regression : --all-solutions UNSAT ne doit plus afficher un double
    statut "s SATISFIABLE" + "s UNSATISFIABLE" (bug jumeau de #7380)."""

    def test_unsat_all_solutions_single_status(self, tmp_path):
        rc, out, _ = _run_cli("p cnf 1 2\n1 0\n-1 0\n", tmp_path, "--all-solutions")
        assert rc == 1
        assert "s UNSATISFIABLE" in out
        # The bug: SATISFIABLE printed upfront then UNSATISFIABLE. Must not
        # contain BOTH on an UNSAT instance.
        assert not (
            "s SATISFIABLE" in out and "s UNSATISFIABLE" in out
        ), f"contradictory dual status:\n{out}"

    def test_unsat_all_solutions_no_premature_satisfiable(self, tmp_path):
        rc, out, _ = _run_cli("p cnf 1 2\n1 0\n-1 0\n", tmp_path, "--all-solutions")
        assert "s SATISFIABLE" not in out  # zero models -> never SAT

    def test_sat_all_solutions_prints_satisfiable_and_model(self, tmp_path):
        rc, out, _ = _run_cli("p cnf 2 2\n1 0\n2 0\n", tmp_path, "--all-solutions", "--max", "3")
        assert rc == 0
        assert "s SATISFIABLE" in out
        assert "v " in out  # at least one model line
        assert "Found" in out

    def test_sat_all_solutions_emits_satisfiable_exactly_once(self, tmp_path):
        rc, out, _ = _run_cli("p cnf 2 2\n1 0\n2 0\n", tmp_path, "--all-solutions", "--max", "3")
        assert out.count("s SATISFIABLE") == 1


# ── main() : single-solution path (regression check, unaffected by fix) ─────


@pytest.mark.skipif(not PYSAT_AVAILABLE, reason="PySAT not installed")
class TestMainSingleSolution:
    def test_single_sat_exit_0(self, tmp_path):
        rc, out, _ = _run_cli("p cnf 2 2\n1 0\n2 0\n", tmp_path)
        assert rc == 0
        assert "s SATISFIABLE" in out
        assert "v " in out

    def test_single_unsat_exit_1(self, tmp_path):
        rc, out, _ = _run_cli("p cnf 1 2\n1 0\n-1 0\n", tmp_path)
        assert rc == 1
        assert "s UNSATISFIABLE" in out

    def test_missing_file_exit_1(self, tmp_path):
        proc = subprocess.run(
            [PYEXE, str(SCRIPT), str(tmp_path / "does_not_exist.cnf")],
            capture_output=True, text=True, timeout=60,
        )
        assert proc.returncode == 1
        assert "not found" in proc.stderr.lower() or "not found" in proc.stdout.lower()
