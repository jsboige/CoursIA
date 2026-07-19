"""Regression tests for maxsat_solver.py (RC2 MaxSAT wrapper).

Pinned bug: ``--enumerate`` on a WCNF whose hard clauses are UNSAT used to
print ``s OPTIMUM FOUND`` (with zero enumerated solutions) instead of
``s UNSATISFIABLE``, contradicting the single-solution branch which correctly
reports UNSAT. The enumerate branch now checks for an empty solution set and
mirrors the single-solution UNSAT handling.

``pysat`` (python-sat) is a declared Tweety dependency but not installed in
every environment, so the whole module skips cleanly when it is unavailable.
"""

import sys
import subprocess
import textwrap
from pathlib import Path

import pytest

pytest.importorskip("pysat", reason="python-sat (pysat) required for maxsat_solver tests")

EXT_TOOLS_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(EXT_TOOLS_DIR))

import maxsat_solver  # noqa: E402  (after importorskip + sys.path)


UNSAT_HARD_WCNF = textwrap.dedent("""\
    c UNSAT hard clauses: x1 AND -x1
    p wcnf 1 3 2
    2 1 0
    2 -1 0
    1 1 0
""")

# Hard: x1 AND x2 (top weight 100). Soft: (-x1 OR -x2) w=5, (-x3) w=3.
# Hard forces x1=x2=True -> clause (-x1 v -x2) violated (cost 5); x3=False
# avoids the w=3 cost -> optimal cost = 5, satisfiable.
SAT_WCNF = textwrap.dedent("""\
    c SAT MaxSAT
    p wcnf 3 4 100
    100 1 0
    100 2 0
    5 -1 -2 0
    3 -3 0
""")


def _write(tmp_path: Path, name: str, content: str) -> Path:
    p = tmp_path / name
    p.write_text(content)
    return p


def _run(wcnf_path: Path, *extra: str) -> subprocess.CompletedProcess:
    return subprocess.run(
        [sys.executable, str(EXT_TOOLS_DIR / "maxsat_solver.py"), str(wcnf_path), *extra],
        capture_output=True,
        text=True,
    )


# --- Regression pin: the bug this file exists for ---------------------------

def test_enumerate_unsat_reports_unsatisfiable(tmp_path):
    """``--enumerate`` on UNSAT hard clauses must report UNSATISFIABLE.

    Before the fix this printed ``s OPTIMUM FOUND`` with zero solutions
    (contradictory / false-positive optimum).
    """
    wcnf = _write(tmp_path, "unsat.wcnf", UNSAT_HARD_WCNF)
    result = _run(wcnf, "--enumerate", "5")
    assert result.returncode == 1, result.stdout
    assert "s UNSATISFIABLE" in result.stdout
    assert "s OPTIMUM FOUND" not in result.stdout, (
        "enumerate branch falsely reported an optimum on UNSAT hard clauses"
    )


def test_enumerate_unsat_no_contradictory_dual_status(tmp_path):
    """Status line must appear exactly once (no SAT+UNSAT contradiction)."""
    wcnf = _write(tmp_path, "unsat.wcnf", UNSAT_HARD_WCNF)
    result = _run(wcnf, "--enumerate", "5")
    status_lines = [ln for ln in result.stdout.splitlines() if ln.startswith("s ")]
    assert len(status_lines) == 1, status_lines
    assert status_lines[0] == "s UNSATISFIABLE"


# --- Normal-path preservation (enumerate + single on SAT input) -------------

def test_enumerate_sat_finds_optimum(tmp_path):
    wcnf = _write(tmp_path, "sat.wcnf", SAT_WCNF)
    result = _run(wcnf, "--enumerate", "3")
    assert result.returncode == 0, result.stdout
    assert "s OPTIMUM FOUND" in result.stdout
    assert "o 5" in result.stdout  # optimal cost is 5 (see SAT_WCNF comment)


def test_enumerate_respects_top_k(tmp_path):
    wcnf = _write(tmp_path, "sat.wcnf", SAT_WCNF)
    for k in (1, 2):
        result = _run(wcnf, "--enumerate", str(k))
        assert result.returncode == 0, result.stdout
        # exactly k solution lines (v <lits> 0), after the single status line
        v_lines = [ln for ln in result.stdout.splitlines() if ln.startswith("v ")]
        assert len(v_lines) == k, (k, result.stdout)


def test_single_unsat_reports_unsatisfiable(tmp_path):
    wcnf = _write(tmp_path, "unsat.wcnf", UNSAT_HARD_WCNF)
    result = _run(wcnf)
    assert result.returncode == 1, result.stdout
    assert result.stdout.strip() == "s UNSATISFIABLE"


def test_single_sat_finds_optimum(tmp_path):
    wcnf = _write(tmp_path, "sat.wcnf", SAT_WCNF)
    result = _run(wcnf)
    assert result.returncode == 0, result.stdout
    assert "s OPTIMUM FOUND" in result.stdout
    assert "o 5" in result.stdout
    assert any(ln.startswith("v ") for ln in result.stdout.splitlines())


# --- Unit tests for parse_wcnf + solve_maxsat -------------------------------

def test_parse_wcnf_classifies_hard_and_soft(tmp_path):
    wcnf = _write(tmp_path, "sat.wcnf", SAT_WCNF)
    formula = maxsat_solver.parse_wcnf(str(wcnf))
    # topw is the hard/soft threshold declared on the `p wcnf` line; PySAT
    # may adjust it internally, so we only check it was parsed (>= declared).
    assert formula.topw >= 100
    assert len(formula.hard) == 2     # x1, x2
    assert len(formula.soft) == 2     # (-x1 v -x2), (-x3)
    assert list(formula.wght) == [5, 3]


def test_solve_maxsat_sat_returns_model_and_cost(tmp_path):
    wcnf = _write(tmp_path, "sat.wcnf", SAT_WCNF)
    model, cost = maxsat_solver.solve_maxsat(maxsat_solver.parse_wcnf(str(wcnf)))
    assert model is not None
    assert cost == 5


def test_solve_maxsat_unsat_returns_none(tmp_path):
    wcnf = _write(tmp_path, "unsat.wcnf", UNSAT_HARD_WCNF)
    model, cost = maxsat_solver.solve_maxsat(maxsat_solver.parse_wcnf(str(wcnf)))
    assert model is None
    assert cost is None
