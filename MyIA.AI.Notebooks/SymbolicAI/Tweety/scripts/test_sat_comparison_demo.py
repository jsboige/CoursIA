# -*- coding: utf-8 -*-
"""Tests pour le module scripts/sat_comparison_demo.py.

Module companion de la serie notebooks Tweety : demonstration de comparaison
des solveurs SAT (CaDiCaL, Glucose, MiniSat) sur des problemes classiques.

Les 4 generateurs CNF sont des fonctions PURES deterministes (aucun I/O,
n'utilisent PAS PySAT) : on peut les tester structurellement ET verifier leurs
invariants mathematiques en resolvant le CNF produit (pigeonhole UNSAT quand
n_pigeons > n_holes, 3-reines UNSAT, 4-reines SAT, coloration de cycle impair
UNSAT en 2 couleurs). C'est cette verification par solveur qui prouve que les
ENCODAGES sont corrects, pas seulement que la structure est plausible.

Couverture :
  - generate_pigeonhole : nb de clauses "au-moins-un-trou", clauses binaires
    "au-plus-un-par-trou", encodage var(i,j)=(i-1)*n_holes+j, UNSAT quand
    n_pigeons > n_holes (verifie par solveur).
  - generate_nqueens_sat : nb de clauses "au-moins-une-par-ligne", range des
    variables, 4-reines SAT / 3-reines UNSAT (verifie par solveur).
  - generate_random_3sat : nb de clauses = int(n_vars*ratio), exactement 3
    litteraux par clause, |lit| dans [1,n_vars], reproductibilite par seed.
  - generate_graph_coloring : clauses "au-moins-une-couleur" par sommet,
    2-coloration cycle impair UNSAT / 3-coloration cycle SAT (solveur).
  - benchmark_problem : retourne dict {status,time_ms} par solveur, gere le
    cas "clauses vides" sans crasher.
"""

import random
import sys
from pathlib import Path

import pytest

# sat_comparison_demo.py calls exit(1) at import if pysat is missing, so guard
# the import by ensuring pysat is present first (tests SKIP cleanly otherwise).
pytest.importorskip("pysat")

SCRIPTS_DIR = Path(__file__).parent
sys.path.insert(0, str(SCRIPTS_DIR))

from sat_comparison_demo import (  # noqa: E402
    benchmark_problem,
    generate_graph_coloring,
    generate_nqueens_sat,
    generate_pigeonhole,
    generate_random_3sat,
)
from pysat.solvers import Solver  # noqa: E402

SOLVER = "cadical195"


def _is_sat(clauses: list) -> bool:
    """Solve a CNF with CaDiCaL and return satisfiability."""
    with Solver(name=SOLVER, bootstrap_with=clauses) as s:
        return bool(s.solve())


# ── generate_pigeonhole ─────────────────────────────────────────────────────


class TestGeneratePigeonhole:
    """Pigeonhole : n pigeons dans n_holes trous. var(i,j) = (i-1)*n_holes + j."""

    def test_n_at_least_one_hole_clauses(self):
        # Each pigeon gets exactly one positive "at-least-one-hole" clause.
        clauses = generate_pigeonhole(5, 4)
        positive_clauses = [c for c in clauses if all(lit > 0 for lit in c)]
        assert len(positive_clauses) == 5  # one per pigeon
        for c in positive_clauses:
            assert len(c) == 4  # n_holes literals

    def test_at_most_one_per_hole_clauses_are_binary_negative(self):
        clauses = generate_pigeonhole(3, 2)
        # At-most-one clauses are [-var1, -var2] (binary, all negative).
        amo = [c for c in clauses if all(lit < 0 for lit in c)]
        for c in amo:
            assert len(c) == 2

    def test_var_encoding_range(self):
        # var(i,j) = (i-1)*n_holes + j ; max = n_pigeons * n_holes.
        clauses = generate_pigeonhole(5, 4)
        max_var = max(abs(lit) for c in clauses for lit in c)
        assert max_var == 5 * 4  # = 20

    def test_unsat_when_more_pigeons_than_holes(self):
        # Pigeonhole principle: 4 pigeons in 3 holes is UNSAT (verifie au solveur).
        assert _is_sat(generate_pigeonhole(4, 3)) is False

    def test_sat_when_enough_holes(self):
        # n pigeons in n holes is SAT (one pigeon per hole is a valid assignment).
        assert _is_sat(generate_pigeonhole(3, 3)) is True


# ── generate_nqueens_sat ────────────────────────────────────────────────────


class TestGenerateNqueensSat:
    """N-Reines : x_{i,j} = (i-1)*n + j. Au-moins-une / au-plus-une par ligne,
    colonne, et diagonale."""

    def test_n_row_at_least_one_clauses(self):
        clauses = generate_nqueens_sat(8)
        positive_clauses = [c for c in clauses if all(lit > 0 for lit in c)]
        # Exactly one "at-least-one-per-row" clause per row (n rows).
        assert len(positive_clauses) == 8
        for c in positive_clauses:
            assert len(c) == 8  # one literal per column

    def test_var_range(self):
        clauses = generate_nqueens_sat(8)
        max_var = max(abs(lit) for c in clauses for lit in c)
        assert max_var == 8 * 8  # = 64

    def test_4_queens_is_sat(self):
        # The 4-queens problem has solutions (2 of them).
        assert _is_sat(generate_nqueens_sat(4)) is True

    def test_3_queens_is_unsat(self):
        # The 3-queens problem has NO solution.
        assert _is_sat(generate_nqueens_sat(3)) is False

    def test_2_queens_is_unsat(self):
        assert _is_sat(generate_nqueens_sat(2)) is False


# ── generate_random_3sat ────────────────────────────────────────────────────


class TestGenerateRandom3sat:
    """3-SAT aleatoire au ratio clauses/variables donne."""

    def test_clause_count_respects_ratio(self):
        # n_clauses = int(n_vars * ratio).
        clauses = generate_random_3sat(50, ratio=4.26)
        assert len(clauses) == int(50 * 4.26)

    def test_each_clause_has_exactly_3_literals(self):
        clauses = generate_random_3sat(30, ratio=3.0)
        for c in clauses:
            assert len(c) == 3

    def test_literal_absolute_value_in_range(self):
        n_vars = 20
        clauses = generate_random_3sat(n_vars, ratio=3.0)
        for c in clauses:
            for lit in c:
                assert 1 <= abs(lit) <= n_vars

    def test_same_seed_reproducible(self):
        random.seed(42)
        a = generate_random_3sat(20, ratio=3.0)
        random.seed(42)
        b = generate_random_3sat(20, ratio=3.0)
        assert a == b

    def test_literal_uniqueness_within_clause(self):
        # random.sample guarantees 3 distinct base vars; with signs they stay distinct.
        clauses = generate_random_3sat(50, ratio=4.0)
        for c in clauses:
            assert len({abs(lit) for lit in c}) == 3


# ── generate_graph_coloring ─────────────────────────────────────────────────


class TestGenerateGraphColoring:
    """Coloration de graphe : x_{v,c} = (v-1)*n_colors + c."""

    def test_n_vertices_at_least_one_color_clauses(self):
        edges = [(1, 2), (2, 3)]
        clauses = generate_graph_coloring(3, edges, 3)
        positive = [c for c in clauses if all(lit > 0 for lit in c)]
        assert len(positive) == 3  # one per vertex
        for c in positive:
            assert len(c) == 3  # n_colors literals

    def test_two_coloring_odd_cycle_unsat(self):
        # Odd cycle (length 5) is NOT 2-colorable.
        edges = [(i, i + 1) for i in range(1, 5)] + [(5, 1)]
        clauses = generate_graph_coloring(5, edges, 2)
        assert _is_sat(clauses) is False

    def test_three_coloring_odd_cycle_sat(self):
        # Odd cycle IS 3-colorable.
        edges = [(i, i + 1) for i in range(1, 5)] + [(5, 1)]
        clauses = generate_graph_coloring(5, edges, 3)
        assert _is_sat(clauses) is True

    def test_two_coloring_even_cycle_sat(self):
        # Even cycle (length 4) IS 2-colorable.
        edges = [(1, 2), (2, 3), (3, 4), (4, 1)]
        clauses = generate_graph_coloring(4, edges, 2)
        assert _is_sat(clauses) is True


# ── benchmark_problem ───────────────────────────────────────────────────────


class TestBenchmarkProblem:
    """benchmark_problem : orchestre la resolution + affichage, retourne dict."""

    def test_returns_status_and_time_per_solver(self, capsys):
        results = benchmark_problem("unit", [[1], [2]], [SOLVER])
        capsys.readouterr()  # drain prints
        assert SOLVER in results
        entry = results[SOLVER]
        assert entry["status"] == "SAT"
        assert "time_ms" in entry and entry["time_ms"] >= 0

    def test_unsat_problem_reports_unsat(self, capsys):
        results = benchmark_problem("u", [[1], [-1]], [SOLVER])
        capsys.readouterr()
        assert results[SOLVER]["status"] == "UNSAT"

    def test_empty_clauses_does_not_crash(self, capsys):
        # n_vars=0 -> "Probleme vide" branch; solver still produces a verdict.
        results = benchmark_problem("empty", [], [SOLVER])
        out = capsys.readouterr().out
        assert "Probleme vide" in out
        assert SOLVER in results
