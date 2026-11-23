# -*- coding: utf-8 -*-
"""Tests unitaires du coeur Z3 Sudoku (service Kernel Gateway, issue #21100).

Cables dans ``.github/workflows/scripts-tests.yml`` (job pytest, avec
``pip install z3-solver``).
Execution locale : ``python test_z3_sudoku_core.py`` ou ``python -m pytest``.
"""
import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from z3_sudoku_core import parse_puzzle, solve_grid, solve_request

# Puzzle facile du carnet phare Z3-02-Sudoku-Python.ipynb (cellule 3).
PUZZLE_FACILE = (
    "530070000"
    "600195000"
    "098000060"
    "800060003"
    "400803001"
    "700020006"
    "060000280"
    "000419005"
    "000080079"
)
# Solution attendue (cellule 5 du carnet phare).
SOLUTION_FACILE = (
    "534678912"
    "672195348"
    "198342567"
    "859761423"
    "426853791"
    "713924856"
    "961537284"
    "287419635"
    "345286179"
)
# Puzzle contradictoire : deux 5 sur la premiere ligne -> insatisfiable.
PUZZLE_UNSAT = (
    "550070000"
    "600195000"
    "098000060"
    "800060003"
    "400803001"
    "700020006"
    "060000280"
    "000419005"
    "000080079"
)


class TestParsePuzzle(unittest.TestCase):
    def test_grille_valide(self):
        grille = parse_puzzle(PUZZLE_FACILE)
        self.assertIsNotNone(grille)
        self.assertEqual(len(grille), 9)
        self.assertEqual(grille[0][:3], [5, 3, 0])
        self.assertEqual(grille[8][8], 9)

    def test_points_comme_vides(self):
        self.assertEqual(
            parse_puzzle(PUZZLE_FACILE.replace("0", ".")),
            parse_puzzle(PUZZLE_FACILE),
        )

    def test_separateurs_ignores(self):
        formate = "\n".join(PUZZLE_FACILE[i * 9:(i + 1) * 9] for i in range(9))
        self.assertEqual(parse_puzzle(formate), parse_puzzle(PUZZLE_FACILE))

    def test_longueur_invalide(self):
        self.assertIsNone(parse_puzzle(PUZZLE_FACILE[:-1]))
        self.assertIsNone(parse_puzzle(PUZZLE_FACILE + "0"))
        self.assertIsNone(parse_puzzle(""))

    def test_caractere_invalide(self):
        self.assertIsNone(parse_puzzle(PUZZLE_FACILE[:-1] + "x"))

    def test_entree_non_chaine(self):
        self.assertIsNone(parse_puzzle(None))
        self.assertIsNone(parse_puzzle(42))


class TestSolveGrid(unittest.TestCase):
    def test_resolution_facile(self):
        solution = solve_grid(parse_puzzle(PUZZLE_FACILE))
        self.assertIsNotNone(solution)
        compact = "".join(str(v) for ligne in solution for v in ligne)
        self.assertEqual(compact, SOLUTION_FACILE)

    def test_insatisfiable(self):
        self.assertIsNone(solve_grid(parse_puzzle(PUZZLE_UNSAT)))


class TestSolveRequest(unittest.TestCase):
    def test_sat(self):
        reponse = solve_request(PUZZLE_FACILE)
        self.assertEqual(reponse["status"], "sat")
        self.assertEqual(reponse["solution"], SOLUTION_FACILE)
        self.assertGreaterEqual(reponse["time_ms"], 0.0)

    def test_unsat(self):
        reponse = solve_request(PUZZLE_UNSAT)
        self.assertEqual(reponse["status"], "unsat")
        self.assertIsNone(reponse["solution"])

    def test_invalid(self):
        reponse = solve_request("trop court")
        self.assertEqual(reponse["status"], "invalid")
        self.assertIsNone(reponse["solution"])

    def test_la_solution_respecte_les_indices(self):
        reponse = solve_request(PUZZLE_FACILE)
        for i, ch in enumerate(PUZZLE_FACILE):
            if ch != "0":
                self.assertEqual(reponse["solution"][i], ch, f"case {i} alteree")


if __name__ == "__main__":
    unittest.main(verbosity=2)