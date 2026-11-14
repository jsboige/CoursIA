# -*- coding: utf-8 -*-
"""Tests du lanceur du service Kernel Gateway Z3 Sudoku (issue #22439).

Cables dans ``.github/workflows/scripts-tests.yml`` a cote de
``test_z3_sudoku_core.py``.

Execution locale : ``python test_run_gateway.py`` ou ``python -m pytest``.
"""
import os
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import run_gateway
from run_gateway import build_arguments, core_dir, main, preflight


class TestCoreDir(unittest.TestCase):
    def test_core_dir_is_the_launcher_directory(self):
        """Le dossier servi est celui du lanceur, quoi qu'il arrive au cwd."""
        self.assertEqual(core_dir(), Path(run_gateway.__file__).resolve().parent)

    def test_core_dir_ignores_current_working_directory(self):
        """Defaut corrige par #22439 : le demarrage ne depend plus du cwd."""
        reference = core_dir()
        previous = os.getcwd()
        with tempfile.TemporaryDirectory() as ailleurs:
            try:
                os.chdir(ailleurs)
                self.assertEqual(core_dir(), reference)
            finally:
                os.chdir(previous)


class TestPreflight(unittest.TestCase):
    def test_real_directory_is_ready(self):
        """Le dossier livre passe le preflight sans aucun probleme."""
        self.assertEqual(preflight(core_dir()), [])

    def test_empty_directory_reports_missing_core_and_notebook(self):
        """Sans coeur ni carnet, les deux manques sont nommes, pas devines.

        Le nom du carnet est neutralise le temps du test : le vrai vit un
        niveau au-dessus du dossier servi, et un ``../`` depuis un dossier
        temporaire dependrait du contenu de son parent.
        """
        original = run_gateway.SERVICE_NOTEBOOK
        run_gateway.SERVICE_NOTEBOOK = "carnet-de-service-absent.ipynb"
        try:
            with tempfile.TemporaryDirectory() as vide:
                problems = preflight(Path(vide))
        finally:
            run_gateway.SERVICE_NOTEBOOK = original
        joined = " | ".join(problems)
        self.assertTrue(any("coeur absent" in p for p in problems), joined)
        self.assertTrue(any("carnet de service absent" in p for p in problems), joined)

    def test_broken_core_is_refused_before_starting(self):
        """Un coeur syntaxiquement casse est refuse, avec le motif."""
        with tempfile.TemporaryDirectory() as dossier:
            base = Path(dossier)
            (base / "z3_sudoku_core.py").write_text("def solve_request(:\n", encoding="utf-8")
            problems = preflight(base)
        self.assertTrue(any("coeur non importable" in p for p in problems), problems)

    def test_core_without_solve_request_is_refused(self):
        """Un coeur importable mais muet sur solve_request est refuse."""
        with tempfile.TemporaryDirectory() as dossier:
            base = Path(dossier)
            (base / "z3_sudoku_core.py").write_text("VALEUR = 1\n", encoding="utf-8")
            problems = preflight(base)
        self.assertTrue(any("solve_request" in p for p in problems), problems)

    def test_service_notebook_is_the_flagship_notebook(self):
        """Le carnet servi est le carnet phare : un seul fichier, deux usages."""
        serves = (core_dir() / run_gateway.SERVICE_NOTEBOOK).resolve()
        self.assertTrue(serves.is_file(), serves)
        self.assertEqual(serves.name, "Z3-02-Sudoku-Python.ipynb")
        self.assertEqual(serves.parent.name, "Z3-API")
        # L'ancien carnet de service dedie est retire : sa fonction est portee
        # par les cellules de la section 4 du carnet phare.
        self.assertFalse((core_dir() / "z3-sudoku-service.ipynb").exists())


class TestCommandLine(unittest.TestCase):
    def test_seed_uri_is_relative_to_the_served_directory(self):
        """Le seed est relatif : le gateway se place lui-meme dans le dossier.

        Le carnet servi vivant un niveau au-dessus du lanceur, le chemin porte
        un ``../`` : il reste relatif au dossier ou le gateway se place, donc
        ouvert par le kernel quel que soit le repertoire de lancement.
        """
        arguments = build_arguments(core_dir(), 8900, [])
        self.assertIn(
            "--KernelGatewayApp.seed_uri=../Z3-02-Sudoku-Python.ipynb", arguments
        )
        self.assertIn("--KernelGatewayApp.port=8900", arguments)
        self.assertIn("--JupyterWebsocketPersonality.list_kernels=True", arguments)
        self.assertNotIn(str(core_dir()), " ".join(arguments))

    def test_check_only_returns_zero_on_the_real_directory(self):
        """`--check-only` sort 0 : c'est la sonde utilisable en CI."""
        self.assertEqual(main(["--check-only"]), 0)

    def test_check_only_fails_fast_when_the_core_is_missing(self):
        """Un coeur absent sort 2 immediatement, sans demarrer le gateway."""
        previous = os.getcwd()
        with tempfile.TemporaryDirectory() as vide:
            original = run_gateway.core_dir
            run_gateway.core_dir = lambda: Path(vide)
            try:
                os.chdir(vide)
                code = main(["--check-only"])
            finally:
                run_gateway.core_dir = original
                os.chdir(previous)
        self.assertEqual(code, run_gateway.EXIT_PREFLIGHT)


if __name__ == "__main__":
    unittest.main(verbosity=2)
