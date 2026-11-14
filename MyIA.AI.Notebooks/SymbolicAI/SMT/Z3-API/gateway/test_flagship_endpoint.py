# -*- coding: utf-8 -*-
"""Tests de l'endpoint porte par le carnet phare (acceptation v2 de #21100).

Le service n'a plus de carnet dedie : la cellule annotee ``# POST /sudoku/solve``
vit dans ``../Z3-02-Sudoku-Python.ipynb``, celui du cours. Ces tests verifient
les deux moities du contrat :

1. **Structure** : le carnet phare porte exactement une cellule annotee, et son
   annotation est ``# POST /sudoku/solve`` ;
2. **Fonction** : cette cellule, executee telle quelle avec les formes de
   ``REQUEST`` que Kernel Gateway injecte (chaine JSON, dict, corps stringifie,
   enveloppe surnumeraire), rend le JSON attendu sur le puzzle facile.

Aucun reseau, aucun service : les cellules sont executees dans un espace de
noms neuf, exactement comme le kernel les executerait apres le seed.

Cable dans ``.github/workflows/scripts-tests.yml`` a cote de
``test_z3_sudoku_core.py`` et ``test_run_gateway.py``.
"""
import io
import json
import os
import sys
import unittest
from contextlib import redirect_stdout
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

GATEWAY_DIR = Path(__file__).resolve().parent
NOTEBOOK = (GATEWAY_DIR / ".." / "Z3-02-Sudoku-Python.ipynb").resolve()

ANNOTATION = "# POST /sudoku/solve"
PUZZLE_FACILE = (
    "530070000600195000098000060800060003400803001700020006060000280000419005000080079"
)
SOLUTION_FACILE = (
    "534678912672195348198342567859761423426853791713924856961537284287419635345286179"
)


def load_cells():
    """Cellules du carnet phare, dans l'ordre."""
    with NOTEBOOK.open(encoding="utf-8") as handle:
        return json.load(handle)["cells"]


def source_of(cell):
    return "".join(cell["source"])


def endpoint_indices(cells):
    """Indices des cellules dont la PREMIERE ligne est une annotation HTTP.

    C'est la regle exacte de Kernel Gateway en mode ``notebook-http`` : une
    annotation ailleurs qu'en premiere ligne n'enregistre aucune ressource.
    """
    found = []
    for index, cell in enumerate(cells):
        if cell["cell_type"] != "code":
            continue
        first = source_of(cell).splitlines()[0].strip() if source_of(cell).strip() else ""
        if first.startswith("# GET ") or first.startswith("# POST "):
            found.append((index, first))
    return found


class TestEndpointStructure(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.cells = load_cells()

    def test_flagship_notebook_exists(self):
        self.assertTrue(NOTEBOOK.is_file(), NOTEBOOK)

    def test_exactly_one_http_annotation_and_it_is_the_sudoku_endpoint(self):
        annotations = endpoint_indices(self.cells)
        self.assertEqual(
            [first for _, first in annotations],
            [ANNOTATION],
            "le carnet phare doit porter exactement une annotation HTTP : %s"
            % (annotations,),
        )

    def test_endpoint_precedes_the_summary(self):
        """La section service est pedagogiquement placee avant le recapitulatif."""
        index = endpoint_indices(self.cells)[0][0]
        rest = [source_of(c).lstrip() for c in self.cells[index + 1 :]]
        self.assertTrue(
            any(s.startswith("## Recapitulatif") for s in rest),
            "le recapitulatif doit rester la derniere section du carnet",
        )

    def test_preparation_cell_precedes_the_endpoint(self):
        """Une cellule de preparation charge le coeur avant la premiere requete."""
        index = endpoint_indices(self.cells)[0][0]
        preparations = [
            source_of(c)
            for c in self.cells[:index]
            if c["cell_type"] == "code"
            and "from z3_sudoku_core import solve_request" in source_of(c)
        ]
        self.assertEqual(len(preparations), 1, "cellule de preparation introuvable")


class TestEndpointBehaviour(unittest.TestCase):
    """Execute reellement les cellules du carnet, sans reseau ni service."""

    @classmethod
    def setUpClass(cls):
        cells = load_cells()
        index = endpoint_indices(cells)[0][0]
        preparation = [
            source_of(c)
            for c in cells[:index]
            if c["cell_type"] == "code"
            and "from z3_sudoku_core import solve_request" in source_of(c)
        ][0]
        cls.endpoint_source = source_of(cells[index])
        cls.namespace = {}
        with redirect_stdout(io.StringIO()):
            exec(compile(preparation, "<preparation>", "exec"), cls.namespace)

    def run_endpoint(self, request, extra=None):
        """Execute la cellule d'endpoint avec la forme de REQUEST demandee.

        ``extra`` simule les globales que le seed laisse en place avant
        l'endpoint (par exemple ``solution_facile``, calculee en section 2).
        """
        namespace = dict(self.namespace)
        namespace.update(extra or {})
        namespace["REQUEST"] = request
        buffer = io.StringIO()
        with redirect_stdout(buffer):
            exec(compile(self.endpoint_source, "<endpoint>", "exec"), namespace)
        lines = [line for line in buffer.getvalue().splitlines() if line.strip()]
        self.assertTrue(lines, "l'endpoint n'a rien ecrit sur la sortie standard")
        return json.loads(lines[0]), lines

    def assert_solved(self, response):
        self.assertEqual(response["status"], "sat", response)
        self.assertEqual(response["solution"], SOLUTION_FACILE, response)
        self.assertIsInstance(response["time_ms"], float)

    def test_local_mode_runs_the_demo_and_checks_the_course_solver(self):
        """Hors gateway (REQUEST absent), la cellule sert de demonstration.

        Le noyau a deja execute tout le carnet au seed : ``solution_facile``
        (section 2) est donc presente, et la cellule doit confronter la reponse
        du service au resultat du solveur du cours.
        """
        solution_carnet = [
            [int(SOLUTION_FACILE[9 * r + c]) for c in range(9)] for r in range(9)
        ]
        response, lines = self.run_endpoint(None, {"solution_facile": solution_carnet})
        self.assert_solved(response)
        self.assertTrue(
            any("Verification locale" in line for line in lines),
            "le mode local doit confronter le service au solveur du carnet",
        )
        self.assertTrue(
            any("solution identique" in line for line in lines),
            "le service et le solveur du carnet doivent rendre la meme solution : %s"
            % (lines,),
        )

    def test_gateway_json_string_form(self):
        """Forme mesuree sur gateway 3.x : REQUEST est une chaine JSON."""
        response, _ = self.run_endpoint(json.dumps({"body": {"puzzle": PUZZLE_FACILE}}))
        self.assert_solved(response)

    def test_gateway_dict_form(self):
        """Les versions qui injectent un dict direct restent acceptees."""
        response, _ = self.run_endpoint({"body": {"puzzle": PUZZLE_FACILE}})
        self.assert_solved(response)

    def test_body_received_as_raw_json_string(self):
        """Corps non parse par la gateway : chaine JSON brute dans ``body``."""
        response, _ = self.run_endpoint(
            {"body": json.dumps({"puzzle": PUZZLE_FACILE})}
        )
        self.assert_solved(response)

    def test_one_too_many_envelope_is_unwrapped(self):
        """Client qui enveloppe son payload une fois de trop (review #22555)."""
        response, _ = self.run_endpoint(
            json.dumps({"body": {"body": json.dumps({"puzzle": PUZZLE_FACILE})}})
        )
        self.assert_solved(response)

    def test_invalid_input_is_reported_not_swallowed(self):
        response, _ = self.run_endpoint({"body": {"puzzle": "trop court"}})
        self.assertEqual(response["status"], "invalid", response)
        self.assertIsNone(response["solution"])
        self.assertNotEqual(response["status"], "sat")

    def test_missing_core_returns_a_structured_error(self):
        """Un coeur indisponible ne laisse pas le client expirer (#22439)."""
        namespace = dict(self.namespace)
        namespace["CORE_IMPORT_ERROR"] = "module introuvable (test)"
        namespace["REQUEST"] = {"body": {"puzzle": PUZZLE_FACILE}}
        buffer = io.StringIO()
        with redirect_stdout(buffer):
            exec(compile(self.endpoint_source, "<endpoint>", "exec"), namespace)
        response = json.loads(buffer.getvalue().splitlines()[0])
        self.assertEqual(response["status"], "error", response)
        self.assertIn("module introuvable (test)", response["detail"])


if __name__ == "__main__":
    unittest.main(verbosity=2)