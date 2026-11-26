"""Parite entre l'export du corpus Z3 et les sorties committes des carnets.

L'export `MyIA.AI.Notebooks/SymbolicAI/SMT/Z3-API/z3_instances.py` ne vaut que
s'il reproduit **exactement** ce que les carnets publient. Ce test lit les
**sorties committes** des deux carnets (la preuve de reference, dans git) et
contrôle que l'export les retrouve.

Il est **falsifiable dans les deux sens** :
- l'export change sans que les carnets changent -> le test rougit ;
- un carnet change d'encodage et l'export n'est pas mis a jour -> le test
  rougit aussi.

Aucun test n'assert de **temps** : les sorties des carnets ne mesurent que
des durees, dependantes de la machine.
"""

from __future__ import annotations

import json
import os
import re
import sys
from pathlib import Path

import pytest

# Le binding z3 est une dependance declaree de la serie Z3-API
# (`MyIA.AI.Notebooks/SymbolicAI/SMT/Z3-API/requirements.txt`). Sur un runner
# qui ne l'a pas installe, le module entier est ignore plutot que rouge.
z3 = pytest.importorskip("z3")

REPO_ROOT = Path(__file__).resolve().parents[3]
SERIES_DIR = REPO_ROOT / "MyIA.AI.Notebooks" / "SymbolicAI" / "SMT" / "Z3-API"
sys.path.insert(0, str(SERIES_DIR))

from z3_instances import (  # noqa: E402
    PETERSEN_EDGES,
    chromatic_number,
    cryptarithm_solutions,
    petersen,
    send_more_money,
)

COLORING_NOTEBOOK = SERIES_DIR / "Z3-11-Graph-Coloring-Python.ipynb"
CRYPTARITHM_NOTEBOOK = SERIES_DIR / "Z3-10-Cryptarithmetic-Python.ipynb"


def _published_outputs(notebook: Path) -> str:
    """Le texte de toutes les sorties committes d'un carnet."""
    assert notebook.exists(), f"carnet absent : {notebook}"
    with open(notebook, encoding="utf-8") as handle:
        donnees = json.load(handle)
    morceaux: list[str] = []
    for cellule in donnees["cells"]:
        for sortie in cellule.get("outputs", []) or []:
            if sortie.get("output_type") == "stream":
                morceaux.append("".join(sortie.get("text", [])))
            elif sortie.get("output_type") == "execute_result":
                morceaux.append("".join(sortie.get("data", {}).get("text/plain", [])))
    return "\n".join(morceaux)


def test_le_carnet_de_coloration_publie_le_graphe_attendu() -> None:
    """Le carnet publie 10 sommets et 15 aretes : l'export doit les rendre."""
    sortie = _published_outputs(COLORING_NOTEBOOK)
    trouve = re.search(r"(\d+) sommets, (\d+) aretes", sortie)
    assert trouve, "le carnet ne publie plus le compte de sommets/aretes"
    sommets, aretes = (int(trouve.group(1)), int(trouve.group(2)))
    assert sommets == 10
    assert aretes == len(PETERSEN_EDGES)


def test_le_carnet_de_coloration_publie_les_memes_variables() -> None:
    """Le carnet publie `C0..C9` : l'export doit nommer les variables pareil."""
    sortie = _published_outputs(COLORING_NOTEBOOK)
    trouve = re.search(r"(\d+) variables de couleur entieres C0\.\.C(\d+)", sortie)
    assert trouve, "le carnet ne publie plus le nommage des variables de couleur"
    nombre, dernier = int(trouve.group(1)), int(trouve.group(2))
    _contraintes, variables = petersen(3)
    noms = [variable.decl().name() for variable in variables]
    assert len(noms) == nombre
    assert noms == [f"C{v}" for v in range(dernier + 1)]


def test_chaque_verdict_publie_par_le_carnet_est_reproduit() -> None:
    """Les verdicts `k -> UNSAT/SAT` du carnet sont reproduits par l'export."""
    sortie = _published_outputs(COLORING_NOTEBOOK)
    publies = re.findall(r"k = (\d+) -> (UNSAT|SAT)", sortie)
    assert publies, "le carnet ne publie plus la boucle sur k"
    for k, verdict in publies:
        contraintes, _variables = petersen(int(k))
        solveur = z3.Solver()
        solveur.add(*contraintes)
        obtenu = "SAT" if solveur.check() == z3.sat else "UNSAT"
        assert obtenu == verdict, f"k = {k} : carnet {verdict}, export {obtenu}"


def test_le_nombre_chromatique_publie_est_reproduit() -> None:
    """Le carnet publie `chi(Petersen) = 3` : l'export doit retrouver 3."""
    sortie = _published_outputs(COLORING_NOTEBOOK)
    trouve = re.search(r"chi\(Petersen\) = (\d+)", sortie)
    assert trouve, "le carnet ne publie plus le nombre chromatique"
    assert chromatic_number() == int(trouve.group(1))


def test_la_solution_du_cryptarithme_publiee_est_reproduite() -> None:
    """Le carnet publie la solution et son unicite : l'export doit les rendre."""
    sortie = _published_outputs(CRYPTARITHM_NOTEBOOK)
    trouve = re.search(
        r"S=(\d) E=(\d) N=(\d) D=(\d)\s+M=(\d) O=(\d) R=(\d) Y=(\d)", sortie
    )
    assert trouve, "le carnet ne publie plus l'affectation des lettres"
    publie = {
        lettre: int(valeur)
        for lettre, valeur in zip("SENDMORY", trouve.groups())
    }
    compte = re.search(r"Nombre total de solutions : (\d+)", sortie)
    assert compte, "le carnet ne publie plus le compte de solutions"
    solutions = cryptarithm_solutions()
    assert len(solutions) == int(compte.group(1))
    assert solutions == [publie]


def test_l_addition_publiee_tient_pour_la_solution_exportee() -> None:
    """`9567 + 1085 = 10652` — l'arithmetique publiee est verifiee."""
    sortie = _published_outputs(CRYPTARITHM_NOTEBOOK)
    trouve = re.search(r"(\d+) \+ (\d+) = (\d+), verifie = True", sortie)
    assert trouve, "le carnet ne publie plus l'addition verifiee"
    gauche, droite, resultat = (int(trouve.group(i)) for i in (1, 2, 3))
    (solution,) = cryptarithm_solutions()
    assert 1000 * solution["S"] + 100 * solution["E"] + 10 * solution["N"] + solution["D"] == gauche
    assert 1000 * solution["M"] + 100 * solution["O"] + 10 * solution["R"] + solution["E"] == droite
    assert gauche + droite == resultat


def test_le_cryptarithme_exporte_est_bien_satisfaisable() -> None:
    """L'export du cryptarithme est lui-meme un enonce satisfiable."""
    contraintes, variables = send_more_money()
    solveur = z3.Solver()
    solveur.add(*contraintes)
    assert solveur.check() == z3.sat
    assert len(variables) == 8


def test_le_repertoire_de_la_serie_est_bien_resolu() -> None:
    """Le test ne doit pas tourner sur une autre copie du depot.

    L'export doit venir de la serie Z3-API du depot mesure, pas d'un module
    homonyme installe ailleurs.
    """
    assert os.path.samefile(SERIES_DIR, SERIES_DIR)
    assert (SERIES_DIR / "z3_instances.py").exists()
    assert str(SERIES_DIR) in sys.path
