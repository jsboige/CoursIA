# -*- coding: utf-8 -*-
"""Coeur du service Kernel Gateway Z3 Sudoku.

Logique reprise du carnet phare ``Z3-02-Sudoku-Python.ipynb`` (cellule
``resoudre_sudoku``, serie SymbolicAI/SMT/Z3-API), adaptee au contrat REST
JSON du service notebook-http (issue #21100, pli 0 de l'Epic #19571).

Contrat :
    POST /sudoku/solve  {"puzzle": "<81 caracteres, 0 ou . pour vide>"}
    -> {"status": "sat"|"unsat"|"invalid", "solution": "<81 car.>|null", "time_ms": float}
"""
from __future__ import annotations

import time
from typing import List, Optional

from z3 import Distinct, Int, Solver, sat


def parse_puzzle(text: object) -> Optional[List[List[int]]]:
    """Valide une chaine de 81 caracteres et la convertit en grille 9x9.

    Les separateurs (espaces, retours ligne, tabulations) sont ignores, ce
    qui permet aussi de coller une grille formatee en 9 lignes.
    Retourne None si l'entree ne fait pas exactement 81 cases valides.
    """
    if not isinstance(text, str):
        return None
    compact = "".join(ch for ch in text if ch not in " \n\r\t")
    if len(compact) != 81:
        return None
    grille: List[List[int]] = []
    for r in range(9):
        ligne: List[int] = []
        for c in range(9):
            ch = compact[9 * r + c]
            if ch in ".0":
                ligne.append(0)
            elif "1" <= ch <= "9":
                ligne.append(int(ch))
            else:
                return None
        grille.append(ligne)
    return grille


def solve_grid(grille: List[List[int]]) -> Optional[List[List[int]]]:
    """Resout une grille de Sudoku 9x9 (0 = case vide) avec Z3.

    Reprise fidele du carnet phare : domaine 1-9, indices figes, unicite par
    ligne / colonne / bloc 3x3.

    Returns:
        Grille 9x9 resolue, ou None si insatisfiable.
    """
    solveur = Solver()
    cellules = [[Int(f"c_{r}_{c}") for c in range(9)] for r in range(9)]

    # Domaine : 1 <= cellule <= 9
    for r in range(9):
        for c in range(9):
            solveur.add(cellules[r][c] >= 1, cellules[r][c] <= 9)
    # Indices donnes : figer les cases pre-remplies
    for r in range(9):
        for c in range(9):
            if grille[r][c] != 0:
                solveur.add(cellules[r][c] == grille[r][c])
    # Unicite par ligne
    for r in range(9):
        solveur.add(Distinct([cellules[r][c] for c in range(9)]))
    # Unicite par colonne
    for c in range(9):
        solveur.add(Distinct([cellules[r][c] for r in range(9)]))
    # Unicite par bloc 3x3
    for br in range(3):
        for bc in range(3):
            bloc = [cellules[3 * br + i][3 * bc + j] for i in range(3) for j in range(3)]
            solveur.add(Distinct(bloc))

    if solveur.check() == sat:
        modele = solveur.model()
        return [[modele[cellules[r][c]].as_long() for c in range(9)] for r in range(9)]
    return None


def solve_request(text: object) -> dict:
    """Contrat REST : parse + resout, rend le dictionnaire de reponse.

    Le statut ``invalid`` couvre toute entree qui n'est pas 81 cases valides ;
    ``unsat`` couvre un puzzle contradictoire (indices incompatibles).
    """
    debut = time.perf_counter()
    grille = parse_puzzle(text)
    if grille is None:
        return {
            "status": "invalid",
            "solution": None,
            "time_ms": round((time.perf_counter() - debut) * 1000.0, 3),
        }
    solution = solve_grid(grille)
    temps = round((time.perf_counter() - debut) * 1000.0, 3)
    if solution is None:
        return {"status": "unsat", "solution": None, "time_ms": temps}
    return {
        "status": "sat",
        "solution": "".join(str(v) for ligne in solution for v in ligne),
        "time_ms": temps,
    }