"""
Tests for Sudoku/dlx_certificates.py.

Couvre les criteres d'acceptation de l'issue #22375 :

  1. Extraction *fidele* du moteur DLX natif -- equivalence avec le moteur
     du notebook (cellules qui definissent les classes), sur les grilles
     que le notebook manipule deja.
  2. Format de certificat versionne + validation par etages -- les cinq
     controles negatifs, chacun rejete a l'etage attendu.
  3. Corpus de denombrement 4x4 (cas 0 / 1 / >=2 solutions) confronte a une
     enumeration independante, avec le statut d'arret (exhausted /
     limit_reached) distinct du denombrement.
  4. Forme de l'export Lean / JSON.

Pas d'erreur volontaire (regle C.1) : les controles negatifs construisent
des certificats *mauvais* en partant d'un certificat *bon*, jamais de code
qui leve.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

# Le module vit a la racine de la serie Sudoku ; les tests dans tests/.
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from dlx_certificates import (  # noqa: E402
    CERTIFICATE_VERSION,
    DLXSudokuSolver,
    RejectionStage,
    StopStatus,
    SudokuGrid,
    certificate_to_json,
    certificate_to_lean,
    clues_from_puzzle,
    enumerate_4x4_independent,
    solve_4x4_all,
    solve_certificate,
    validate_certificate,
)

# Grille canonique 81 caracteres, celle que Sudoku-02-DancingLinks-Python.ipynb
# resout deja.
NB_PUZZLE = (
    "530070000600195000098000060800060003400803001700020006060000280000419005000080079"
)
NB_PUZZLE_BLANK = "0" * 81

# Classes que le moteur DLX expose -- selection des cellules a executer.
_ENGINE_MARKERS = (
    "class DancingLinksNode",
    "class ColumnHeader",
    "class DancingLinks",
    "class SudokuGrid",
    "class DLXSudokuSolver",
)


# ---------------------------------------------------------------------------
# 1. Extraction fidele : equivalence avec le moteur du notebook
# ---------------------------------------------------------------------------

def _load_notebook_engine() -> dict:
    """Exec seulement les cellules qui definissent les classes du moteur.

    Executer l'integralite du notebook declencherait aussi les cellules de
    demonstration (resolution + affichage) ; on ne veut que l'organe a
    comparer. La selection par marqueur `class ...` est robuste a la
    renumeroitation des cellules.
    """
    nb_path = (
        Path(__file__).resolve().parents[1]
        / "Sudoku-02-DancingLinks-Python.ipynb"
    )
    nb = json.loads(nb_path.read_text(encoding="utf-8"))
    code = []
    for c in nb["cells"]:
        if c["cell_type"] != "code":
            continue
        src = "".join(c.get("source", []))
        if any(m in src for m in _ENGINE_MARKERS):
            code.append(src)
    ns: dict = {}
    exec("\n\n".join(code), ns)  # noqa: S102 -- code du notebook de reference
    return ns


@pytest.fixture(scope="module")
def notebook_ns() -> dict:
    return _load_notebook_engine()


@pytest.mark.parametrize(
    "puzzle",
    [
        # Grille canonique 81 caracteres, celle que Sudoku-02 resout deja.
        # Les grilles quasi-vides (vide, un seul indice, premiere ligne remplie)
        # ne sont PAS comparees ici : `solve()` appelle `search(find_all=True)`
        # et la ramification MRV y est pathologique -- 6,67 milliards de
        # solutions sur la grille vide, toutes les 324 colonnes liees a la meme
        # taille -- si le solveur n'aboutit pas en temps borne. L'equivalence
        # se mesure sur la grille que le notebook manipule reellement.
        NB_PUZZLE,
    ],
)
def test_engine_equivalence(notebook_ns: dict, puzzle: str) -> None:
    """Le moteur extrait dans le module resout exactement comme le notebook."""
    nb_solver = notebook_ns["DLXSudokuSolver"]()
    nb_out = nb_solver.solve(notebook_ns["SudokuGrid"].from_string(puzzle))

    my_solver = DLXSudokuSolver()
    my_out = my_solver.solve(SudokuGrid.from_string(puzzle))

    if nb_out is None:
        assert my_out is None
        return
    assert my_out is not None
    assert my_out.cells == nb_out.cells


def test_build_matrix_exposes_row_info() -> None:
    """La correspondance ligne -> placement est exposee (et non locale)."""
    solver = DLXSudokuSolver()
    dlx, row_info = solver._build_matrix(SudokuGrid.from_string(NB_PUZZLE))
    # 30 cellules pre-remplies -> 1 ligne chacune ; 51 vides -> 9 chacune.
    assert len(row_info) == 30 * 1 + 51 * 9
    assert dlx is not None


# ---------------------------------------------------------------------------
# 2. Certificat : aller-retour + conventions
# ---------------------------------------------------------------------------

def test_certificate_round_trip() -> None:
    res = solve_certificate(NB_PUZZLE)
    assert res is not None
    assert res.status == StopStatus.EXHAUSTED
    assert len(res.placements) == 81
    assert res.version == CERTIFICATE_VERSION
    # Reconstruire la grille depuis les placements -> solution valide.
    grid = SudokuGrid()
    for cell, val in res.placements:
        grid.cells[cell // 9][cell % 9] = val + 1
    assert grid.is_valid()


def test_clues_from_puzzle() -> None:
    clues = clues_from_puzzle(NB_PUZZLE)
    assert len(clues) == 30
    assert clues == sorted(clues)
    # La premiere case (5) -> (0, 4) en convention value = v - 1.
    assert clues[0] == (0, 4)


def test_validate_accepts_good_certificate() -> None:
    res = solve_certificate(NB_PUZZLE)
    v = validate_certificate(NB_PUZZLE, res.placements)
    assert v.accepted
    assert v.stage is None


def _good_placements() -> list:
    return solve_certificate(NB_PUZZLE).placements


# ---------------------------------------------------------------------------
# 3. Cinq controles negatifs, chacun rejete a l'etage attendu
# ---------------------------------------------------------------------------

def test_negative_missing_placement() -> None:
    placements = _good_placements()[:-1]  # une case manquante
    v = validate_certificate(NB_PUZZLE, placements)
    assert not v.accepted
    assert v.stage == RejectionStage.COMPLETENESS


def test_negative_raw_duplicate() -> None:
    placements = list(_good_placements())
    placements.append(placements[0])  # paire exacte repetee
    v = validate_certificate(NB_PUZZLE, placements)
    assert not v.accepted
    assert v.stage == RejectionStage.RAW_DUPLICATE


def test_negative_cell_conflict() -> None:
    placements = list(_good_placements())
    cell = placements[0][0]
    # Deuxieme valeur pour la meme cellule -> conflit de cellule.
    placements[1] = (cell, (placements[1][1] + 1) % 9)
    v = validate_certificate(NB_PUZZLE, placements)
    assert not v.accepted
    assert v.stage == RejectionStage.CELL_CONFLICT


def test_negative_domain_out_of_range() -> None:
    placements = list(_good_placements())
    placements[0] = (0, 9)  # valeur 9 hors domaine [0, 8]
    v = validate_certificate(NB_PUZZLE, placements)
    assert not v.accepted
    assert v.stage == RejectionStage.DOMAIN


def test_negative_latin_valid_bad_blocks() -> None:
    """Carré latin d'ordre 9 (lignes et colonnes valides) mais blocs cassés.

    Le carrelage cyclique `L[r][c] = (r + c) mod 9` est un carre latin :
    chaque ligne et chaque colonne est une permutation de [0, 8]. Les blocs
    3x3, eux, ne le sont pas. Le rejet doit donc tomber a l'etage
    EXACT_COVER (portee bloc), apres que lignes et colonnes ont passe.
    """
    placements = sorted(
        (r * 9 + c, (r + c) % 9) for r in range(9) for c in range(9)
    )
    v = validate_certificate(NB_PUZZLE_BLANK, placements)
    assert not v.accepted
    assert v.stage == RejectionStage.EXACT_COVER


def test_negative_other_puzzle_clues() -> None:
    """Solution correcte confrontee a un puzzle dont un indice est modifie.

    Deterministe : on prend la solution du puzzle, on altere un seul de ses
    indices, et la (bonne) solution viole precisement cet indice -> CLUES.
    """
    sol = solve_certificate(NB_PUZZLE)
    puzzle = list(NB_PUZZLE)
    clue_cell = next(i for i, ch in enumerate(puzzle) if ch != "0")
    puzzle[clue_cell] = str(int(puzzle[clue_cell]) % 9 + 1)
    v = validate_certificate("".join(puzzle), sol.placements)
    assert not v.accepted
    assert v.stage == RejectionStage.CLUES


# ---------------------------------------------------------------------------
# 4. Corpus 4x4 : DLX vs enumeration independante, statut d'arret
# ---------------------------------------------------------------------------

def test_4x4_unique() -> None:
    p = "1234341243212143"
    ds, st = solve_4x4_all(p)
    i = enumerate_4x4_independent(p)
    assert st == StopStatus.EXHAUSTED
    assert len(ds) == 1
    assert sorted(ds) == sorted(i)


def test_4x4_zero() -> None:
    p = "1134341243212143"  # deux 1 dans la meme case de depart
    ds, st = solve_4x4_all(p)
    i = enumerate_4x4_independent(p)
    assert st == StopStatus.EXHAUSTED
    assert ds == []
    assert i == []


def test_4x4_multi_subset_and_canonical_count() -> None:
    """Grille vide 4x4 : 288 solutions (nombre canonique), DLX coupe a 100.

    L'arret sur limite ne permet pas de comparer les ensembles : on verifie
    l'inclusion (les 100 trouvees par DLX sont parmi les 288) et le compte
    exact de l'enumeration independante.
    """
    p = "." * 16
    ds, st = solve_4x4_all(p, limit=100)
    i = enumerate_4x4_independent(p)
    assert st == StopStatus.LIMIT_REACHED
    assert len(ds) == 100
    assert len(i) == 288
    assert set(map(tuple, ds)) <= set(map(tuple, i))


def test_4x4_exactly_two() -> None:
    """Intercale sur les lignes 0-1 (colonnes 0 et 2) -> exactement 2 solutions.

    Supprimer les quatre cases (0,0) (0,2) (1,0) (1,2) d'une grille complete
    laisse l'echange de l'intercale comme seule seconde solution : les deux
    organes doivent s'accorder sur le compte, et l'arret est naturel.
    """
    p = list("1234341243212143")
    for pos in (0, 2, 4, 6):
        p[pos] = "."
    p = "".join(p)
    ds, st = solve_4x4_all(p, limit=100)
    i = enumerate_4x4_independent(p)
    assert st == StopStatus.EXHAUSTED
    assert len(ds) == 2
    assert sorted(map(tuple, ds)) == sorted(map(tuple, i))


# ---------------------------------------------------------------------------
# 5. Forme de l'export Lean / JSON
# ---------------------------------------------------------------------------

def test_certificate_to_lean_shape() -> None:
    res = solve_certificate(NB_PUZZLE)
    text = certificate_to_lean(res, name="nbCertificate")
    assert "import Sudoku.Certificate" in text
    assert "namespace Sudoku.Certificate" in text
    assert "def nbCertificate : RawCertificate (Fin 81) (Fin 9) where" in text
    assert 'puzzle := "530070000600195000098000060800060003400803001700020006060000280000419005000080079"' in text
    assert "checkCertificate nbCertificate sudokuScopes = .ok := by decide" in text
    # 81 placements emis.
    assert text.count("(0, ") >= 1  # au moins la case 0
    assert "placements :=" in text


def test_certificate_to_json_round_trip() -> None:
    res = solve_certificate(NB_PUZZLE)
    data = json.loads(certificate_to_json(res))
    assert data["version"] == CERTIFICATE_VERSION
    assert data["puzzle"] == NB_PUZZLE
    assert data["status"] == StopStatus.EXHAUSTED
    assert len(data["placements"]) == 81
    assert len(data["clues"]) == 30
    assert data["conventions"]["value"].startswith("v - 1")
