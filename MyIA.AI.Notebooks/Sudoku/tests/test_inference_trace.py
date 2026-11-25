"""Tests for Sudoku/scripts/inference_trace.py (#26242 volet 3).

Couvre les criteres d'acceptation du volet 3 :

  1. Format de trace verifiable : chaque etape (placement / elimination) est
     controlee independamment contre l'oracle exact ``dlx_certificates`` --
     la solution unique du puzzle.
  2. Couverture mesuree par strate sur le corpus certifie #26426, recherche
     desactivee : les grilles resolues ET non resolues sont conservees
     (temoins de la frontiere de l'inference pure).
  3. Temoin negatif (regle organ-first) : une etape qui elimine un candidat
     present dans la solution unique est rejetee par la verification, et
     nommee avec sa raison.
  4. Frontiere « sans gomme » : le solveur instrumente ne fait AUCUNE
     recherche -- une grille non resolue par inference pure est marquee
     ``stalled``, jamais completee par un essai/retour arriere.

Pas d'erreur volontaire (regle C.1) : les controles negatifs construisent des
etapes *fausses* a partir d'une trace *bonne*, jamais du code qui leve.
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

# Le module vit dans Sudoku/scripts/ ; l'oracle a la racine Sudoku/.
_SUDOKU = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(_SUDOKU))
sys.path.insert(0, str(_SUDOKU / "scripts"))

from dlx_certificates import solve_certificate  # noqa: E402
from inference_trace import (  # noqa: E402
    InferenceSolver,
    Step,
    Trace,
    init_candidates,
    measure_coverage,
    parse_grid,
    verify_trace,
)

PUZZLES = _SUDOKU / "Puzzles"


def _load(name: str, n: int | None = None) -> list[str]:
    out = []
    for line in (PUZZLES / name).read_text().splitlines():
        line = line.strip()
        if len(line) >= 81:
            out.append(line[:81])
            if n and len(out) >= n:
                break
    return out


# Grille facile connue : resolue par inference pure seule.
EASY = _load("Sudoku_gen_facile.txt", 1)[0]


def _solution(puzzle: str) -> list[int]:
    cert = solve_certificate(puzzle, find_all=True, limit=2)
    assert cert is not None and cert.solutions_found == 1
    sol = [0] * 81
    for ci, v in cert.placements:
        sol[ci] = v + 1
    return sol


# ---------------------------------------------------------------------------
# 1. Format de trace : structure et etat resultat
# ---------------------------------------------------------------------------


def test_parse_grid_roundtrip():
    grid = parse_grid(EASY)
    assert len(grid) == 9 and all(len(row) == 9 for row in grid)
    # la valeur d'indice 0 de la grille facile est 0 (case vide)
    assert grid[0][0] == 0
    assert grid[0][1] == 8


def test_trace_steps_have_verifiable_shape():
    solver = InferenceSolver(EASY)
    trace = solver.solve()
    assert trace.steps, "une grille facile produit des etapes"
    for k, step in enumerate(trace.steps):
        assert step.index == k
        assert step.rule in InferenceSolver.RULE_ORDER
        assert step.premises
        assert len(step.grid_after) == 81
        # une etape agit : placement ou elimination
        assert step.placements or step.eliminations


def test_easy_grid_solved_by_pure_inference():
    solver = InferenceSolver(EASY)
    trace = solver.solve()
    assert trace.solved and not trace.stalled


# ---------------------------------------------------------------------------
# 2. Verification contre l'oracle : toute trace valide est acceptee
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("name", [
    "Sudoku_gen_facile.txt",
    "Sudoku_gen_moyen.txt",
    "Sudoku_gen_difficile.txt",
])
def test_every_produced_trace_is_oracle_accepted(name):
    for p in _load(name):
        trace = InferenceSolver(p).solve()
        verdict = verify_trace(trace)
        assert verdict.accepted, (
            f"{name}: etape(s) invalide(s) : "
            + "; ".join(v.reason for v in verdict.step_verdicts if not v.ok)
        )


# ---------------------------------------------------------------------------
# 3. Temoin negatif : une elimination fausse est rejetee et nommee
# ---------------------------------------------------------------------------


def _unsolved_by_inference() -> InferenceSolver:
    for p in _load("Sudoku_gen_moyen.txt"):
        s = InferenceSolver(p)
        if not s.solve().solved:
            return s
    pytest.skip("aucune grille moyenne non resolue par inference pure")


def test_negative_witness_bad_elimination_rejected():
    solver = _unsolved_by_inference()
    trace = solver.solve()
    sol = _solution(trace.puzzle)
    # case encore vide : on elimine le BON candidat (invalide)
    target = next((r, c) for r in range(9) for c in range(9)
                  if solver.grid[r][c] == 0)
    r, c = target
    good = sol[r * 9 + c]
    trace.steps.append(Step(len(trace.steps), "naked_pair", "etape fabriquee",
                            eliminations=[(r, c, good)], grid_after=trace.puzzle))
    verdict = verify_trace(trace)
    assert not verdict.accepted
    assert verdict.n_bad == 1
    bad = next(v for v in verdict.step_verdicts if not v.ok)
    assert "solution" in bad.reason and str(good) in bad.reason


def test_negative_witness_bad_placement_rejected():
    solver = _unsolved_by_inference()
    trace = solver.solve()
    sol = _solution(trace.puzzle)
    r, c = next((r, c) for r in range(9) for c in range(9)
                if solver.grid[r][c] == 0)
    good = sol[r * 9 + c]
    wrong = (good % 9) + 1  # une autre valeur
    trace.steps.append(Step(len(trace.steps), "naked_single", "etape fabriquee",
                            placements=[(r, c, wrong)], grid_after=trace.puzzle))
    verdict = verify_trace(trace)
    assert not verdict.accepted
    assert any("contredit la solution" in v.reason
               for v in verdict.step_verdicts if not v.ok)


# ---------------------------------------------------------------------------
# 4. Frontiere « sans gomme » : pas de recherche, stalled conserve
# ---------------------------------------------------------------------------


def test_no_backtracking_unsolved_is_stalled():
    solver = _unsolved_by_inference()
    trace = solver.solve()
    # non resolue par inference pure : marquee stalled, grille incomplete
    assert trace.stalled and not trace.solved
    # la grille reste incomplete (aucune recherche n'a comble les cases)
    assert "0" in trace.steps[-1].grid_after if trace.steps else True


def test_coverage_rows_keep_solved_and_unsolved():
    rows = measure_coverage(_load("Sudoku_gen_moyen.txt"))
    assert len(rows) == 10
    # temoins des deux classes conserves
    solved = [r for r in rows if r.solved_by_inference]
    unsolved = [r for r in rows if not r.solved_by_inference]
    assert solved and unsolved, "la frontiere doit produire les deux classes"
    # toutes les traces sont valides, resolues ou non
    assert all(r.trace_accepted for r in rows)


def test_coverage_by_stratum_is_measured():
    """La frontiere de l'inference pure decroit avec la difficulte (mesure)."""
    easy = measure_coverage(_load("Sudoku_gen_facile.txt"))
    hard = measure_coverage(_load("Sudoku_gen_difficile.txt"))
    easy_rate = sum(r.solved_by_inference for r in easy) / len(easy)
    hard_rate = sum(r.solved_by_inference for r in hard) / len(hard)
    assert easy_rate == 1.0, "facile : entierement resolu par inference pure"
    assert hard_rate < easy_rate, "la couverture chute sur le corpus difficile"
