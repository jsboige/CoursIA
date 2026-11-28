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


# ---------------------------------------------------------------------------
# 5. Lot 2 (#27533) : tuples nus/caches d'ordre 2 a 4 + candidats verrouilles
#
# Les motifs sont sculptes sur une grille vide a candidats pleins (les tests
# visent la logique du chercheur, independamment de l'ordre de resolution) ;
# la garde oracle sur le corpus reel est le test d'integration du lot.
# ---------------------------------------------------------------------------


def _blank_solver() -> InferenceSolver:
    """Solveur sur grille vide a candidats pleins, pour sculpter des motifs."""
    solver = InferenceSolver(EASY)
    solver.grid = [[0] * 9 for _ in range(9)]
    solver.cands = [[set(range(1, 10)) for _ in range(9)] for _ in range(9)]
    return solver


def test_naked_triple_eliminates_union_from_other_cells():
    solver = _blank_solver()
    solver.cands[0][0] = {1, 2, 3}
    solver.cands[0][1] = {1, 2}
    solver.cands[0][2] = {2, 3}
    solver.cands[0][4] = {1, 9}
    step = solver._naked_triple()
    assert step is not None and step.rule == "naked_triple"
    assert (0, 4, 1) in step.eliminations
    assert (0, 4, 9) not in step.eliminations
    assert 9 in solver.cands[0][4], "9 hors du tuple reste candidat"


def test_naked_triple_silent_when_union_exceeds_n():
    solver = _blank_solver()
    solver.cands[0][0] = {1, 2, 3}
    solver.cands[0][1] = {1, 2}
    solver.cands[0][2] = {3, 4}  # union {1,2,3,4} : ordre 4, pas 3
    assert solver._naked_triple() is None


def test_naked_tuple_ignores_single_candidate_cells():
    """Invariant d'ordre documente : dans la boucle, ``naked_single`` passe
    toujours avant les tuples (RULE_ORDER + reprise au sommet), donc aucune
    case a candidat unique ne devrait exister au scan. Ce test negatif prouve
    que la correction ne DEPEND pas de cet ordre : appelee hors ordre, la
    regle exclut structurellement les cases a candidat unique (filtre
    ``2 <= len(cands) <= n``) et ne les touche pas."""
    solver = _blank_solver()
    solver.cands[0][0] = {5}  # candidat unique en attente (single non joue)
    solver.cands[0][1] = {1, 2, 3}
    solver.cands[0][2] = {1, 2}
    solver.cands[0][3] = {2, 3}
    solver.cands[0][4] = {1, 9}
    step = solver._naked_triple()
    # le tuple {(0,1),(0,2),(0,3)} est trouve malgre la case a candidat unique
    assert step is not None and step.rule == "naked_triple"
    assert (0, 4, 1) in step.eliminations
    # la case a candidat unique n'est ni membre ni cible : son candidat survit
    assert solver.cands[0][0] == {5}
    assert all((0, 0, v) not in step.eliminations for v in range(1, 10))


def test_naked_quad_eliminates_union_from_other_cells():
    solver = _blank_solver()
    solver.cands[0][0] = {1, 2, 3, 4}
    solver.cands[0][1] = {1, 2}
    solver.cands[0][2] = {3, 4}
    solver.cands[0][3] = {2, 3}
    solver.cands[0][5] = {4, 9}
    step = solver._naked_quad()
    assert step is not None and step.rule == "naked_quad"
    assert (0, 5, 4) in step.eliminations
    assert (0, 5, 9) not in step.eliminations


def test_hidden_pair_confines_two_digits_to_two_cells():
    solver = _blank_solver()
    # dans la ligne 0, les valeurs 7 et 8 ne peuvent aller qu'en (0,0)/(0,1)
    for c in range(9):
        for v in (7, 8):
            solver.cands[0][c].discard(v)
    solver.cands[0][0] |= {7, 8}
    solver.cands[0][1] |= {7, 8}
    step = solver._hidden_pair()
    assert step is not None and step.rule == "hidden_pair"
    # tout autre candidat des deux cases est elimine
    assert solver.cands[0][0] == {7, 8}
    assert solver.cands[0][1] == {7, 8}


def test_hidden_pair_silent_when_digits_escape_the_two_cells():
    solver = _blank_solver()
    for c in range(9):
        for v in (7, 8):
            solver.cands[0][c].discard(v)
    solver.cands[0][0] |= {7, 8}
    solver.cands[0][1] |= {7}
    solver.cands[0][2] |= {8}  # union de 3 cases : pas une paire cachee
    assert solver._hidden_pair() is None
    assert 8 in solver.cands[0][2], "aucune elimination ne doit survenir"


def test_hidden_triple_removes_outsider_candidates():
    solver = _blank_solver()
    for c in range(9):
        for v in (7, 8, 9):
            solver.cands[0][c].discard(v)
    solver.cands[0][0] |= {7}
    solver.cands[0][1] |= {8}
    solver.cands[0][2] |= {7, 8, 9}
    step = solver._hidden_triple()
    assert step is not None and step.rule == "hidden_triple"
    assert solver.cands[0][0] == {7}
    assert solver.cands[0][1] == {8}
    assert solver.cands[0][2] == {7, 8, 9}


def test_hidden_quad_removes_outsider_candidates():
    solver = _blank_solver()
    for c in range(9):
        for v in (6, 7, 8, 9):
            solver.cands[0][c].discard(v)
    solver.cands[0][0] |= {6, 7}
    solver.cands[0][1] |= {8}
    solver.cands[0][2] |= {6, 9}
    solver.cands[0][3] |= {7, 8, 9}
    step = solver._hidden_quad()
    assert step is not None and step.rule == "hidden_quad"
    assert solver.cands[0][0] == {6, 7}
    assert solver.cands[0][1] == {8}
    assert solver.cands[0][2] == {6, 9}
    assert solver.cands[0][3] == {7, 8, 9}


def test_locked_claiming_removes_value_from_rest_of_block():
    solver = _blank_solver()
    # valeur 5 de la colonne 0 confinee au bloc (0,0)
    for r in range(9):
        solver.cands[r][0].discard(5)
    solver.cands[0][0] |= {5}
    solver.cands[1][0] |= {5}
    step = solver._locked_claiming()
    assert step is not None and step.rule == "locked_claiming"
    for (r, c) in [(0, 1), (0, 2), (1, 1), (1, 2), (2, 1), (2, 2)]:
        assert (r, c, 5) in step.eliminations, f"5 doit partir de ({r},{c})"
    assert 5 not in solver.cands[2][2]
    assert 5 in solver.cands[0][0] and 5 in solver.cands[1][0]


def test_locked_claiming_silent_when_spans_two_blocks():
    solver = _blank_solver()
    # valeur 5 de la ligne 0 presente dans deux blocs differents
    for c in range(9):
        solver.cands[0][c].discard(5)
    solver.cands[0][0] |= {5}
    solver.cands[0][4] |= {5}
    assert solver._locked_claiming() is None
    assert 5 in solver.cands[2][2], "aucune elimination ne doit survenir"


# ---------------------------------------------------------------------------
# Lot 3 (#27533) : fish d'ordre 3 et 4 -- swordfish, jellyfish
# ---------------------------------------------------------------------------


def _keep_only(solver: InferenceSolver, v: int, cells: list[tuple[int, int]]):
    """Sculpte le motif : v n'est candidat QUE dans ``cells``."""
    for r in range(9):
        for c in range(9):
            solver.cands[r][c].discard(v)
    for (r, c) in cells:
        solver.cands[r][c].add(v)


def test_swordfish_eliminates_from_cover_columns():
    solver = _blank_solver()
    # v=5 : base lignes {0,3,6}, positions confinees aux colonnes {1,4,7} ;
    # les cibles (une par ligne hors base, 1 position -> jamais base) portent
    # le candidat que le fish doit eliminer.
    _keep_only(solver, 5, [(0, 1), (0, 4),
                           (3, 4), (3, 7),
                           (6, 1), (6, 7)])
    for (r, c) in [(1, 1), (2, 1), (5, 7), (8, 4)]:
        solver.cands[r][c].add(5)
    step = solver._swordfish()
    assert step is not None and step.rule == "swordfish"
    for (r, c) in [(1, 1), (2, 1), (5, 7), (8, 4)]:
        assert (r, c, 5) in step.eliminations, f"5 doit partir de ({r},{c})"
    # les 6 positions de base survivent
    for (r, c) in [(0, 1), (0, 4), (3, 4), (3, 7), (6, 1), (6, 7)]:
        assert 5 in solver.cands[r][c]


def test_swordfish_silent_when_cover_spans_four_columns():
    solver = _blank_solver()
    # couverture de 4 colonnes {1,4,7,8} : pas un fish d'ordre 3
    _keep_only(solver, 5, [(0, 1), (0, 4),
                           (3, 4), (3, 7),
                           (6, 1), (6, 8)])
    solver.cands[1][1].add(5)  # cible potentielle : ne doit pas etre touchee
    assert solver._swordfish() is None
    assert 5 in solver.cands[1][1], "aucune elimination ne doit survenir"


def test_swordfish_base_columns_orientation():
    solver = _blank_solver()
    # v=6 : base colonnes {0,3,6} confinee aux lignes {2,5,8} ; la ligne 2
    # porte en outre (2,1),(2,2) hors couverture -> 4 positions, elle ne peut
    # pas etre une base LIGNE : seul le fish base colonnes peut tirer.
    _keep_only(solver, 6, [(2, 0), (5, 0),
                           (2, 3), (8, 3),
                           (5, 6), (8, 6),
                           (2, 1), (2, 2)])
    step = solver._swordfish()
    assert step is not None and step.rule == "swordfish"
    assert sorted(step.eliminations) == [(2, 1, 6), (2, 2, 6)]


def test_jellyfish_eliminates_from_cover_columns():
    solver = _blank_solver()
    # v=7 : base lignes {0,2,4,6}, couverture colonnes {1,3,5,7} ; aucun
    # sous-ensemble de 3 lignes ne couvre exactement 3 colonnes (chaque
    # triplet en couvre 4) : motif jellyfish pur, pas un swordfish deguise.
    _keep_only(solver, 7, [(0, 1), (0, 3),
                           (2, 3), (2, 5),
                           (4, 5), (4, 7),
                           (6, 1), (6, 7)])
    for (r, c) in [(1, 1), (3, 3), (5, 5), (7, 7)]:
        solver.cands[r][c].add(7)
    step = solver._jellyfish()
    assert step is not None and step.rule == "jellyfish"
    for (r, c) in [(1, 1), (3, 3), (5, 5), (7, 7)]:
        assert (r, c, 7) in step.eliminations, f"7 doit partir de ({r},{c})"
    for (r, c) in [(0, 1), (2, 5), (6, 7)]:
        assert 7 in solver.cands[r][c]


def test_fish_ignores_units_with_single_position():
    """Invariant d'ordre documente : dans la boucle, ``hidden_single``
    consomme une unite a position unique avant ce scan. Ce temoin negatif
    prouve que la correction ne DEPEND pas de cet ordre : appelee hors
    ordre, la regle exclut structurellement les unites a position unique
    du filtre ``2 <= len(spots) <= n`` -- la ligne 0 a 1 position de 8,
    elle ne peut pas completer la base {0,3,6} (cover {1,4,7})."""
    solver = _blank_solver()
    _keep_only(solver, 8, [(0, 1),            # ligne 0 : 1 position
                           (3, 1), (3, 4),
                           (6, 4), (6, 7)])
    solver.cands[1][7].add(8)  # cible potentielle : ne doit pas etre touchee
    assert solver._swordfish() is None
    assert 8 in solver.cands[1][7], "aucune elimination ne doit survenir"


def test_lot2_corpus_all_accepted_and_progress_measured():
    """Garde d'integration du lot 2 : toutes les traces du corpus restent
    acceptees par l'oracle, les nouvelles regles tirent, et la couverture
    moyenne progresse (4/10 a l'organe a 5 regles, mesure #27533 lot 2)."""
    fired: set = set()
    for name in ("Sudoku_gen_moyen.txt", "Sudoku_gen_difficile.txt"):
        rows = measure_coverage(_load(name, 10))
        assert all(r.trace_accepted for r in rows), (
            f"{name} : etape(s) invalide(s) apres le lot 2")
        for r in rows:
            fired |= set(r.rules_used)
    assert {"naked_triple", "locked_claiming"} <= fired, (
        "les regles du lot 2 doivent tirer sur le corpus moyen/difficile")
    rows = measure_coverage(_load("Sudoku_gen_moyen.txt", 10))
    solved = sum(r.solved_by_inference for r in rows)
    assert solved >= 5, "couverture moyenne attendue : >= 5/10 apres le lot 2"


def test_lot3_corpus_all_accepted_and_fish_fired():
    """Garde d'integration du lot 3 : toutes les traces du corpus restent
    acceptees par l'oracle (30/30), le jellyfish tire sur la strate difficile
    (grille 0 : 19 -> 21 etapes de stall, mesure #27533 lot 3), et les gardes
    des strates facile/moyen tiennent (sans regression). Le swordfish, onboarded et
    teste par sculptures unitaires, ne tire pas encore sur ces 30 grilles --
    les grilles qui l'exigent vivent au-dela de la frontiere actuelle."""
    fired: set = set()
    for name in ("Sudoku_gen_facile.txt", "Sudoku_gen_moyen.txt",
                 "Sudoku_gen_difficile.txt"):
        rows = measure_coverage(_load(name, 10))
        assert all(r.trace_accepted for r in rows), (
            f"{name} : etape(s) invalide(s) apres le lot 3")
        for r in rows:
            fired |= set(r.rules_used)
    assert "jellyfish" in fired, (
        "le jellyfish du lot 3 doit tirer sur le corpus difficile")
    easy = measure_coverage(_load("Sudoku_gen_facile.txt", 10))
    assert all(r.solved_by_inference for r in easy), "facile : 10/10 attendues"
    medium = measure_coverage(_load("Sudoku_gen_moyen.txt", 10))
    assert sum(r.solved_by_inference for r in medium) >= 5, (
        "couverture moyenne : >= 5/10 (garde du lot 2 preservee)")
