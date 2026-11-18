#!/usr/bin/env python3
"""Tests pour scripts/sudoku/core/corpus.py — l'audit mesure du corpus de
puzzles de la serie Sudoku.

Couvre :
- `parse_puzzle` : les deux notations du corpus (`0` et `.`), et ses deux
  erreurs (longueur, caractere) ;
- `load_corpus` : lecture d'un fichier de corpus, erreur de ligne nommee ;
- `count_solutions` : unicite (1) contre pluralite (2) — la distinction qui
  manque si l'on se contente de « une solution trouvee » ;
- `search_effort` / `propagation_only` : 0 decision = propagation seule ;
- `minimal_clue_set` : le sous-ensemble rendu determine **la meme** solution
  unique, et il est irredondant ;
- `audit_all` : l'invariant du corpus — chaque grille est valide et unique, et
  la hierarchie de difficulte annoncee par les noms de fichiers tient
  (propagation seule de plus en plus rare, effort de recherche de plus en plus
  grand). Si l'invariant cesse de tenir, le test **refute** la hierarchie au
  lieu de la laisser implicite.

Import direct par chemin (sys.path.insert sur core/) pour contourner le
core/__init__.py qui force-importe torch : ces tests restent numpy-only et
hermetiques.
"""

import sys
from pathlib import Path

import numpy as np
import pytest

HERE = Path(__file__).resolve().parent
CORE_DIR = HERE.parent / "core"
sys.path.insert(0, str(CORE_DIR))

import corpus  # noqa: E402  (numpy-only, __init__.py torch chain bypassed)

np = pytest.importorskip("numpy")


# --------------------------------------------------------------------------
# Grilles de reference
# --------------------------------------------------------------------------

# Grille complete resolue (solution canonique de reference).
SOLVED = np.array(
    [
        5, 3, 4, 6, 7, 8, 9, 1, 2,
        6, 7, 2, 1, 9, 5, 3, 4, 8,
        1, 9, 8, 3, 4, 2, 5, 6, 7,
        8, 5, 9, 7, 6, 1, 4, 2, 3,
        4, 2, 6, 8, 5, 3, 7, 9, 1,
        7, 1, 3, 9, 2, 4, 8, 5, 6,
        9, 6, 1, 5, 3, 7, 2, 8, 4,
        2, 8, 7, 4, 1, 9, 6, 3, 5,
        3, 4, 5, 2, 8, 6, 1, 7, 9,
    ],
    dtype=np.int64,
)

# Grille vide : plusieurs solutions, et une decision de backtracking.
EMPTY = np.zeros(81, dtype=np.int64)

# Grille contradictoire : deux 5 sur la premiere ligne, donc aucune solution.
CONTRADICTORY = EMPTY.copy()
CONTRADICTORY[0] = 5
CONTRADICTORY[1] = 5


def _first_corpus_puzzle():
    """Premiere grille du corpus Easy51 (verifiee unique par l'audit)."""
    return corpus.load_corpus(corpus.PUZZLE_DIR / corpus.CORPUS_FILES[0])[0]


# --------------------------------------------------------------------------
# Parsing
# --------------------------------------------------------------------------

def test_parse_puzzle_accepte_les_deux_notations():
    zeros = "0" * 81
    dots = "." * 81
    assert np.array_equal(corpus.parse_puzzle(zeros), np.zeros(81, dtype=np.int64))
    assert np.array_equal(corpus.parse_puzzle(dots), np.zeros(81, dtype=np.int64))


def test_parse_puzzle_lit_les_chiffres():
    line = "5" + "." * 80
    grid = corpus.parse_puzzle(line)
    assert grid[0] == 5
    assert grid[1] == 0


def test_parse_puzzle_refuse_une_mauvaise_longueur():
    with pytest.raises(ValueError, match="81 caracteres"):
        corpus.parse_puzzle("0" * 80)


def test_parse_puzzle_refuse_un_caractere_invalide():
    line = "x" + "." * 80
    with pytest.raises(ValueError, match="caractere invalide"):
        corpus.parse_puzzle(line)


def test_load_corpus_nomme_le_fichier_et_la_ligne(tmp_path):
    source = tmp_path / "corps.txt"
    source.write_text("." * 81 + "\n" + "court\n", encoding="utf-8")
    with pytest.raises(ValueError, match=r"corps\.txt:2"):
        corpus.load_corpus(source)


def test_load_corpus_ignore_les_lignes_vides(tmp_path):
    source = tmp_path / "corps.txt"
    source.write_text("\n" + "." * 81 + "\n\n", encoding="utf-8")
    assert len(corpus.load_corpus(source)) == 1


# --------------------------------------------------------------------------
# Denombrement et mesure
# --------------------------------------------------------------------------

def test_count_solutions_unique_et_pluriel():
    assert corpus.count_solutions(SOLVED, 2) == 1
    assert corpus.count_solutions(EMPTY, 2) == 2


def test_count_solutions_plafonne_au_seuil():
    # La grille vide a plusieurs solutions : un seuil de 1 sature a 1.
    assert corpus.count_solutions(EMPTY, 1) == 1


def test_count_solutions_refuse_un_seuil_invalide():
    with pytest.raises(ValueError, match="au moins 1"):
        corpus.count_solutions(SOLVED, 0)


def test_count_solutions_detecte_une_contradiction():
    assert corpus.count_solutions(CONTRADICTORY, 2) == 0


def test_search_effort_nul_sur_une_grille_deja_resolue():
    assert corpus.search_effort(SOLVED) == 0
    assert corpus.propagation_only(SOLVED)


def test_search_effort_positif_ou_inconnu():
    # La grille vide demande des decisions de backtracking.
    assert corpus.search_effort(EMPTY) > 0
    assert not corpus.propagation_only(EMPTY)
    # Une contradiction : aucune solution, donc aucune decision possible.
    assert corpus.search_effort(CONTRADICTORY) == -1


def test_minimal_clue_set_determine_la_meme_solution():
    puzzle = _first_corpus_puzzle()
    solution = corpus.solve_sudoku(puzzle)
    reduced, retired = corpus.minimal_clue_set(puzzle)
    assert retired, "la reduction doit retirer des indices"
    assert (reduced != 0).sum() < (puzzle != 0).sum()
    assert corpus.count_solutions(reduced, 2) == 1
    assert np.array_equal(corpus.solve_sudoku(reduced), solution)


def test_minimal_clue_set_refuse_une_grille_non_unique():
    with pytest.raises(ValueError, match="plusieurs solutions"):
        corpus.minimal_clue_set(EMPTY)


# --------------------------------------------------------------------------
# Audit du corpus
# --------------------------------------------------------------------------

def test_audit_puzzle_rend_les_mesures_de_base():
    record = corpus.audit_puzzle(SOLVED)
    assert record["clues"] == 81
    assert record["valid"]
    assert record["solutions"] == 1
    assert record["propagation_only"]


def test_audit_corpus_signale_les_grilles_non_uniques(tmp_path):
    source = tmp_path / "corps.txt"
    source.write_text("." * 81 + "\n" + "0" * 81 + "\n", encoding="utf-8")
    audit = corpus.audit_corpus(source)
    assert audit["count"] == 2
    assert audit["not_unique"] == [1, 2]
    assert audit["unsolved"] == []


def test_audit_corpus_signale_les_grilles_sans_solution(tmp_path):
    source = tmp_path / "corps.txt"
    source.write_text("55" + "." * 79 + "\n", encoding="utf-8")
    audit = corpus.audit_corpus(source)
    assert audit["invalid"] == [1]
    assert audit["unsolved"] == [1]


def test_audit_all_certifie_le_corpus_de_la_serie():
    audits = corpus.audit_all()
    assert set(audits) == set(corpus.CORPUS_FILES)
    for audit in audits.values():
        assert audit["count"] > 0
        assert audit["invalid"] == []
        assert audit["not_unique"] == []
        assert audit["unsolved"] == []


def test_invariant_hierarchie_de_difficulte():
    """La hierarchie annoncee par les noms de fichiers doit tenir.

    Les trois corpus sont nommes par difficulte croissante (`Easy51`,
    `hardest`, `top95`). Ce test refute cette hierarchie si elle cesse de
    tenir : la part de grilles resolues par propagation seule decroit, et
    l'effort de recherche maximal croît.
    """
    audits = corpus.audit_all()
    order = list(corpus.CORPUS_FILES)
    propagation = [audits[name]["propagation_only"] / audits[name]["count"] for name in order]
    effort = [audits[name]["max_decisions"] for name in order]

    assert propagation[0] >= propagation[-1], (
        f"la part de grilles resolues par propagation seule doit decroitre : {propagation}"
    )
    assert effort[0] <= effort[-1], (
        f"l'effort de recherche maximal doit croitre avec la difficulte : {effort}"
    )


def test_format_summary_ne_leve_pas():
    summary = corpus.format_summary(corpus.audit_all())
    assert "Sudoku_Easy51.txt" in summary
    assert "propagation" in summary


def test_corpus_top95_est_integralement_irredondant():
    """Chaque puzzle de `top95` est irredondant : aucun indice n'est superflu.

    C'est la propriete la plus distinctive du corpus de la serie -- elle
    distingue structurellement `top95` de `Easy51`, ou presque toutes les
    grilles portent des indices redondants. Le test refute la propriete si
    elle cesse de tenir.
    """
    puzzles = corpus.load_corpus(corpus.PUZZLE_DIR / "Sudoku_top95.txt")
    removable = [
        index
        for index, puzzle in enumerate(puzzles)
        if corpus.minimal_clue_set(puzzle)[1]
    ]
    assert not removable, f"puzzles de top95 devenus redondants : {removable}"


def test_corpus_easy51_admet_des_indices_redondants():
    """La plupart des grilles de `Easy51` portent des indices superflus.

    Symetrique du test precedent : le corpus « facile » et le corpus
    « difficile » ne se distinguent pas seulement par l'effort de recherche,
    mais par la **redondance** de leurs indices.
    """
    puzzles = corpus.load_corpus(corpus.PUZZLE_DIR / corpus.CORPUS_FILES[0])
    with_redundancy = sum(1 for puzzle in puzzles if corpus.minimal_clue_set(puzzle)[1])
    assert with_redundancy >= len(puzzles) // 2, (
        f"seules {with_redundancy} grilles de Easy51 sur {len(puzzles)} "
        "portent des indices redondants"
    )
