#!/usr/bin/env python3
"""Tests pour scripts/sudoku/core/dataset.py + models.py — le chargement de
donnees et le one-hot encoding qui alimentent l'entrainement du RRN Sudoku.

Couvre les fonctions a logique pure NON testees par test_core_solvers.py (qui
ne touche que solvers.py + generation.py, numpy-only) :

  - ``parse_81`` : parseur string 81 chars -> array int64 (longueur, non-digit).
  - ``SudokuGraphDataset`` : __len__ / __getitem__ (pass-through int8).
  - ``sudoku_collate_fn`` : LE point critique. One-hot encoding (bs, 81, 10) +
    canal is_given (index 9) + solutions shift -1 (0..8 pour CrossEntropy). Un
    bug ici corromprait silencieusement l'entrainement (mauvais canal allume,
    masque is_given inverse, labels hors [0,8]).
  - ``count_params`` : decompte des parametres entrainables (exclut requires_grad=False).

Import direct par chemin (sys.path.insert sur core/) pour matcher la convention
de test_core_solvers.py. Contrairement a ce dernier, ces tests importent torch
(dataset/models en dependent) — pytest via l'env coursia-ml-training (torch
2.6.0+cu124). CPU-only, <2s.
"""

import sys
from pathlib import Path

import numpy as np
import pytest

torch = pytest.importorskip("torch")  # skip propre si torch absent (CI sans GPU env)

HERE = Path(__file__).resolve().parent
CORE_DIR = HERE.parent / "core"
sys.path.insert(0, str(CORE_DIR))

import dataset  # noqa: E402  (torch needed, __init__.py chain bypassed)
import models  # noqa: E402


# --------------------------------------------------------------------------
# parse_81 — string 81 chars -> int64 array
# --------------------------------------------------------------------------

class TestParse81:
    def test_valid_81_digit_string_to_int64_array(self):
        s = "5" * 10 + "0" * 71  # 81 chars, mix of 5 and 0
        arr = dataset.parse_81(s)
        assert arr.shape == (81,)
        assert arr.dtype == np.int64
        assert arr[0] == 5 and arr[10] == 0

    def test_all_digits_preserved(self):
        s = "123456789" * 9  # 81 chars, every digit repeated
        arr = dataset.parse_81(s)
        assert arr.tolist() == [int(c) for c in s]

    def test_length_agnostic_maps_whatever_chars_given(self):
        # G.9 finding: parse_81 is a thin char->int mapper — it does NOT enforce
        # the 81-char length its name/docstring imply (callers guarantee 81-char
        # rows from the HF dataset). An 80-char string returns an 80-element
        # array, not an error. Documenting the actual behavior; the missing
        # length validation is a minor latent hardening gap (out of scope here:
        # separate code-change concern, not a test-grain).
        assert len(dataset.parse_81("1" * 80)) == 80
        assert len(dataset.parse_81("1" * 82)) == 82

    def test_non_digit_char_raises(self):
        # parse_81 fait int(c) -> un caractere non-digit leve ValueError.
        bad = "1" * 40 + "x" + "1" * 40  # 81 chars avec un 'x'
        with pytest.raises(ValueError):
            dataset.parse_81(bad)


# --------------------------------------------------------------------------
# SudokuGraphDataset — __len__ / __getitem__
# --------------------------------------------------------------------------

class TestSudokuGraphDataset:
    def _toy(self, n=4):
        puzzles = np.zeros((n, 81), dtype=np.int64)
        puzzles[:, 0] = 5  # quelques clues
        solutions = np.ones((n, 81), dtype=np.int64) * 3
        return dataset.SudokuGraphDataset(puzzles, solutions)

    def test_len_matches_input(self):
        ds = self._toy(n=7)
        assert len(ds) == 7

    def test_getitem_returns_puzzle_solution_pair(self):
        ds = self._toy(n=3)
        puzzle, solution = ds[1]
        assert puzzle.shape == (81,)
        assert solution.shape == (81,)
        assert puzzle[0] == 5
        assert solution[0] == 3

    def test_internal_storage_is_int8(self):
        # Le cast int8 (economie memoire pour 1M puzzles) doit etre applique.
        ds = self._toy(n=2)
        assert ds.puzzles.dtype == np.int8
        assert ds.solutions.dtype == np.int8


# --------------------------------------------------------------------------
# sudoku_collate_fn — LE point critique : one-hot + is_given + solutions-1
# --------------------------------------------------------------------------

class TestSudokuCollateFn:
    def test_output_shapes_and_dtypes(self):
        puzzles = np.zeros((4, 81), dtype=np.int8)
        solutions = np.zeros((4, 81), dtype=np.int8)
        batch = list(zip(puzzles, solutions))
        x, sol, is_given = dataset.sudoku_collate_fn(batch)
        assert x.shape == (4, 81, 10)
        assert x.dtype == torch.float32
        assert sol.shape == (4, 81)
        assert sol.dtype == torch.long
        assert is_given.shape == (4, 81)
        assert is_given.dtype == torch.float32

    def test_one_hot_given_cell_value_5_lights_channel_4(self):
        # Une cellule clue de valeur 5 -> canal 4 (index d-1) a 1.0, autres 0,
        # ET le canal is_given (index 9) a 1.0.
        puzzle = np.zeros(81, dtype=np.int8)
        puzzle[0] = 5
        solution = np.zeros(81, dtype=np.int8)
        solution[0] = 5
        x, _, is_given = dataset.sudoku_collate_fn([(puzzle, solution)])
        # canaux chiffre 0..8 (index 0..8 = digits 1..9)
        assert x[0, 0, 4] == 1.0   # digit 5 -> channel 4
        for d in range(8):         # tous les autres canaux-chiffre eteints
            if d != 4:
                assert x[0, 0, d] == 0.0
        assert x[0, 0, 9] == 1.0   # is_given channel
        assert is_given[0, 0] == 1.0

    def test_empty_cell_has_no_digit_and_is_not_given(self):
        # Une cellule vide (0) -> aucun canal-chiffre allume, is_given=0.
        puzzle = np.zeros(81, dtype=np.int8)
        puzzle[0] = 7   # une clue pour distinguer
        solution = np.full(81, 1, dtype=np.int8)
        x, _, is_given = dataset.sudoku_collate_fn([(puzzle, solution)])
        # cellule 1 est vide (puzzle[1]==0)
        assert x[0, 1, 9] == 0.0   # pas given
        assert is_given[0, 1] == 0.0
        for d in range(9):
            assert x[0, 1, d] == 0.0  # aucun canal-chiffre

    def test_solutions_shifted_minus_one_in_range_0_to_8(self):
        # CrossEntropy attend des labels dans [0, n_classes-1] = [0,8].
        # sudoku_collate_fn applique solutions - 1 : valeur 9 -> label 8.
        solutions = np.full((2, 81), 9, dtype=np.int8)
        puzzles = np.zeros((2, 81), dtype=np.int8)
        _, sol, _ = dataset.sudoku_collate_fn(list(zip(puzzles, solutions)))
        assert sol.max().item() == 8
        assert sol.min().item() == 8  # tout a 9 -> tout a 8
        # et un mix 1..9 -> labels 0..8
        solutions[0, 0] = 1
        _, sol2, _ = dataset.sudoku_collate_fn([(puzzles[0], solutions[0])])
        assert sol2[0, 0].item() == 0  # valeur 1 -> label 0

    def test_is_given_mask_matches_nonzero_puzzle_cells(self):
        puzzle = np.zeros(81, dtype=np.int8)
        puzzle[[0, 5, 40, 80]] = [1, 2, 3, 9]  # 4 clues
        solution = np.ones(81, dtype=np.int8)
        _, _, is_given = dataset.sudoku_collate_fn([(puzzle, solution)])
        # exactement les 4 cellules clue sont "given"
        given_idx = set(np.where(is_given[0].numpy() == 1.0)[0].tolist())
        assert given_idx == {0, 5, 40, 80}

    def test_batch_of_multiple_puzzles_independent(self):
        # Verifie qu'un batch de 3 puzzles encode chacun independamment.
        puzzles = np.zeros((3, 81), dtype=np.int8)
        puzzles[0, 0] = 1
        puzzles[1, 0] = 2
        puzzles[2, 0] = 9
        solutions = np.ones((3, 81), dtype=np.int8)
        x, _, _ = dataset.sudoku_collate_fn(list(zip(puzzles, solutions)))
        assert x[0, 0, 0] == 1.0  # puzzle0 digit1 -> ch0
        assert x[1, 0, 1] == 1.0  # puzzle1 digit2 -> ch1
        assert x[2, 0, 8] == 1.0  # puzzle2 digit9 -> ch8


# --------------------------------------------------------------------------
# count_params — decompte trainable, exclut requires_grad=False
# --------------------------------------------------------------------------

class TestCountParams:
    def test_tiny_linear_layer_exact_count(self):
        # Linear(3, 2) = 3*2 weights + 2 bias = 8 parametres.
        lin = torch.nn.Linear(3, 2)
        assert models.count_params(lin) == 8

    def test_returns_zero_for_parameterless_module(self):
        # ReLU n'a aucun parametre.
        assert models.count_params(torch.nn.ReLU()) == 0

    def test_excludes_frozen_parameters(self):
        lin = torch.nn.Linear(3, 2)  # 8 trainable par defaut
        assert models.count_params(lin) == 8
        for p in lin.parameters():
            p.requires_grad_(False)
        assert models.count_params(lin) == 0  # tous geles -> 0

    def test_sudoku_rrn_has_positive_param_count(self):
        # Le modele complet doit avoir un decompte > 0 (sanity, pas de valeur
        # exacte — depend de hidden_dim/msg_dim/n_steps defaults).
        model = models.SudokuRRN()
        assert models.count_params(model) > 0
