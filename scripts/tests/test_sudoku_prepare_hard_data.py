#!/usr/bin/env python3
"""Tests pour scripts/sudoku/prepare_hard_data.py — préparation du dataset
Sudoku-extreme (Phase 2, sapientinc/sudoku-extreme).

Couvre les fonctions pures HERMETIQUES de parsing/conversion du dataset :
  - _parse_81 : string 81-char -> (81,) int8 array (0 = cellule vide)
  - _convert_csv : CSV (source,question,answer,rating) -> (puzzles, solutions) npz
  - _report : statistiques de givens (min/max/mean/pct)

main() télécharge via huggingface_hub (réseau) -> hors scope hermétique :
non testé ici (l'import lazy `hf_hub_download` est dans main(), pas au top-level,
donc le module s'importe sans réseau). numpy-only, fixtures synthétiques sous
tmp_path, aucun téléchargement.

LIVE: 4 callers (sudoku_curriculum_train, sudoku_double_track, train_phase2_hard,
phase2_iterative) attendent le format npz (puzzles/solutions (N,81) int8).
"""

import sys
from pathlib import Path

import numpy as np
import pytest

# Add sudoku/ to sys.path (convention scripts/tests/test_sudoku_*.py)
_SUDOKU_DIR = str(Path(__file__).resolve().parent.parent / "sudoku")
if _SUDOKU_DIR not in sys.path:
    sys.path.insert(0, _SUDOKU_DIR)

from prepare_hard_data import _parse_81, _convert_csv, _report  # noqa: E402


# --------------------------------------------------------------------------
# Helpers
# --------------------------------------------------------------------------

def _full81(digits):
    """Construit une string de 81 chars à partir d'une liste de 81 ints (0->'.')."""
    assert len(digits) == 81
    return "".join("." if d == 0 else str(d) for d in digits)


def _write_csv(path, rows):
    """rows = liste de dict {source, question, answer, rating}."""
    path.parent.mkdir(parents=True, exist_ok=True)
    import csv as _csv
    with path.open("w", encoding="utf-8", newline="") as f:
        w = _csv.DictWriter(f, fieldnames=["source", "question", "answer", "rating"])
        w.writeheader()
        for r in rows:
            w.writerow(r)
    return path


# --------------------------------------------------------------------------
# _parse_81 — string 81-char -> (81,) int8 array
# --------------------------------------------------------------------------

def test_parse_81_all_digits_values():
    s = "123456789" * 9  # 81 chars, digits 1-9 répétés
    arr = _parse_81(s)
    assert arr.shape == (81,)
    assert arr.dtype == np.int8
    # chaque digit positionnel correct
    for i, ch in enumerate(s):
        assert arr[i] == int(ch)


def test_parse_81_dot_means_empty():
    s = "." * 81
    arr = _parse_81(s)
    assert arr.shape == (81,)
    assert (arr == 0).all()


def test_parse_81_zero_char_means_empty():
    """Le format source utilise '.' OU '0' pour les cellules vides."""
    s = "0" * 81
    arr = _parse_81(s)
    assert (arr == 0).all()


def test_parse_81_mixed_digits_and_empties():
    # 17 givens (le minimum pour un Sudoku unique), reste vide
    digits = [5]*17 + [0]*64
    s = _full81(digits)
    arr = _parse_81(s)
    assert arr.shape == (81,)
    assert (arr[:17] == 5).all()
    assert (arr[17:] == 0).all()
    assert arr.dtype == np.int8


def test_parse_81_round_trip_with_full81_helper():
    digits = [(i % 9) + 1 for i in range(81)]  # 1..9 cyclique, aucun vide
    s = _full81(digits)
    arr = _parse_81(s)
    assert arr.tolist() == digits


# --------------------------------------------------------------------------
# _convert_csv — CSV (source,question,answer,rating) -> (puzzles, solutions)
# --------------------------------------------------------------------------

def test_convert_csv_parses_valid_rows(tmp_path):
    q1 = _full81([5] + [0] * 80)
    a1 = _full81([1] * 81)
    q2 = _full81([3] + [0] * 80)
    a2 = _full81([2] * 81)
    csv_path = _write_csv(tmp_path / "in.csv", [
        {"source": "src", "question": q1, "answer": a1, "rating": 9.0},
        {"source": "src", "question": q2, "answer": a2, "rating": 8.5},
    ])
    puzzles, solutions = _convert_csv(str(csv_path))
    assert puzzles.shape == (2, 81)
    assert solutions.shape == (2, 81)
    assert puzzles.dtype == np.int8
    assert solutions.dtype == np.int8
    # première cellule des puzzles préservée, le reste vide
    assert puzzles[0, 0] == 5 and (puzzles[0, 1:] == 0).all()
    # solutions entièrement remplies
    assert (solutions[0] == 1).all()
    assert (solutions[1] == 2).all()


def test_convert_csv_skips_rows_with_wrong_length(tmp_path):
    """Les lignes dont question/answer != 81 chars sont ignorées (silencieusement)."""
    valid_q = _full81([5] + [0] * 80)
    valid_a = _full81([1] * 81)
    csv_path = _write_csv(tmp_path / "in.csv", [
        {"source": "s", "question": valid_q, "answer": valid_a, "rating": 1.0},  # OK
        {"source": "s", "question": "123", "answer": valid_a, "rating": 1.0},     # question trop courte
        {"source": "s", "question": valid_q, "answer": "12", "rating": 1.0},      # answer trop court
        {"source": "s", "question": valid_q, "answer": valid_a, "rating": 2.0},  # OK
    ])
    puzzles, solutions = _convert_csv(str(csv_path))
    assert puzzles.shape == (2, 81)  # 2 valides sur 4


def test_convert_csv_max_rows_truncation(tmp_path):
    rows = []
    for i in range(10):
        rows.append({
            "source": "s", "question": _full81([i + 1] + [0] * 80),
            "answer": _full81([9] * 81), "rating": float(i),
        })
    csv_path = _write_csv(tmp_path / "in.csv", rows)
    puzzles, solutions = _convert_csv(str(csv_path), max_rows=3)
    assert puzzles.shape == (3, 81)
    assert solutions.shape == (3, 81)


def test_convert_csv_empty_file_returns_empty_arrays(tmp_path):
    """CSV sans ligne valide : puzzles=[] -> np.array([]) est 1-D shape (0,),
    PAS (0, 81). Quirk numpy documenté (le module ne reshape pas l'empty case).
    Latent : en pratique le dataset source téléchargé est toujours non-vide,
    donc ce cas n'arrive jamais dans main(). On pinne le comportement réel."""
    csv_path = _write_csv(tmp_path / "empty.csv", [])
    puzzles, solutions = _convert_csv(str(csv_path))
    assert puzzles.shape == (0,)
    assert solutions.shape == (0,)
    assert puzzles.dtype == np.int8


def test_convert_csv_consistency_with_parse_81(tmp_path):
    """Le puzzle converti doit être identique à _parse_81(question) row-par-row."""
    qs = [_full81([(i % 9) + 1] + [0] * 80) for i in range(5)]
    a = _full81([7] * 81)
    rows = [{"source": "s", "question": q, "answer": a, "rating": 1.0} for q in qs]
    csv_path = _write_csv(tmp_path / "in.csv", rows)
    puzzles, _ = _convert_csv(str(csv_path))
    for i, q in enumerate(qs):
        assert puzzles[i].tolist() == _parse_81(q).tolist()


def test_convert_csv_dtype_int8_boundary_values(tmp_path):
    """Les valeurs 1-9 tiennent dans int8 ; 0 (vide) aussi. Vérifier pas d'overflow."""
    digits = [1, 9, 1, 9] + [0] * 77
    q = _full81(digits)
    a = _full81([9] * 81)
    csv_path = _write_csv(tmp_path / "in.csv", [
        {"source": "s", "question": q, "answer": a, "rating": 1.0}])
    puzzles, solutions = _convert_csv(str(csv_path))
    assert puzzles.dtype == np.int8
    assert puzzles[0, 0] == 1 and puzzles[0, 1] == 9
    assert solutions.max() == 9 and solutions.min() == 9


# --------------------------------------------------------------------------
# _report — statistiques de givens (capture stdout)
# --------------------------------------------------------------------------

def test_report_prints_givens_statistics(capsys):
    # 3 puzzles : 17, 22, 30 givens (le reste = 0)
    puzzles = np.zeros((3, 81), dtype=np.int8)
    puzzles[0, :17] = np.arange(1, 18, dtype=np.int8)
    puzzles[1, :22] = np.arange(1, 23, dtype=np.int8)
    puzzles[2, :30] = np.arange(1, 31, dtype=np.int8)
    _report("train", puzzles)
    out = capsys.readouterr().out
    assert "train" in out
    assert "min=17" in out
    assert "max=30" in out
    # mean = (17+22+30)/3 = 23.0
    assert "mean=23.0" in out
    # pct<=22 = 2/3 = 0.667
    assert "0.667" in out


def test_report_single_puzzle(capsys):
    puzzles = np.zeros((1, 81), dtype=np.int8)
    puzzles[0, :25] = 5
    _report("test", puzzles)
    out = capsys.readouterr().out
    assert "min=25" in out
    assert "max=25" in out
    assert "mean=25.0" in out
    assert "1" in out  # count


def test_report_empty_dataset_handled(capsys):
    """Un dataset vide ne doit pas crasher (min/max sur array vide = erreur numpy
    -> le helper doit soit gérer, soit on documente qu'il attend >= 1 puzzle)."""
    puzzles = np.zeros((0, 81), dtype=np.int8)
    # _report appelle .min()/.max() sur givens (vide) -> ValueError attendu.
    # On documente le contrat : _report n'est appelé qu'avec >= 1 puzzle (main()
    # garantit min via le dataset source). On pinne ce comportement.
    with pytest.raises(ValueError):
        _report("empty", puzzles)
