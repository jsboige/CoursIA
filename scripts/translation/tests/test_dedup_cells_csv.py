#!/usr/bin/env python3
"""Tests pour scripts/translation/dedup_cells_csv.py — outil de déduplication
des lignes du CSV de cellules (#19023, chantier 1). L'invariant central : la
dédup ne réordonne RIEN (ni carnets ni lignes conservées) et refuse tout
fichier qu'elle ne peut pas relire byte-identique — la regen intégrale (T1
--full) reste réservée au resync, pas au nettoyage.

Couvre : dédup d'occurrences byte-identiques, refus sur divergence (arbitrage
manuel), mode --check sans écriture, garde round-trip (fichier CRLF refusé),
ordre des carnets inchangé. stdlib-only, hermétique (tmp_path).
"""

import csv
import io
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
TRANSLATION_DIR = HERE.parent
sys.path.insert(0, str(TRANSLATION_DIR))

import dedup_cells_csv  # noqa: E402

HEADER = ["notebook", "cell_id", "cell_type", "src_lang", "src_hash"]


def _row(nb: str, cid: str, extra: str = "x") -> list[str]:
    return [nb, cid, "markdown", "fr", extra]


def _write_csv(path: Path, rows: list[list[str]], lineterminator: str = "\n") -> None:
    buffer = io.StringIO(newline="")
    csv.writer(buffer, lineterminator=lineterminator).writerows(rows)
    with io.open(path, "w", encoding="utf-8", newline="") as handle:
        handle.write(buffer.getvalue())


# --- dédup pure : occurrences identiques

def test_dedup_identical_duplicates_keeps_first_and_order():
    rows = [
        HEADER,
        _row("nb-a", "c1", "h1"),
        _row("nb-a", "c2", "h2"),
        _row("nb-a", "c1", "h1"),  # doublon exact, plus tard dans le fichier
        _row("nb-b", "c1", "h3"),
    ]
    deduped, removed, errors = dedup_cells_csv.dedup(rows)
    assert removed == 1
    assert errors == []
    assert [r[4] for r in deduped[1:]] == ["h1", "h2", "h3"]
    assert dedup_cells_csv.notebook_order(rows) == dedup_cells_csv.notebook_order(deduped)


def test_dedup_no_duplicates_is_noop():
    rows = [HEADER, _row("nb-a", "c1"), _row("nb-a", "c2")]
    deduped, removed, errors = dedup_cells_csv.dedup(rows)
    assert removed == 0
    assert errors == []
    assert deduped == rows


# --- dédup pure : divergence = refus nommé

def test_dedup_divergent_duplicates_refuses():
    rows = [
        HEADER,
        _row("nb-a", "c1", "ancien-hash"),
        _row("nb-a", "c1", "nouveau-hash"),  # divergence : arbitrage manuel
    ]
    deduped, removed, errors = dedup_cells_csv.dedup(rows)
    assert removed == 1
    assert len(errors) == 1
    assert "nb-a" in errors[0] and "arbitrage" in errors[0]
    # la divergence ne tranche pas : première occurrence conservée dans la
    # sortie, MAIS main() refusera l'écriture (voir test dédié)


# --- notebook_order

def test_notebook_order_first_occurrences_only():
    rows = [HEADER, _row("nb-b", "c1"), _row("nb-a", "c1"), _row("nb-b", "c2")]
    assert dedup_cells_csv.notebook_order(rows) == ["nb-b", "nb-a"]


# --- main() : écriture réelle, --check, gardes

def test_main_dedups_real_file(tmp_path):
    path = tmp_path / "cells.csv"
    _write_csv(path, [HEADER, _row("nb-a", "c1"), _row("nb-a", "c1"), _row("nb-b", "c1")])
    rc = dedup_cells_csv.main([str(path)])
    assert rc == 0
    with io.open(path, encoding="utf-8", newline="") as handle:
        rows = list(csv.reader(handle))
    assert len(rows) == 3  # header + 2 lignes uniques
    assert [r[0] for r in rows[1:]] == ["nb-a", "nb-b"]


def test_main_check_mode_writes_nothing(tmp_path):
    path = tmp_path / "cells.csv"
    _write_csv(path, [HEADER, _row("nb-a", "c1"), _row("nb-a", "c1")])
    before = path.read_bytes()
    rc = dedup_cells_csv.main(["--check", str(path)])
    assert rc == 0
    assert path.read_bytes() == before


def test_main_refuses_non_roundtrippable_file(tmp_path):
    # fichier sérialisé en CRLF : le writer (LF) ne le reproduirait pas
    # byte-identique → refus, fichier inchangé
    path = tmp_path / "cells.csv"
    _write_csv(path, [HEADER, _row("nb-a", "c1"), _row("nb-a", "c1")], lineterminator="\r\n")
    before = path.read_bytes()
    rc = dedup_cells_csv.main([str(path)])
    assert rc == 1
    assert path.read_bytes() == before


def test_main_refuses_divergent_duplicates_without_write(tmp_path):
    path = tmp_path / "cells.csv"
    _write_csv(
        path,
        [HEADER, _row("nb-a", "c1", "ancien"), _row("nb-a", "c1", "nouveau")],
    )
    before = path.read_bytes()
    rc = dedup_cells_csv.main([str(path)])
    assert rc == 1
    assert path.read_bytes() == before
