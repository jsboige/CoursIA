"""Unit tests for scripts/relabel_qc_exercises.py.

This module relabels exercise/example-guide headers in QuantConnect notebooks
to ascending order. It is durable tooling (re-run whenever a QC notebook's
exercise cells get re-numbered) but had ZERO test coverage. These tests pin the
pure logic (header detection, the 2-pass placeholder swap that avoids
chained rewrites, the audit scrambled-detector invariant) and an integration
run on a fake notebook.

Run from repo root::

    python -m pytest scripts/tests/test_relabel_qc_exercises.py -q
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

# Make ``scripts/`` importable (same bootstrap as test_verify_diarization.py).
_SCRIPTS = Path(__file__).resolve().parent.parent
if str(_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(_SCRIPTS))

from relabel_qc_exercises import (  # noqa: E402
    EXERCICE_PAT,
    RELABEL_MAP,
    _replace_in_source,
    _to_text,
    get_exercice_num,
    relabel_notebook,
)


# ──────────────────────────────────────────────────────────────────────────
# get_exercice_num — header detection
# ──────────────────────────────────────────────────────────────────────────


def test_detects_exercice_header_number():
    """A `### Exercice N` markdown header yields N."""
    assert get_exercice_num("### Exercice 3") == 3


def test_detects_exemple_guide_header_number():
    """A `### Exemple guide N` markdown header yields N (the regex accepts
    both labels — example guides and exercises are both numbered)."""
    assert get_exercice_num("### Exemple guide 5") == 5


def test_case_insensitive_detection():
    """Header detection is case-insensitive (EXERCICE_PAT uses re.IGNORECASE)
    so 'exercice' / 'EXERCICE' also match."""
    assert get_exercice_num("### exercice 3") == 3
    assert get_exercice_num("### EXERCICE 7") == 7


def test_header_inside_multiline_source():
    """The header may not be the first line — search() finds it anywhere in
    a multiline cell source (notebook source can be a list of lines)."""
    multi = ["some intro\n", "### Exercice 12\n", "\n", "Solve this.\n"]
    assert get_exercice_num(multi) == 12


def test_no_number_returns_none():
    """A header without a trailing digit is not an exercise label."""
    assert get_exercice_num("### Exercice") is None
    assert get_exercice_num("### Conclusion") is None


def test_non_markdown_returns_none():
    """A plain code-style line is not detected (no `### ` prefix)."""
    assert get_exercice_num("Exercice 3") is None
    assert get_exercice_num("## Exercice 3") is None  # h2, not h3
    assert get_exercice_num("") is None


def test_accepts_string_or_list_source():
    """get_exercice_num coerces both a string and a list source (notebook
    cell sources come in both forms) via _to_text."""
    assert get_exercice_num("### Exercice 4") == 4
    assert get_exercice_num(["### Exercice 4\n"]) == 4


# ──────────────────────────────────────────────────────────────────────────
# _replace_in_source — the 2-pass placeholder swap
# ──────────────────────────────────────────────────────────────────────────


def test_replace_string_source_swaps_label():
    """A string source: `Exercice 3` -> `Exercice 1` (old -> new)."""
    src = "### Exercice 3\nSee Exercice 3 for context."
    out = _replace_in_source(src, old_n=3, new_n=1)
    assert out == "### Exercice 1\nSee Exercice 1 for context."


def test_replace_does_not_chain_via_placeholder():
    """The 2-pass placeholder swap (old -> __RL_new__ -> new) prevents a
    chained rewrite: renaming 3->1 must NOT then rename the freshly-written
    `1` to something else. Within a single cell only the old label moves."""
    # A cell that mentions BOTH 3 and 1: only the 3s move to 1.
    src = "Exercice 3 and Exercice 1 both here"
    out = _replace_in_source(src, old_n=3, new_n=1)
    # Both 3s became 1s; the original 1 stays 1 (no double-move).
    assert out == "Exercice 1 and Exercice 1 both here"
    # And critically, a hypothetical 3->1->3 chain would have left the moved
    # label back at 3 — verify it did NOT by counting 'Exercice 3'.
    assert "Exercice 3" not in out


def test_replace_handles_exemple_guide_label():
    """The placeholder swap applies to the 'Exemple guide' label too, not
    just 'Exercice'."""
    src = "### Exemple guide 5"
    out = _replace_in_source(src, old_n=5, new_n=2)
    assert out == "### Exemple guide 2"


def test_replace_list_source_preserves_structure():
    """A list source (per-line) is returned as a list of the same length —
    the rewrite happens per-line, structure preserved."""
    src = ["### Exercice 3\n", "Body referencing Exercice 3.\n"]
    out = _replace_in_source(src, old_n=3, new_n=1)
    assert isinstance(out, list)
    assert len(out) == 2
    assert "".join(out) == "### Exercice 1\nBody referencing Exercice 1.\n"


def test_replace_only_touches_target_number():
    """Renaming 3->1 must NOT touch an unrelated 'Exercice 7' in the same
    cell — only the old_n label moves."""
    src = "Exercice 3 then Exercice 7"
    out = _replace_in_source(src, old_n=3, new_n=1)
    assert out == "Exercice 1 then Exercice 7"


# Multi-digit boundary regression (was a silent corruption: the naive
# str.replace matched the "1" prefix of "12", turning "Exercice 12" into
# "Exercice 92" when relabeling exercise 1 -> 9).
# ──────────────────────────────────────────────────────────────────────────


def test_replace_multi_digit_not_corrupted_by_single_digit_old():
    """Renaming 1->9 must leave 'Exercice 12' intact (was corrupted to
    'Exercice 92' by the prefix-matching str.replace)."""
    src = "### Exercice 1\nSee Exercice 12 for context."
    out = _replace_in_source(src, old_n=1, new_n=9)
    assert out == "### Exercice 9\nSee Exercice 12 for context."


def test_replace_multi_digit_not_corrupted_when_relabeling_higher_digit():
    """Renaming 3->1 must also leave 'Exercice 30' intact (the naive
    str.replace('Exercice 3', ...) matched the '3' in '30')."""
    src = "Exercice 3 then Exercice 30"
    out = _replace_in_source(src, old_n=3, new_n=1)
    assert out == "Exercice 1 then Exercice 30"


def test_replace_multi_digit_old_n_matched_correctly():
    """A multi-digit old_n is matched as a whole (relabeling 12 -> 5 touches
    'Exercice 12' but not 'Exercice 1' nor 'Exercice 120')."""
    src = "Exercice 1, Exercice 12, Exercice 120"
    out = _replace_in_source(src, old_n=12, new_n=5)
    assert out == "Exercice 1, Exercice 5, Exercice 120"


def test_replace_multi_digit_list_source_not_corrupted():
    """The boundary guard applies on the per-line list path too."""
    src = ["### Exercice 1\n", "Refs Exercice 12.\n"]
    out = _replace_in_source(src, old_n=1, new_n=9)
    assert "".join(out) == "### Exercice 9\nRefs Exercice 12.\n"


def test_replace_exemple_guide_multi_digit_not_corrupted():
    """The 'Exemple guide' label gets the same boundary protection."""
    src = "Exemple guide 1 and Exemple guide 12"
    out = _replace_in_source(src, old_n=1, new_n=2)
    assert out == "Exemple guide 2 and Exemple guide 12"


# ──────────────────────────────────────────────────────────────────────────
# RELABEL_MAP sanity (the hand-curated target table)
# ──────────────────────────────────────────────────────────────────────────


def test_relabel_map_entries_are_valid_triplets():
    """Each RELABEL_MAP entry is (cell_idx, old_num, new_num) — 3 ints. A
    malformed entry would crash relabel_notebook at unpack time."""
    for nb_path, mappings in RELABEL_MAP.items():
        assert nb_path.endswith(".ipynb"), f"{nb_path} is not an .ipynb path"
        for entry in mappings:
            assert len(entry) == 3, f"{nb_path}: entry {entry} is not a 3-tuple"
            cell_idx, old_n, new_n = entry
            assert isinstance(cell_idx, int) and cell_idx >= 0
            assert isinstance(old_n, int) and old_n >= 1
            assert isinstance(new_n, int) and new_n >= 1


# ──────────────────────────────────────────────────────────────────────────
# relabel_notebook — integration on a fake notebook
# ──────────────────────────────────────────────────────────────────────────


def _write_fake_nb(tmp_path: Path, cells: list) -> Path:
    """Write a minimal .ipynb with the given cell source list."""
    nb = {
        "cells": [{"cell_type": ct, "source": src, "metadata": {}} for ct, src in cells],
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    p = tmp_path / "FakeQC.ipynb"
    p.write_text(json.dumps(nb), encoding="utf-8")
    return p


def test_relabel_applies_mapping_dry_run(tmp_path):
    """A dry-run reports the change but does NOT write to disk."""
    cells = [
        ("markdown", "### Exercice 3\n"),  # cell 0: scrambled (should be 1)
        ("code", "print('solve')\n"),
    ]
    nb_path = _write_fake_nb(tmp_path, cells)
    before = nb_path.read_text(encoding="utf-8")

    changed = relabel_notebook(nb_path, [(0, 3, 1)], dry_run=True)

    assert changed is True, "dry-run must report the would-be change"
    assert nb_path.read_text(encoding="utf-8") == before, "dry-run must NOT write"


def test_relabel_applies_mapping_writes_disk(tmp_path):
    """A non-dry-run writes the relabeled source to disk and the cell now
    reads the new number."""
    cells = [("markdown", "### Exercice 3\n")]
    nb_path = _write_fake_nb(tmp_path, cells)

    relabel_notebook(nb_path, [(0, 3, 1)], dry_run=False)

    nb = json.loads(nb_path.read_text(encoding="utf-8"))
    assert get_exercice_num(nb["cells"][0]["source"]) == 1


def test_relabel_skips_non_markdown_cell(tmp_path):
    """A mapping pointing at a non-markdown cell is skipped (WARN, not
    crash) and does not corrupt the cell."""
    cells = [("code", "x = 1\n")]
    nb_path = _write_fake_nb(tmp_path, cells)

    changed = relabel_notebook(nb_path, [(0, 3, 1)], dry_run=False)

    assert changed is False
    nb = json.loads(nb_path.read_text(encoding="utf-8"))
    assert nb["cells"][0]["source"] == "x = 1\n"


def test_relabel_skip_already_correct(tmp_path):
    """A cell already at the target number is skipped (no-op), not rewritten."""
    cells = [("markdown", "### Exercice 1\n")]
    nb_path = _write_fake_nb(tmp_path, cells)
    before = nb_path.read_text(encoding="utf-8")

    changed = relabel_notebook(nb_path, [(0, 1, 1)], dry_run=False)

    assert changed is False
    assert nb_path.read_text(encoding="utf-8") == before


def test_relabel_oob_cell_index_skipped(tmp_path):
    """A mapping whose cell_idx exceeds the cell count is skipped (WARN),
    not an IndexError crash."""
    cells = [("markdown", "### Exercice 3\n")]
    nb_path = _write_fake_nb(tmp_path, cells)

    # cell_idx 99 does not exist; the (0, 3, 1) mapping DOES.
    changed = relabel_notebook(nb_path, [(99, 3, 1), (0, 3, 1)], dry_run=False)

    assert changed is True  # the valid (0,3,1) mapping still applied
    nb = json.loads(nb_path.read_text(encoding="utf-8"))
    assert get_exercice_num(nb["cells"][0]["source"]) == 1


def test_relabel_cell_without_label_skipped(tmp_path):
    """A mapping pointing at a markdown cell that has NO exercise label is
    skipped (WARN), not a crash on int(None)."""
    cells = [("markdown", "### Conclusion\nno exercise here\n")]
    nb_path = _write_fake_nb(tmp_path, cells)
    before = nb_path.read_text(encoding="utf-8")

    changed = relabel_notebook(nb_path, [(0, 3, 1)], dry_run=False)

    assert changed is False
    assert nb_path.read_text(encoding="utf-8") == before
