#!/usr/bin/env python3
"""Tests for scripts/fix_texte_hierarchy.py.

Covers the four pure markdown-manipulation helpers and fix_notebook() via
synthetic notebooks in tmp_path (hermetic, no repo files touched).

The most incident-prone logic is _demote_all_hint_headings, which locates
hint headings in the JOINED source then maps them back to line ranges in
the original split source -- including the nbformat 'char-split' form (each
character its own list element). That mapping caused two real content-loss
incidents (c.925 #8654 Sudoku-1 cell 9: 941 -> 16 chars; c.914 commit
318faa104: -970 / -1594 char losses on GenAI/Texte cells), so its correct
behavior is locked here.

Note: fix_texte_hierarchy.py has its OWN inline copy of the logic (stdlib
imports only) -- it does not delegate to notebook_tools/demote_md_asides,
whose separate test (test_demote_md_asides.py) covers the sudoku/tweety
variant with a different HINT set. Tests here use fix_texte_hierarchy's
actual HINT_AS_HEADINGS set (Indices + Pistes variants).

Executable both ways:
    py scripts/tests/test_fix_texte_hierarchy.py
    npx pytest scripts/tests/test_fix_texte_hierarchy.py
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import fix_texte_hierarchy as mod  # noqa: E402


# ---------------------------------------------------------------------------
# _matches_hint
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("text", [
    "Indices",
    "Pistes pour Aller Plus Loin",
    "Pistes pour aller plus loin",        # lowercase variant in set
    "Pistes d'amélioration",              # straight apostrophe + accent
    "Pistes d'amelioration",              # straight apostrophe, no accent (legacy)
])
def test_matches_hint_positive(text):
    assert mod._matches_hint(text) is True


def test_matches_hint_curly_apostrophe_normalized():
    # curly ’ is normalized to straight ' via stem_norm
    assert mod._matches_hint("Pistes d’amélioration") is True


def test_matches_hint_parenthetical_stripped():
    # trailing "(...)" is stripped before matching
    assert mod._matches_hint("Indices (quelques)") is True
    assert mod._matches_hint("Indices (pour aller plus loin)") is True


@pytest.mark.parametrize("text", [
    "Exercice 5",
    "Notes techniques",        # in the sibling's set, NOT in this module's set
    "Sommaire",
    "",
    "### Indices",             # the markdown sigil is not part of the stem text
])
def test_matches_hint_negative(text):
    assert mod._matches_hint(text) is False


# ---------------------------------------------------------------------------
# _detect_source_format
# ---------------------------------------------------------------------------

def test_detect_format_string():
    assert mod._detect_source_format("a single string") == "string"


def test_detect_format_line_list():
    assert mod._detect_source_format(["line1\n", "line2\n"]) == "line-list"


def test_detect_format_char_split():
    # list with no newline in any element -> char-split
    assert mod._detect_source_format(["a", "b", "c"]) == "char-split"


def test_detect_format_empty_list_is_line_list():
    assert mod._detect_source_format([]) == "line-list"


def test_detect_format_single_line_no_newline_is_char_split():
    assert mod._detect_source_format(["no newline here"]) == "char-split"


# ---------------------------------------------------------------------------
# _demote_first_line_h1
# ---------------------------------------------------------------------------

def test_demote_h1_with_trailing_newline():
    out, changed = mod._demote_first_line_h1(["# Title\n", "body"])
    assert changed is True
    assert out == ["## Title\n", "body"]


def test_demote_h1_without_trailing_newline():
    out, changed = mod._demote_first_line_h1(["# Title", "body"])
    assert changed is True
    assert out == ["## Title", "body"]


def test_demote_h1_only_first_line():
    # an H1 NOT on the first line is left alone (conservative)
    out, changed = mod._demote_first_line_h1(["body", "# Title"])
    assert changed is False
    assert out == ["body", "# Title"]


def test_demote_h1_skips_already_h2():
    out, changed = mod._demote_first_line_h1(["## Already H2"])
    assert changed is False
    assert out == ["## Already H2"]


def test_demote_h1_requires_space_after_hash():
    # regex ^#\s+ requires whitespace; "#Title" (no space) is not a heading
    out, changed = mod._demote_first_line_h1(["#NoSpace"])
    assert changed is False


def test_demote_h1_empty():
    assert mod._demote_first_line_h1([]) == ([], False)


# ---------------------------------------------------------------------------
# _demote_all_hint_headings -- the char-split incident-prone mapper
# ---------------------------------------------------------------------------

def test_demote_hint_line_list():
    src = ["### Indices\n", "body text"]
    out, count = mod._demote_all_hint_headings(src)
    assert count == 1
    assert "".join(out) == "> **Indices :**\nbody text"


def test_demote_hint_no_match_returns_unchanged():
    src = ["### Exercice 5\n", "body"]
    out, count = mod._demote_all_hint_headings(src)
    assert count == 0
    assert out == src


def test_demote_hint_char_split_replaces_heading_line():
    """char-split form: each character its own element. The heading line
    (heading text + its trailing '\\n', since the regex's \\s*$ greedily
    consumes the newline) is replaced by the blockquote line."""
    src = list("### Indices\n")
    out, count = mod._demote_all_hint_headings(src)
    assert count == 1
    assert "".join(out) == "> **Indices :**\n"


def test_demote_hint_char_split_preserves_following_body():
    """char-split form WITH body after the heading: the body characters live
    in their own elements beyond the match, so they survive intact. This is
    the exact scenario of the c.925 #8654 content-loss regression -- the body
    must NOT be collapsed. (A blank line separates blockquote from body
    because the heading's own '\\n' element is retained when body follows.)"""
    src = list("### Indices\nhint body here")
    out, count = mod._demote_all_hint_headings(src)
    assert count == 1
    joined = "".join(out)
    assert "hint body here" in joined     # body preserved (not collapsed)
    assert joined.startswith("> **Indices :**\n")


def test_demote_hint_multiple_in_one_cell():
    src = ["### Indices\n", "middle\n", "### Pistes pour Aller Plus Loin\n"]
    out, count = mod._demote_all_hint_headings(src)
    assert count == 2
    joined = "".join(out)
    assert "> **Indices :**" in joined
    assert "> **Pistes pour Aller Plus Loin :**" in joined


def test_demote_hint_empty():
    assert mod._demote_all_hint_headings([]) == ([], 0)


def test_demote_hint_does_not_touch_h1_h2_hint():
    # only #{1,6} headings are scanned, but a hint word as H1/H2 is still a
    # heading match -> it IS demoted (the regex is #{1,6}, not just ###)
    src = ["## Indices\n"]
    out, count = mod._demote_all_hint_headings(src)
    assert count == 1
    assert "".join(out) == "> **Indices :**\n"


# ---------------------------------------------------------------------------
# fix_notebook -- integration via synthetic notebook in tmp_path
# ---------------------------------------------------------------------------

def _write_nb(path: Path, cells: list[dict]) -> Path:
    nb = {"cells": cells, "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
    raw = json.dumps(nb, ensure_ascii=False, indent=1).encode("utf-8") + b"\n"
    path.write_bytes(raw)
    return path


def _md(source):
    # Store string sources AS strings (fix_notebook splits them to a proper
    # line-list internally via splitlines). Wrapping a multi-line string in a
    # single list element would defeat the per-line heading mapper -- the
    # heading's "line range" would span the whole cell and the body would be
    # dropped (the c.925/c.914 content-loss class). String source is the
    # realistic + safe fixture.
    if isinstance(source, str):
        return {"cell_type": "markdown", "source": source}
    return {"cell_type": "markdown", "source": source}


def test_fix_notebook_dry_run_no_write(tmp_path):
    nb_path = _write_nb(tmp_path / "nb.ipynb", [
        _md("# Canonical Title"),            # cell[0] H1 preserved
        _md("# Deep H1\nbody"),              # cell[1] H1 -> H2
        _md("### Indices\nhint body"),       # hint -> blockquote
    ])
    before = nb_path.read_bytes()
    changed, err = mod.fix_notebook(nb_path, dry_run=True)
    assert err is None
    assert changed >= 2
    assert nb_path.read_bytes() == before     # dry-run: untouched


def test_fix_notebook_preserves_cell0_title(tmp_path):
    nb_path = _write_nb(tmp_path / "nb.ipynb", [
        _md("# Canonical Notebook Title"),   # cell[0] must NOT be demoted
        _md("# A Deep Section\ncontent"),
    ])
    mod.fix_notebook(nb_path, dry_run=False)
    nb = json.loads(nb_path.read_bytes())
    assert "".join(nb["cells"][0]["source"]) == "# Canonical Notebook Title"
    assert "".join(nb["cells"][1]["source"]).startswith("## A Deep Section")


def test_fix_notebook_demotes_hint_to_blockquote(tmp_path):
    nb_path = _write_nb(tmp_path / "nb.ipynb", [
        _md("# Title"),
        _md("### Indices\nthe actual hints"),
    ])
    mod.fix_notebook(nb_path, dry_run=False)
    nb = json.loads(nb_path.read_bytes())
    src1 = "".join(nb["cells"][1]["source"])
    assert src1.startswith("> **Indices :**")
    assert "the actual hints" in src1       # body preserved (not collapsed)


def test_fix_notebook_skips_already_demoted(tmp_path):
    nb_path = _write_nb(tmp_path / "nb.ipynb", [
        _md("# Title"),
        _md("> **Indices :**\nalready a blockquote"),
    ])
    changed, err = mod.fix_notebook(nb_path, dry_run=False)
    assert err is None
    assert changed == 0


def test_fix_notebook_skips_code_cells(tmp_path):
    nb_path = _write_nb(tmp_path / "nb.ipynb", [
        _md("# Title"),
        {"cell_type": "code", "source": ["# Indices\n"], "outputs": [], "execution_count": 1},
    ])
    changed, err = mod.fix_notebook(nb_path, dry_run=False)
    assert err is None
    assert changed == 0
