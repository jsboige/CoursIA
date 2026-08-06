"""Tests for scripts/fix_sudoku_hierarchy.py.

Covers the importable pure helpers that implement the byte-surgical heading
demotion logic, plus fix_notebook (via tmp_path synthetic notebooks) and main
(via monkeypatch on sys.argv).

Scope (issue EPIC #3966, tranche 3): heading-as-aside demotion for the Sudoku
family. The three module-level helpers each carry real branching logic that is
worth pinning:
  - _matches_target     : 6 heading patterns (curly/straight apostrophe,
                          parenthetical strip, prefix match)
  - _detect_source_format: 3 nbformat source formats (string / line-list /
                           char-split)
  - _demote_all_headings: joined->line position mapping, reversed-order index
                          preservation, multi-line span collapse, multi-heading
                          cells, no-op on empty/heading-free

fix_notebook exercises: idempotency guard (skip already-demoted `> **`),
format-preservation round-trip (string/line-list/char-split), no-write on
dry-run, write on apply (LF-only via indent=1 binary write), parse error path.
"""
import json
import sys
from pathlib import Path

import importlib.util

# Module lives in scripts/ (flat, not a package) -> spec_from_file_location.
_MOD_PATH = Path(__file__).resolve().parent.parent / "fix_sudoku_hierarchy.py"
_spec = importlib.util.spec_from_file_location("fix_sudoku_hierarchy", _MOD_PATH)
fsh = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(fsh)


# ---------------------------------------------------------------------------
# _matches_target
# ---------------------------------------------------------------------------

def test_matches_target_indices_exact():
    assert fsh._matches_target("Indices") is True


def test_matches_target_etapes_exact_and_prefixed():
    assert fsh._matches_target("Étapes") is True
    assert fsh._matches_target("Étapes a suivre") is True  # legacy no-accent
    assert fsh._matches_target("Étapes de la modélisation avec OR-Tools") is True


def test_matches_target_pistes_curly_and_straight_apostrophe():
    # Curly U+2019 (modern)
    assert fsh._matches_target("Pistes d’amélioration") is True
    # Straight U+0027, no accent (legacy)
    assert fsh._matches_target("Pistes d'amelioration") is True


def test_matches_target_parenthetical_stripped_before_match():
    # A trailing parenthetical (e.g. engine tag) must not block matching.
    assert fsh._matches_target("Indices (Sudoku-1)") is True
    assert fsh._matches_target("Étapes (legacy)") is True


def test_matches_target_rejects_unrelated_headings():
    for t in ["Solution", "Conclusion", "Exercice", "Exemple", "Introduction",
              "Exercice 1", "Indices avancés"]:  # last = not exact "Indices"
        assert fsh._matches_target(t) is False, f"unexpectedly matched {t!r}"


# ---------------------------------------------------------------------------
# _detect_source_format
# ---------------------------------------------------------------------------

def test_detect_format_string():
    assert fsh._detect_source_format("a single joined string\n") == "string"


def test_detect_format_line_list():
    assert fsh._detect_source_format(["line one\n", "line two\n"]) == "line-list"


def test_detect_format_line_list_no_trailing_newline_on_last():
    assert fsh._detect_source_format(["line one\n", "line two"]) == "line-list"


def test_detect_format_empty_is_line_list():
    # Safety convention: empty source treated as line-list.
    assert fsh._detect_source_format([]) == "line-list"


def test_detect_format_char_split():
    # Each element a single char, no '\n' anywhere -> character-split list.
    assert fsh._detect_source_format(list("# heading")) == "char-split"


# ---------------------------------------------------------------------------
# _demote_all_headings
# ---------------------------------------------------------------------------

def test_demote_single_heading_line_list():
    src = ["### Indices\n", "\n", "Some body text.\n"]
    new, n = fsh._demote_all_headings(src)
    assert n == 1
    joined = "".join(new)
    assert "> **Indices :**\n" in joined
    assert "Some body text." in joined  # body preserved


def test_demote_no_heading_returns_unchanged_count_zero():
    src = ["Just prose.\n", "No heading here.\n"]
    new, n = fsh._demote_all_headings(src)
    assert n == 0
    assert new == src  # exact same object returned when nothing matched


def test_demote_empty_source():
    new, n = fsh._demote_all_headings([])
    assert new == []
    assert n == 0


def test_demote_multiple_headings_same_cell_reversed_order():
    # A cell with BOTH ### Étapes and ### Indices (Sudoku-6 pattern).
    src = ["Some intro.\n", "### Étapes\n", "do stuff\n", "### Indices\n",
           "hint\n"]
    new, n = fsh._demote_all_headings(src)
    assert n == 2
    joined = "".join(new)
    assert "> **Étapes :**\n" in joined
    assert "> **Indices :**\n" in joined
    assert "do stuff" in joined  # interleaved body preserved
    assert "hint" in joined


def test_demote_curly_apostrophe_pistes():
    src = ["### Pistes d’amélioration\n", "ideas\n"]
    new, n = fsh._demote_all_headings(src)
    assert n == 1
    assert "> **Pistes d’amélioration :**\n" in "".join(new)


def test_demote_non_target_heading_not_touched():
    # A legit content heading like "### Exercice" must NOT be demoted.
    src = ["### Exercice\n", "solve this\n"]
    new, n = fsh._demote_all_headings(src)
    assert n == 0
    assert "".join(new) == "".join(src)


def test_demote_collapses_character_split_span_into_one_line():
    # Character-split source: the heading is spread across many single-char
    # elements. The demote must collapse the span into one blockquote line.
    src = list("### Indices\nbody here")
    new, n = fsh._demote_all_headings(src)
    assert n == 1
    joined = "".join(new)
    assert "> **Indices :**\n" in joined
    assert "body here" in joined


# ---------------------------------------------------------------------------
# fix_notebook (via tmp_path synthetic notebooks)
# ---------------------------------------------------------------------------

def _make_nb(cell_sources):
    """Build a minimal notebook dict with markdown cells of the given sources."""
    cells = []
    for i, s in enumerate(cell_sources):
        cells.append({
            "cell_type": "markdown",
            "id": f"cell-{i}",
            "metadata": {},
            "source": s if isinstance(s, list) else s,
        })
    return {
        "cells": cells,
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }


def _write_nb(path, nb):
    path.write_bytes((json.dumps(nb, ensure_ascii=False, indent=1) + "\n").encode("utf-8"))


def test_fix_notebook_dry_run_no_write(tmp_path):
    p = tmp_path / "nb.ipynb"
    nb = _make_nb([["### Indices\n", "hint\n"]])
    _write_nb(p, nb)
    before = p.read_bytes()
    n, err = fsh.fix_notebook(p, dry_run=True)
    assert err is None
    assert n == 1
    assert p.read_bytes() == before  # dry-run leaves file untouched


def test_fix_notebook_apply_demotes_and_writes_lf(tmp_path):
    p = tmp_path / "nb.ipynb"
    _write_nb(p, _make_nb([["### Indices\n", "hint\n"]]))
    n, err = fsh.fix_notebook(p, dry_run=False)
    assert err is None
    assert n == 1
    out = p.read_bytes()
    assert b"> **Indices :**" in out
    # LF-only (no CRLF introduced by the binary write).
    assert b"\r\n" not in out
    # Body preserved.
    assert b"hint" in out


def test_fix_notebook_idempotent_skips_already_demoted(tmp_path):
    p = tmp_path / "nb.ipynb"
    # Cell already starts with `> **` -> idempotency guard skips it.
    _write_nb(p, _make_nb(["> **Indices :**\n", "hint\n"]))
    n, err = fsh.fix_notebook(p, dry_run=False)
    assert err is None
    assert n == 0


def test_fix_notebook_no_markdown_cells_zero_change(tmp_path):
    p = tmp_path / "nb.ipynb"
    nb = {
        "cells": [{"cell_type": "code", "source": "print(1)", "id": "c1",
                   "metadata": {}, "outputs": [], "execution_count": None}],
        "metadata": {}, "nbformat": 4, "nbformat_minor": 5,
    }
    _write_nb(p, nb)
    n, err = fsh.fix_notebook(p, dry_run=False)
    assert err is None
    assert n == 0


def test_fix_notebook_parse_error_returns_error(tmp_path):
    p = tmp_path / "bad.ipynb"
    p.write_bytes(b"not valid json {{{")
    n, err = fsh.fix_notebook(p, dry_run=False)
    assert n == 0
    assert err is not None
    assert "parse" in err


def test_fix_notebook_preserves_string_format(tmp_path):
    p = tmp_path / "nb.ipynb"
    # source as a single joined string (string format)
    nb = _make_nb(["### Indices\nhint\n"])
    _write_nb(p, nb)
    n, err = fsh.fix_notebook(p, dry_run=False)
    assert err is None
    assert n == 1
    reloaded = json.loads(p.read_text(encoding="utf-8"))
    cell_src = reloaded["cells"][0]["source"]
    # The 'string' format must round-trip as a single string (not char-split).
    assert isinstance(cell_src, str)
    assert "> **Indices :**" in cell_src
    # Body must be preserved (incident c.925 #8654: string-format body loss).
    assert "hint" in cell_src


# ---------------------------------------------------------------------------
# main (via monkeypatch on sys.argv)
# ---------------------------------------------------------------------------

def test_main_dry_run_target_reports_count(tmp_path, monkeypatch, capsys):
    # Build a synthetic family dir with one notebook.
    fam = tmp_path / "Sudoku"
    fam.mkdir()
    _write_nb(fam / "Sudoku-X.ipynb", _make_nb([["### Indices\n", "hint\n"]]))
    # Redirect the module's FAMILY_DIR to our synthetic family.
    monkeypatch.setattr(fsh, "FAMILY_DIR", fam)
    monkeypatch.setattr(sys, "argv",
                        ["fix_sudoku_hierarchy.py", "--dry-run",
                         "--target", "Sudoku-X.ipynb"])
    rc = fsh.main()
    captured = capsys.readouterr()
    assert rc is None  # main() does not return an explicit code
    assert "Sudoku-X.ipynb: 1 heading(s) demoted (dry-run)" in captured.out
    # Dry-run: file untouched.
    assert b"### Indices" in (fam / "Sudoku-X.ipynb").read_bytes()


def test_main_apply_target_writes(monkeypatch, tmp_path, capsys):
    fam = tmp_path / "Sudoku"
    fam.mkdir()
    _write_nb(fam / "Sudoku-Y.ipynb", _make_nb([["### Étapes\n", "steps\n"]]))
    monkeypatch.setattr(fsh, "FAMILY_DIR", fam)
    monkeypatch.setattr(sys, "argv",
                        ["fix_sudoku_hierarchy.py", "--target", "Sudoku-Y.ipynb"])
    fsh.main()
    # Non-ASCII ("Étapes") cannot live in a bytes literal -> compare decoded text.
    assert "> **Étapes :**" in (fam / "Sudoku-Y.ipynb").read_text(encoding="utf-8")


def test_main_missing_target_reports_to_stderr(monkeypatch, tmp_path, capsys):
    fam = tmp_path / "Sudoku"
    fam.mkdir()
    monkeypatch.setattr(fsh, "FAMILY_DIR", fam)
    monkeypatch.setattr(sys, "argv",
                        ["fix_sudoku_hierarchy.py", "--target", "Ghost.ipynb"])
    fsh.main()
    captured = capsys.readouterr()
    assert "MISSING" in captured.err
