"""Tests for the `_fix_source_newlines` helper (normalize-source-newlines, #5005).

Locks in the boundary-aware surgical fix that replaced the earlier blanket transform.
The blanket form added '\\n' to every non-last source element unconditionally, which
(a) doubled existing newlines ('\\n\\n' -> '\\n\\n\\n\\n') and (b) inserted hard breaks
into flowing markdown prose split across list elements -- both cosmetic false positives
that the blanket transform corrupted. The surgical fix touches ONLY boundaries where
''.join glues two non-whitespace tokens.

Covers:
  - genuine code-cell merge (the original #5005 root cause: a leading comment swallows
    the cell when ''.join collapses to one line)
  - genuine markdown heading-glue (po-2024's 01-3-Basic-Image cell25 pattern)
  - cosmetic: mid-paragraph chunk split at a trailing space (must stay flowing)
  - cosmetic: next element carries the '\\n' (must not double)
  - cosmetic: elements already ending in '\\n' (must not double)
  - regression: a cell the OLD blanket tool corrupted is left byte-identical
  - string-form source and single-element lists (no-op)
"""

import sys
from pathlib import Path

_tools_dir = str(Path(__file__).resolve().parent.parent)
if _tools_dir not in sys.path:
    sys.path.insert(0, _tools_dir)

from notebook_tools import _fix_source_newlines


# --- genuine cases (must fix) ---


def test_genuine_code_cell_merge_is_fixed():
    # The #5005 root cause: two statements glued, ''.join = one line.
    src = ["print('a')", "print('b')"]
    new_src, changed = _fix_source_newlines(src)
    assert changed is True
    assert "".join(new_src) == "print('a')\nprint('b')"


def test_genuine_markdown_heading_glue_is_fixed():
    # po-2024's 01-3-Basic-Image cell25 pattern: heading glued to preceding prose.
    src = ["Some prose ending here.", "### Heading glued"]
    new_src, changed = _fix_source_newlines(src)
    assert changed is True
    assert "".join(new_src) == "Some prose ending here.\n### Heading glued"


# --- cosmetic cases (must NOT change) ---


def test_cosmetic_mid_paragraph_space_is_untouched():
    # Trailing space = mid-paragraph chunk; join flows correctly. Must not break.
    src = ["A paragraph that ", "continues flowing."]
    new_src, changed = _fix_source_newlines(src)
    assert changed is False
    assert "".join(new_src) == "A paragraph that continues flowing."


def test_cosmetic_next_element_carries_newline_is_untouched():
    # elem[k] lacks '\n' but elem[k+1] STARTS with '\n' -> separator already present.
    src = ["Line one", "\nLine two"]
    new_src, changed = _fix_source_newlines(src)
    assert changed is False
    assert "".join(new_src) == "Line one\nLine two"


def test_cosmetic_leading_space_next_is_untouched():
    # elem[k+1] starts with a space -> joins cleanly. Must not add '\n'.
    src = ["mots", " collés par espace en tête"]
    new_src, changed = _fix_source_newlines(src)
    assert changed is False
    assert "".join(new_src) == "mots collés par espace en tête"


def test_already_newline_terminated_not_doubled():
    # Every non-last element already ends in '\n' -> no genuine break, no change.
    # The OLD blanket form would have produced '\n\n' here (the doubling bug).
    src = ["line1\n", "line2\n", "line3"]
    new_src, changed = _fix_source_newlines(src)
    assert changed is False
    assert new_src == src  # byte-identical (no doubling)


# --- regression: mixed genuine + cosmetic in one cell ---


def test_mixed_cell_fixes_only_genuine_boundaries():
    # One genuine break + one cosmetic (space) boundary: only the genuine one fixed.
    src = ["print('a')", "print('b')", " # trailing comment chunk"]
    new_src, changed = _fix_source_newlines(src)
    assert changed is True
    # boundary 0 (print/print) genuine -> '\n' added; boundary 1 (space) cosmetic -> kept.
    assert "".join(new_src) == "print('a')\nprint('b') # trailing comment chunk"


def test_paragraph_break_not_doubled():
    # A markdown cell with a deliberate '\n\n' paragraph break plus a cosmetic chunk.
    # The OLD blanket tool turned '\n\n' into '\n\n\n\n'. Surgical fix must preserve.
    src = ["First paragraph.\n\n", "Second ", "paragraph flows."]
    new_src, changed = _fix_source_newlines(src)
    assert changed is False
    assert "".join(new_src) == "First paragraph.\n\nSecond paragraph flows."


# --- no-op cases ---


def test_string_form_source_is_noop():
    new_src, changed = _fix_source_newlines("a single string source")
    assert changed is False
    assert new_src == "a single string source"


def test_single_element_list_is_noop():
    src = ["only one element"]
    new_src, changed = _fix_source_newlines(src)
    assert changed is False
    assert new_src is src


def test_empty_list_is_noop():
    src = []
    new_src, changed = _fix_source_newlines(src)
    assert changed is False
    assert new_src is src
