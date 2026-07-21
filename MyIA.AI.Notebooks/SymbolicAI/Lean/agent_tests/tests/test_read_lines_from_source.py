"""Regression suite for ``prover.tools._read_lines_from_source`` (#7477 P5b/P6 residual).

Background. ``_read_lines_from_source(source, start, end)`` is the pure
1-based-inclusive line-extraction primitive that three agent file-read tools
delegate to:

  * ``SearchTools.file_read_lines``      (``prover/tools.py`` L668)
  * ``CoordinatorTools.file_read_lines`` (``prover/tools.py`` L1005)
  * third call site                      (``prover/tools.py`` L2655)

Agents read sorry-context and source excerpts through this helper, so a silent
regression in its clamping (``max(1, start)`` / ``min(len(lines), end)``), its
1-based-inclusive indexing, or its ``"{n}: {line}"`` prefix format would
corrupt every downstream excerpt the Coordinator/Tactic agents reason over --
without any test catching it.  As of c.731 this helper had **zero** dedicated
coverage (grep of ``tests/`` returned no reference outside ``tools.py`` itself),
unlike its three sibling pure parsers (``_parse_lean_errors``,
``_count_sorries_from_build_output``, ``_is_heartbeat_timeout``) which each
have a dedicated regression suite.

This file pins the contract on the cases that exercise each branch:

  * basic multi-line range + ``"{n}: {line}"`` prefix
  * ``start < 1`` clamping (0 and negative) -> treated as line 1
  * ``end > len(lines)`` clamping -> capped at last line
  * ``start > end`` (inverted) -> empty selection
  * empty source / single-line source / trailing-newline source
  * off-by-one boundary ``start == end`` (inclusive single line)
  * ``end == 0`` -> empty selection

Stdlib-only -- imports the helper via ``sys.path`` manipulation exactly like
``test_prover_guards.py`` (#7477), so it runs without the LLM stack.

Run: ``python -m pytest tests/test_read_lines_from_source.py -q``
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

# Make `prover/` importable regardless of how pytest was invoked.
ROOT = Path(__file__).resolve().parents[1]  # agent_tests/
sys.path.insert(0, str(ROOT))

from prover.tools import _read_lines_from_source  # noqa: E402


# ---------------------------------------------------------------------------
# Basic range extraction + line-number prefix format
# ---------------------------------------------------------------------------


def test_basic_multiline_range_prefix_format():
    """A 3-line slice carries the 1-based ``{n}: {line}`` prefix per line."""
    result = _read_lines_from_source("a\nb\nc\nd\ne", 2, 4)
    assert result == "2: b\n3: c\n4: d"


def test_full_range():
    """start=1, end=len yields every line with contiguous numbering."""
    assert _read_lines_from_source("a\nb\nc", 1, 3) == "1: a\n2: b\n3: c"


def test_single_line_source():
    """A one-line source returns that line prefixed with ``1:``."""
    assert _read_lines_from_source("only", 1, 1) == "1: only"


# ---------------------------------------------------------------------------
# start < 1 clamping (the non-redundant branch)
# ---------------------------------------------------------------------------


def test_start_zero_clamped_to_one():
    """start=0 is clamped to 1 (max(1, start)); without the clamp Python's
    negative index would silently select the LAST line instead of the first.
    """
    assert _read_lines_from_source("a\nb\nc", 0, 2) == "1: a\n2: b"


def test_start_negative_clamped_to_one():
    """A strongly negative start is clamped to 1, not treated as a Python
    negative slice index (which would wrap to the end of the list)."""
    assert _read_lines_from_source("a\nb\nc", -5, 2) == "1: a\n2: b"


# ---------------------------------------------------------------------------
# end > len(lines) clamping
# ---------------------------------------------------------------------------


def test_end_beyond_length_clamped():
    """end greater than the number of lines is capped at the last line -- no
    IndexError, no phantom empty trailing entries."""
    assert _read_lines_from_source("a\nb\nc", 2, 100) == "2: b\n3: c"


def test_trailing_newline_source():
    """A source ending in ``\\n`` splits to a trailing empty string entry;
    requesting the full range surfaces it as a numbered empty line (mirrors
    how the agent would see a real file that ends with a newline)."""
    assert _read_lines_from_source("a\nb\n", 1, 5) == "1: a\n2: b\n3: "


# ---------------------------------------------------------------------------
# Inverted / degenerate ranges -> empty selection
# ---------------------------------------------------------------------------


def test_inverted_range_empty_selection():
    """start > end yields an empty string (slice is empty), not an error."""
    assert _read_lines_from_source("a\nb\nc", 3, 1) == ""


def test_end_zero_empty_selection():
    """end=0 clamps to min(len, 0)=0; the slice [start-1:0] is empty."""
    assert _read_lines_from_source("a\nb\nc", 1, 0) == ""


# ---------------------------------------------------------------------------
# Empty source edge case
# ---------------------------------------------------------------------------


def test_empty_source():
    """An empty string splits to [""] (one empty line); the full range returns
    a single numbered empty line ``1: ``."""
    assert _read_lines_from_source("", 1, 5) == "1: "


# ---------------------------------------------------------------------------
# Off-by-one boundary: start == end (1-based INCLUSIVE single line)
# ---------------------------------------------------------------------------


def test_boundary_start_equals_end_inclusive():
    """start == end selects exactly ONE line (1-based inclusive), not zero
    lines -- the off-by-one that a half-open convention would get wrong."""
    assert _read_lines_from_source("a\nb", 1, 1) == "1: a"


def test_boundary_start_equals_end_mid_source():
    """Same inclusivity check mid-source: start=end=2 returns only line 2."""
    assert _read_lines_from_source("a\nb\nc\nd", 2, 2) == "2: b"


# ---------------------------------------------------------------------------
# Parametrized sanity sweep over a fixed 5-line source
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    "start,end,expected",
    [
        (1, 1, "1: a"),
        (1, 5, "1: a\n2: b\n3: c\n4: d\n5: e"),
        (3, 3, "3: c"),
        (2, 5, "2: b\n3: c\n4: d\n5: e"),
        (5, 9, "5: e"),  # end clamped to 5
        (0, 2, "1: a\n2: b"),  # start clamped to 1
    ],
)
def test_parametrized_sweep(start, end, expected):
    """Sweep over a fixed 5-line source pinning clamping + inclusivity + prefix
    in one parametrized table for fast regression triage."""
    assert _read_lines_from_source("a\nb\nc\nd\ne", start, end) == expected
