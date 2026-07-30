"""Regression suite for ``scripts/lean/check_i18n_siblings.py`` (#4980, #6711).

Background. ``check_i18n_siblings.py`` is the daily-driver i18n checker for the
Lean FR/EN sibling-pair convention (EPIC #4980, Pattern A): ``Foo.lean`` FR
canonical + ``Foo_en.lean`` EN mirror, with docstrings ``/- -/`` differing and
signatures/proofs byte-identical. Its verdicts (``OK`` / ``OK-CONSUMER`` /
``DRIFT`` / ``ORPHAN`` / ``UNBUILT`` / ``HALF-DONE`` advisory) gate every Lean
i18n PR in this lane, yet the core helpers had ZERO unit tests -- a regression
risk for the comment-stripping, suffix-collapsing and consumer-pattern logic
that one bad edit to a single regex could silently invert on every lake.

This suite covers the pure helpers that the verdicts reduce to:

  * ``strip_comments`` : block/docstring comment stripping (nesting-aware),
    ``--`` line-comment removal, string-literal preservation.
  * ``extract_block_comment_bodies`` : the complement of ``strip_comments`` --
    returns the prose bodies for the ``HALF-DONE`` advisory verbatim-match
    detection.
  * ``is_half_done`` : byte-identical verbatim body detection (threshold
    ``min_body_chars``), empty-side and below-threshold edges.
  * ``normalize_body`` : ``_en`` suffix collapse, structural-line drop, and
    self-qualifier / ``_root_.`` erasure (the Arrow_en/#6716 FP fix).
  * ``imports_fr_sibling`` : consumer-pattern detection from import lines.
  * ``split_decls`` : top-level block splitting with attribute attachment.
  * ``check_pair`` : the three status verdicts (``OK`` / ``OK-CONSUMER`` /
    ``DRIFT``) and the consumer-variant ``DRIFT`` sub-case.

G.9 non-vacuous : the assertions are pinned to exact normalized outputs and
status strings, not just truthiness. A reverted ``_en``-collapse, a broken
nesting counter, or a swapped consumer subset direction would fail concrete
assertions here rather than silently mis-verdicting a sibling pair in CI.

Run: ``python -m pytest scripts/tests/test_check_i18n_siblings.py -q``
"""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts" / "lean"))

import check_i18n_siblings as C  # noqa: E402


# --- strip_comments -------------------------------------------------------

def test_strip_comments_block_comment():
    # A regular block comment is removed; surrounding code and the newline survive.
    out = C.strip_comments("def x := 1 /- removed -/\n")
    assert out == "def x := 1 \n"


def test_strip_comments_docstring():
    # A docstring /-- ... -/ is a block comment; stripped the same way.
    out = C.strip_comments("/-- doc -/\ndef x := 1\n")
    assert out == "\ndef x := 1\n"


def test_strip_comments_nested_block():
    # Block comments nest in Lean; the nesting counter must balance both markers.
    out = C.strip_comments("/- outer /- inner -/ still outer -/\ncode\n")
    # The whole nested region is gone; its newline is preserved (line structure).
    assert out == "\ncode\n"


def test_strip_comments_line_comment():
    # -- to end of line is dropped; the trailing newline is kept for line parity.
    out = C.strip_comments("def x := 1 -- inline\n")
    assert out == "def x := 1 \n"


def test_strip_comments_preserves_string_literal():
    # "--" inside a "..." literal must NOT be parsed as a line comment.
    out = C.strip_comments('def s := "a -- b" rest\n')
    assert '"a -- b"' in out
    assert "rest" in out


def test_strip_comments_preserves_block_marker_in_string():
    # "/- ... -/" inside a string literal must NOT open/close a block comment.
    out = C.strip_comments('def s := "/- not a comment -/" tail\n')
    assert "/- not a comment -/" in out
    assert "tail" in out


# --- extract_block_comment_bodies ----------------------------------------

def test_extract_bodies_single_block():
    bodies = C.extract_block_comment_bodies("/- hello -/\ncode\n")
    assert bodies == [" hello "]


def test_extract_bodies_docstring_delimiters_stripped():
    # /-- opens with two hyphens; the body starts after them so the mirror's
    # doc style can differ from the canonical.
    bodies = C.extract_block_comment_bodies("/-- docstring body -/\ncode\n")
    assert bodies == [" docstring body "]


def test_extract_bodies_multiple_in_source_order():
    bodies = C.extract_block_comment_bodies("/- first -/\ncode\n/- second -/\n")
    assert bodies == [" first ", " second "]


def test_extract_bodies_nested_skipped():
    # The outer body absorbs the nested region verbatim (nesting-aware scan).
    bodies = C.extract_block_comment_bodies("/- outer /- inner -/ tail -/\n")
    assert bodies == [" outer /- inner -/ tail "]


def test_extract_bodies_empty_when_none():
    assert C.extract_block_comment_bodies("def x := 1\n") == []


# --- is_half_done --------------------------------------------------------

# A body comfortably above the default 100-char threshold.
_LONG_BODY = "/-" + ("x" * 120) + "-/"


def test_is_half_done_detects_identical(tmp_path):
    fr = tmp_path / "Foo.lean"
    en = tmp_path / "Foo_en.lean"
    fr.write_text(_LONG_BODY + "\ndef x := 1\n", encoding="utf-8")
    en.write_text(_LONG_BODY + "\ndef x := 1\n", encoding="utf-8")
    flagged, n = C.is_half_done(fr, en)
    assert flagged is True
    assert n == 1


def test_is_half_done_below_threshold_not_flagged(tmp_path):
    short = "/-" + ("y" * 50) + "-/"  # body below the 100-char threshold
    fr = tmp_path / "Foo.lean"
    en = tmp_path / "Foo_en.lean"
    fr.write_text(short + "\ncode\n", encoding="utf-8")
    en.write_text(short + "\ncode\n", encoding="utf-8")
    flagged, n = C.is_half_done(fr, en)
    assert flagged is False
    assert n == 0


def test_is_half_done_distinct_bodies_not_flagged(tmp_path):
    fr = tmp_path / "Foo.lean"
    en = tmp_path / "Foo_en.lean"
    fr.write_text("/-" + ("a" * 120) + "-/\n", encoding="utf-8")
    en.write_text("/-" + ("b" * 120) + "-/\n", encoding="utf-8")
    flagged, n = C.is_half_done(fr, en)
    assert flagged is False
    assert n == 0


def test_is_half_done_empty_side_not_flagged(tmp_path):
    # No block comments at all -> empty bodies list -> short-circuits to (False, 0).
    fr = tmp_path / "Foo.lean"
    en = tmp_path / "Foo_en.lean"
    fr.write_text("def x := 1\n", encoding="utf-8")
    en.write_text("def x := 1\n", encoding="utf-8")
    flagged, n = C.is_half_done(fr, en)
    assert flagged is False
    assert n == 0


# --- normalize_body ------------------------------------------------------

def test_normalize_body_drops_structural_and_comments():
    src = ("import Mathlib\n"
           "open scoped Classical\n"
           "namespace Bar\n"
           "/- a block comment -/\n"
           "def x := 1\n"
           "end Bar\n")
    out = C.normalize_body(src)
    assert "import" not in out
    assert "open scoped Classical" not in out
    assert "namespace Bar" not in out
    assert "end Bar" not in out
    assert "block comment" not in out
    assert "def x := 1" in out


def test_normalize_body_collapses_en_suffix():
    # _en suffix on identifiers collapsed (symmetric on both files).
    src = "theorem TUGame_en : True := by trivial\n"
    out = C.normalize_body(src)
    assert "_en" not in out
    assert "TUGame" in out  # TUGame_en -> TUGame


def test_normalize_body_erases_root_qualifier():
    src = "theorem t : _root_.True := by trivial\n"
    out = C.normalize_body(src)
    assert "_root_." not in out
    assert "True" in out


def test_normalize_body_erases_self_qualifier():
    # A namespace declared in-file -> references qualified by it are neutral and
    # erased; this is the Arrow_en/#6716 false-positive fix.
    src = ("namespace Conway\n"
           "theorem t : Conway.True := by trivial\n"
           "end Conway\n")
    out = C.normalize_body(src)
    assert "Conway.True" not in out  # self-qualifier erased
    assert "True" in out


# --- imports_fr_sibling --------------------------------------------------

def test_imports_fr_sibling_simple_module():
    assert C.imports_fr_sibling("import Foo\n", "Foo") is True


def test_imports_fr_sibling_dotted_module():
    # The FR stem is the last dotted segment.
    assert C.imports_fr_sibling("import Conway.Life.Foo\n", "Foo") is True


def test_imports_fr_sibling_no_match():
    assert C.imports_fr_sibling("import Mathlib\nimport Bar\n", "Foo") is False


def test_imports_fr_sibling_empty():
    assert C.imports_fr_sibling("def x := 1\n", "Foo") is False


# --- split_decls ---------------------------------------------------------

def test_split_decls_separates_top_level():
    blocks = C.split_decls("def a := 1\ndef b := 2\n")
    assert blocks == ["def a := 1", "def b := 2"]


def test_split_decls_attaches_attribute():
    # A standalone @[attr] preceding a declaration stays attached to the block.
    blocks = C.split_decls("@[simp]\ntheorem t : True := by trivial\n")
    assert len(blocks) == 1
    assert "@[simp]" in blocks[0]
    assert "theorem t" in blocks[0]


def test_split_decls_empty_body():
    assert C.split_decls("") == []


# --- check_pair ----------------------------------------------------------

def test_check_pair_ok_identical_after_docstring_diff(tmp_path):
    fr = tmp_path / "Foo.lean"
    en = tmp_path / "Foo_en.lean"
    # Same code body; docstrings differ (stripped) -> bodies compare equal -> OK.
    fr.write_text("/-- doc en francais -/\ndef x := 1\n", encoding="utf-8")
    en.write_text("/-- doc in english -/\ndef x := 1\n", encoding="utf-8")
    status, detail = C.check_pair(fr, en)
    assert status == "OK"
    assert detail == ""


def test_check_pair_drift_en_has_extra_block(tmp_path):
    fr = tmp_path / "Foo.lean"
    en = tmp_path / "Foo_en.lean"
    # EN declares a block FR lacks, no consumer import -> DRIFT.
    fr.write_text("def a := 1\n", encoding="utf-8")
    en.write_text("def a := 1\ndef b := 2\n", encoding="utf-8")
    status, detail = C.check_pair(fr, en)
    assert status == "DRIFT"
    assert "only in EN" in detail
    assert "def b := 2" in detail


def test_check_pair_ok_consumer_subset(tmp_path):
    fr = tmp_path / "Foo.lean"
    en = tmp_path / "Foo_en.lean"
    # EN imports the FR module and re-states a subset of FR's declarations;
    # the rest is legitimately reused via the import -> OK-CONSUMER.
    fr.write_text("def a := 1\ndef b := 2\n", encoding="utf-8")
    en.write_text("import Foo\ndef a := 1\n", encoding="utf-8")
    status, detail = C.check_pair(fr, en)
    assert status == "OK-CONSUMER"
    assert "reused" in detail


def test_check_pair_consumer_drift_unmatched_block(tmp_path):
    fr = tmp_path / "Foo.lean"
    en = tmp_path / "Foo_en.lean"
    # EN imports FR but re-states a block FR does NOT have -> consumer-variant
    # DRIFT (distinct from the non-consumer DRIFT above).
    fr.write_text("def a := 1\n", encoding="utf-8")
    en.write_text("import Foo\ndef a := 1\ndef b := 2\n", encoding="utf-8")
    status, detail = C.check_pair(fr, en)
    assert status == "DRIFT"
    assert "def b" in detail
    assert "counterpart" in detail
