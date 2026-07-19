"""Tests for ``lean_notebook_utils.count_sorry`` + ``_strip_lean_comments``.

Regression coverage for the fix to issue #7414: ``count_sorry`` previously ran
a bare ``grep -rc sorry --include=*.lean`` that counted ``sorry`` everywhere
(including docstrings ``/- ... -/`` and line comments ``-- ...``), contradicting
its own docstring which claimed to exclude comments. The fix rewrites it as a
pure-Python pass that strips comments first (mirroring the canonical
``agent_tests/prover/lean_utils.py:strip_lean_comments`` FX-6 #1453) then counts
word-bounded ``sorry``.

These tests are hermetic (synthetic ``.lean`` files in ``tmp_path``); no real
Lake project is required. CPU-only, stdlib + pytest.

Run with: pytest MyIA.AI.Notebooks/SymbolicAI/Lean/scripts/tests/test_count_sorry.py -v
"""

from __future__ import annotations

import os
import sys
from pathlib import Path

import pytest

# Module under test: SymbolicAI/Lean/lean_notebook_utils.py
# This test:        SymbolicAI/Lean/scripts/tests/test_count_sorry.py
# (3 levels up from tests/ -> scripts/ -> Lean/)
_LEAN_DIR = Path(__file__).resolve().parent.parent.parent
sys.path.insert(0, str(_LEAN_DIR))

import lean_notebook_utils as L  # noqa: E402


# --------------------------------------------------------------------------- #
#  _strip_lean_comments                                                        #
# --------------------------------------------------------------------------- #

class TestStripLeanComments:
    """_strip_lean_comments must mirror the canonical prover strip_lean_comments."""

    def test_line_comment_removed(self):
        assert L._strip_lean_comments("code -- a sorry comment") == "code "

    def test_block_comment_removed(self):
        assert L._strip_lean_comments("/- sorry block -/ code") == " code"

    def test_nested_block_comment_removed(self):
        # Lean allows nested /- -/ blocks.
        src = "nested /- /- sorry inner -/ sorry outer -/ ok"
        assert L._strip_lean_comments(src) == "nested  ok"

    def test_multiline_block_comment_removed(self):
        src = "/- multi\nline sorry block\nhere -/\nsorry"
        assert L._strip_lean_comments(src) == "\nsorry"

    def test_trailing_inline_comment_keeps_sorry_before_it(self):
        # `sorry -- comment` : the tactic is real, only the comment is stripped.
        assert L._strip_lean_comments("sorry -- trailing") == "sorry "

    def test_no_comments_preserved(self):
        assert L._strip_lean_comments("theorem x : True := by sorry") == \
            "theorem x : True := by sorry"

    def test_empty(self):
        assert L._strip_lean_comments("") == ""

    def test_line_comment_keeps_newline(self):
        # The newline after a -- comment is kept (so line structure survives).
        assert L._strip_lean_comments("-- a\nsorry") == "\nsorry"

    def test_unclosed_block_comment_strips_to_end(self):
        # An unterminated /- block swallows the rest (char-scan semantics).
        assert L._strip_lean_comments("ok /- never closed sorry") == "ok "


# --------------------------------------------------------------------------- #
#  count_sorry — the #7414 fix                                                 #
# --------------------------------------------------------------------------- #

class TestCountSorry:
    """count_sorry counts REAL sorry tactics, ignoring prose in comments."""

    def test_one_real_sorry(self, tmp_path):
        (tmp_path / "A.lean").write_text(
            "theorem t : True := by sorry\n", encoding="utf-8")
        assert L.count_sorry(str(tmp_path)) == 1

    def test_sorry_in_block_comment_not_counted(self, tmp_path):
        (tmp_path / "A.lean").write_text(
            "/- This docstring mentions sorry as an example. -/\n"
            "theorem t : True := trivial\n", encoding="utf-8")
        assert L.count_sorry(str(tmp_path)) == 0

    def test_sorry_in_line_comment_not_counted(self, tmp_path):
        (tmp_path / "A.lean").write_text(
            "-- TODO: replace sorry later\n"
            "theorem t : True := trivial\n", encoding="utf-8")
        assert L.count_sorry(str(tmp_path)) == 0

    def test_regression_prose_and_real_mixed(self, tmp_path):
        """The #7414 bug: prose sorry in comments must not inflate the count.
        Before the fix, grep -rc counted 3 here (docstring + comment + real).
        After the fix, only the 1 real tactic is counted."""
        (tmp_path / "A.lean").write_text(
            "/- module has sorry in its docstring narrative -/\n"
            "-- the word sorry appears in this comment too\n"
            "theorem t : True := by sorry\n", encoding="utf-8")
        assert L.count_sorry(str(tmp_path)) == 1

    def test_multiple_real_sorries_across_files(self, tmp_path):
        (tmp_path / "A.lean").write_text("theorem a : True := by sorry\n", encoding="utf-8")
        (tmp_path / "B.lean").write_text(
            "theorem b : True := by sorry\ntheorem c : True := by sorry\n",
            encoding="utf-8")
        assert L.count_sorry(str(tmp_path)) == 3

    def test_all_sorry_forms_caught_after_strip(self, tmp_path):
        """Word-bounded \\bsorry\\b catches every real tactic form."""
        (tmp_path / "A.lean").write_text(
            "theorem a : True := sorry\n"          # bare sorry
            "theorem b : True := by sorry\n"       # by sorry
            "theorem c : True := exact sorry\n"    # exact sorry
            "theorem d : True := sorry -- inline\n",  # sorry + inline comment
            encoding="utf-8")
        assert L.count_sorry(str(tmp_path)) == 4

    def test_word_boundary_not_substring(self, tmp_path):
        # "sorries" / "sorryFree" / "unsorry" must NOT match \bsorry\b on both sides.
        (tmp_path / "A.lean").write_text(
            "/- the sorries list -/\n-- unsorry check\n"
            "def sorryFree := 0\n", encoding="utf-8")
        assert L.count_sorry(str(tmp_path)) == 0

    def test_non_lean_files_ignored(self, tmp_path):
        (tmp_path / "A.lean").write_text("theorem t : True := by sorry\n", encoding="utf-8")
        (tmp_path / "notes.txt").write_text("sorry sorry sorry\n", encoding="utf-8")
        (tmp_path / "B.py").write_text("sorry = 1\n", encoding="utf-8")
        assert L.count_sorry(str(tmp_path)) == 1

    def test_empty_directory(self, tmp_path):
        assert L.count_sorry(str(tmp_path)) == 0

    def test_missing_directory_returns_minus_one(self, tmp_path):
        missing = str(tmp_path / "does_not_exist")
        assert L.count_sorry(missing) == -1

    def test_lake_cache_skipped(self, tmp_path):
        """``.lake`` (build cache / vendored Mathlib source) must not be counted."""
        (tmp_path / "Real.lean").write_text("theorem r : True := by sorry\n", encoding="utf-8")
        lake = tmp_path / ".lake" / "packages" / "Mathlib" / "Mathlib"
        lake.mkdir(parents=True)
        # 99 "sorry" inside the cache — must be ignored.
        (lake / "Junk.lean").write_text("sorry " * 99, encoding="utf-8")
        assert L.count_sorry(str(tmp_path)) == 1

    def test_subdir_scoped(self, tmp_path):
        (tmp_path / "A.lean").write_text("theorem a : True := by sorry\n", encoding="utf-8")
        sub = tmp_path / "Sub"
        sub.mkdir()
        (sub / "B.lean").write_text(
            "theorem b : True := by sorry\ntheorem c : True := by sorry\n",
            encoding="utf-8")
        # subdir "Sub" -> only B.lean's 2 sorries.
        assert L.count_sorry(str(tmp_path), "Sub") == 2

    def test_recurses_into_nested_dirs(self, tmp_path):
        deep = tmp_path / "a" / "b" / "c"
        deep.mkdir(parents=True)
        (deep / "Deep.lean").write_text("theorem t : True := by sorry\n", encoding="utf-8")
        assert L.count_sorry(str(tmp_path)) == 1


# --------------------------------------------------------------------------- #
#  Cross-check against the canonical prover counter (defense against drift)    #
# --------------------------------------------------------------------------- #

class TestCanonicalParity:
    """count_sorry must agree with the canonical count_real_sorries semantics.

    If this test fails, the local _strip_lean_comments has drifted from the
    canonical ``agent_tests/prover/lean_utils.py:strip_lean_comments`` (FX-6).
    """

    @pytest.fixture
    def prover(self):
        prover_path = (_LEAN_DIR / "agent_tests" / "prover" / "lean_utils.py")
        if not prover_path.is_file():
            pytest.skip("canonical prover lean_utils.py not present")
        import importlib.util
        spec = importlib.util.spec_from_file_location("_prover_lean_utils", prover_path)
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        return mod

    @pytest.mark.parametrize("src", [
        "/- sorry -/ code sorry",
        "-- sorry\nsorry",
        "nested /- /- sorry -/ -/ ok",
        "sorry -- trailing",
        "no sorry here",
        "/- multi\nline sorry block -/\nsorry",
        "theorem x : True := by sorry  -- real",
    ])
    def test_strip_identical_to_canonical(self, prover, src):
        assert L._strip_lean_comments(src) == prover.strip_lean_comments(src)

    def test_count_matches_canonical_on_synthetic_project(self, prover, tmp_path):
        """count_sorry(project) must equal the sum of count_real_sorries(file)
        over the project's .lean source — the shared contract."""
        files = {
            "A.lean": "/- sorry doc -/\ntheorem a : True := by sorry\n",
            "B.lean": "-- sorry\ntheorem b : True := sorry\ntheorem c : True := by sorry\n",
        }
        for name, content in files.items():
            (tmp_path / name).write_text(content, encoding="utf-8")
        expected = sum(prover.count_real_sorries(c) for c in files.values())
        assert L.count_sorry(str(tmp_path)) == expected


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
