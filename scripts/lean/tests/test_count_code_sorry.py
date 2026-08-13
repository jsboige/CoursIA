#!/usr/bin/env python3
"""Tests for count_code_sorry.py -- the real-sorry counter + vacuous detector.

Dual-mode: runnable directly or under pytest (auto-collected by scripts-tests.yml).
Covers the two organ responsibilities cited in #10188:

1. ``sorry`` in comments/prose is NOT counted; ``sorry`` in code IS counted and
   attributed to its enclosing declaration.
2. vacuous conclusions (``: True``, ``∃ ..., True``) are flagged; legit
   ``a = True`` and ``True -> True`` are NOT (low false-positive by design).
3. ``_en`` i18n mirrors are excluded from the *distinct* count.
4. ``*_prerequisites`` markers are tagged so the strict gate ignores them.
"""
from __future__ import annotations

import sys
import textwrap
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from count_code_sorry import (  # noqa: E402
    _VACUOUS_RE,
    main,
    scan_file,
    strip_lean_comments,
)


def _write(tmp_path: Path, name: str, body: str) -> Path:
    """Write a .lean snippet to the test's tmp_path and return its path."""
    f = tmp_path / name
    f.write_text(body, encoding="utf-8")
    return f


# --------------------------------------------------------------------------- #
# strip_lean_comments
# --------------------------------------------------------------------------- #

def test_strip_line_comment(tmp_path: Path) -> None:
    src = "theorem foo : True := by\n  -- sorry in comment\n  trivial"
    assert "sorry" not in strip_lean_comments(src)


def test_strip_block_comment_nested() -> None:
    # Lean nests block comments: /- outer -/ ... -/ is NOT a close inside outer.
    src = "/- outer /- inner sorry -/ still outer sorry -/\ntheorem foo : True := by trivial"
    stripped = strip_lean_comments(src)
    assert "sorry" not in stripped
    # The theorem line survives (only comment chars blanked).
    assert "theorem foo" in stripped


def test_strip_preserves_newlines_for_line_numbers() -> None:
    src = "a\n-- comment line\nb"
    stripped = strip_lean_comments(src)
    assert stripped.count("\n") == src.count("\n")


def test_dash_dash_inside_string_is_not_a_comment() -> None:
    src = 'def s := "-- not a comment sorry"\n-- real comment sorry'
    stripped = strip_lean_comments(src)
    # The string sorry survives; the comment sorry is blanked.
    assert stripped.count("sorry") == 1


# --------------------------------------------------------------------------- #
# sorry counting + attribution
# --------------------------------------------------------------------------- #

def test_sorry_in_docstring_not_counted(tmp_path: Path) -> None:
    f = _write(tmp_path, "Foo.lean", textwrap.dedent("""\
        /- Docstring mentions sorry twice: sorry sorry -/
        theorem real_one (n : Nat) : n = n := by sorry
        -- prose: sorry in a line comment
        theorem no_sorry (n : Nat) : n + 0 = n := by rfl
        """))
    decls, naive, code = scan_file(f, f.parent)
    assert code == 1, f"only the code sorry should count: naive={naive} code={code}"
    assert naive >= 3, "naive grep counts the docstring + comment sorries"
    by_name = {d.name: d.sorry_count for d in decls}
    assert by_name.get("real_one") == 1
    assert by_name.get("no_sorry") == 0


# --------------------------------------------------------------------------- #
# vacuous detection -- the core low-FP heuristic
# --------------------------------------------------------------------------- #

def test_vacuous_single_line_true(tmp_path: Path) -> None:
    f = _write(tmp_path, "T.lean", "theorem t : True := by trivial\n")
    decls, _, _ = scan_file(f, f.parent)
    assert decls[0].is_vacuous


def test_vacuous_existential_true(tmp_path: Path) -> None:
    f = _write(tmp_path, "T.lean",
               "theorem t (n : Nat) : ∃ μ : Nat, True := by exact ⟨0, trivial⟩\n")
    decls, _, _ = scan_file(f, f.parent)
    assert decls[0].is_vacuous


def test_vacuous_multiline_existential_true(tmp_path: Path) -> None:
    f = _write(tmp_path, "T.lean", textwrap.dedent("""\
        theorem folk (g : Nat) :
            ∃ (d : Nat), d < 1 ∧
              ∃ (s : Nat), True := by
          sorry
        """))
    decls, _, _ = scan_file(f, f.parent)
    assert decls[0].is_vacuous, "multiline ∃ ..., True must be flagged"
    assert decls[0].sorry_count == 1


def test_NOT_vacuous_equality_with_true(tmp_path: Path) -> None:
    # ``a = True`` is an equation, not an empty conclusion: char before True is '='.
    f = _write(tmp_path, "T.lean", "theorem t (a : Prop) [Decidable a] : a = True := by sorry\n")
    decls, _, _ = scan_file(f, f.parent)
    assert not decls[0].is_vacuous


def test_NOT_vacuous_true_arrow_true(tmp_path: Path) -> None:
    # ``True -> True`` is trivial-but-meaningful as a function type.
    f = _write(tmp_path, "T.lean", "theorem t : True -> True := by intro h; exact h\n")
    decls, _, _ = scan_file(f, f.parent)
    assert not decls[0].is_vacuous


def test_marker_prerequisites_tagged(tmp_path: Path) -> None:
    f = _write(tmp_path, "T.lean", "theorem foo_prerequisites : True := by trivial\n")
    decls, _, _ = scan_file(f, f.parent)
    assert decls[0].is_vacuous is True        # still detected (advisory)
    assert decls[0].is_marker is True          # but tagged -- strict gate skips it


def test_regex_unit_directly() -> None:
    # Direct regex contract: anchored at end, preceded by ':' or ','.
    assert _VACUOUS_RE.search("theorem t : True")
    assert _VACUOUS_RE.search("∃ μ, True")
    assert not _VACUOUS_RE.search("a = True")
    assert not _VACUOUS_RE.search("True -> True")


# --------------------------------------------------------------------------- #
# _en mirror distinct-count
# --------------------------------------------------------------------------- #

def test_en_mirrors_excluded_from_distinct(tmp_path: Path) -> None:
    lake = tmp_path / "fake_lean"
    lake.mkdir()
    (lake / "lakefile.lean").write_text("", encoding="utf-8")
    (lake / "Foo.lean").write_text("theorem a : True := by sorry\n", encoding="utf-8")
    (lake / "Foo_en.lean").write_text("theorem a : True := by sorry\n", encoding="utf-8")
    from count_code_sorry import scan_lake
    r = scan_lake(lake, tmp_path)
    assert r.code_sorry == 2          # both files have one code sorry
    assert r.code_sorry_en_mirrors == 1
    assert r.distinct_code_sorry == 1  # the _en mirror is a translation sibling


# --------------------------------------------------------------------------- #
# CLI smoke (default exit 0; --strict exit 1 on vacuous non-marker)
# --------------------------------------------------------------------------- #

def _make_demo_lake(tmp_path: Path, decl: str) -> Path:
    repo = tmp_path / "repo"
    lake = repo / "MyIA.AI.Notebooks" / "demo_lean"
    lake.mkdir(parents=True)
    (lake / "lakefile.lean").write_text("", encoding="utf-8")
    (lake / "D.lean").write_text(decl, encoding="utf-8")
    return repo


def test_cli_smoke_default_exit_zero(tmp_path: Path) -> None:
    repo = _make_demo_lake(tmp_path, "theorem a : True := by trivial\n")
    rc = main(["--repo", str(repo)])
    assert rc == 0, "default mode is advisory -> exit 0 even with a vacuous theorem"


def test_cli_strict_exit_one_on_vacuous_non_marker(tmp_path: Path) -> None:
    repo = _make_demo_lake(tmp_path, "theorem a : True := by trivial\n")
    rc = main(["--repo", str(repo), "--strict"])
    assert rc == 1, "strict mode fires on a vacuous non-marker theorem"


def test_cli_strict_exit_zero_when_only_markers(tmp_path: Path) -> None:
    repo = _make_demo_lake(tmp_path, "theorem foo_prerequisites : True := by trivial\n")
    rc = main(["--repo", str(repo), "--strict"])
    assert rc == 0, "markers are assumed-legit -> strict does not fire"


if __name__ == "__main__":
    import pytest
    sys.exit(pytest.main([__file__, "-v"]))
