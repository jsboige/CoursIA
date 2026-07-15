#!/usr/bin/env python3
"""Tests for check_i18n_siblings.py (Lean i18n #4980 sibling byte-identity).

Dual-mode: runnable directly (``python scripts/lean/tests/test_check_i18n_siblings.py``)
or under pytest (auto-collected by scripts-tests.yml on any ``scripts/**`` change).
"""
from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from check_i18n_siblings import (  # noqa: E402
    check_pair,
    find_en_files,
    fr_sibling,
    normalize_body,
    strip_comments,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
CONWAY_DIR = (
    REPO_ROOT
    / "MyIA.AI.Notebooks" / "SymbolicAI" / "Lean" / "conway_lean" / "Conway"
)


def test_strip_comments_removes_block_line_and_docstring():
    src = (
        '/-- doc -/\n'
        'def f := 1 -- trailing comment\n'
        '/- multi\nline block -/\n'
        'def g := 2\n'
    )
    out = strip_comments(src)
    assert "doc" not in out
    assert "trailing comment" not in out
    assert "multi" not in out and "block" not in out
    assert "def f := 1" in out
    assert "def g := 2" in out


def test_strip_comments_nested_block():
    src = "/- outer /- inner -/ still outer -/def h := 3\n"
    out = strip_comments(src)
    assert "outer" not in out and "inner" not in out
    assert "def h := 3" in out


def test_strip_comments_preserves_string_with_double_dash():
    # A "--" inside a string literal must NOT be treated as a line comment.
    src = 'def s := "a -- b"\ndef t := 4\n'
    out = strip_comments(src)
    assert '"a -- b"' in out
    assert "def t := 4" in out


def test_normalize_drops_structural_lines():
    fr = (
        "import Mathlib.Data.List.Basic\n"
        "namespace Conway\n"
        "def f (n : Nat) := n + 1\n"
        "end Conway\n"
    )
    en = (
        "import Conway.Foo\n"
        "namespace Conway_en\n"
        "open Conway\n"
        "def f (n : Nat) := n + 1\n"
        "end Conway_en\n"
    )
    assert normalize_body(fr) == normalize_body(en)


def test_normalize_ignores_docstring_language():
    fr = "/-- Additionne un. -/\ndef f (n : Nat) := n + 1\n"
    en = "/-- Adds one. -/\ndef f (n : Nat) := n + 1\n"
    assert normalize_body(fr) == normalize_body(en)


def test_normalize_preserves_indentation_drift():
    # Tactic-block indentation is meaningful; a real indentation change must show.
    a = "theorem t : True := by\n  trivial\n"
    b = "theorem t : True := by\n    trivial\n"
    assert normalize_body(a) != normalize_body(b)


def test_normalize_collapses_en_suffix_variant():
    # prefixed-suffix variant (game_theory_lean): EN refers to `_en`-suffixed
    # entities; body must still compare equal to the FR canonical.
    fr = "def Efficiency (G : TUGame N) : Prop := G.v = 0\n"
    en = "def Efficiency (G : TUGame_en N) : Prop := G.v = 0\n"
    assert normalize_body(fr) == normalize_body(en)


def test_normalize_en_suffix_does_not_mask_real_drift():
    fr = "def f (G : TUGame N) : Nat := 42\n"
    en = "def f (G : TUGame_en N) : Nat := 43\n"
    assert normalize_body(fr) != normalize_body(en)


def test_check_pair_matching(tmp_path):
    fr = tmp_path / "Foo.lean"
    en = tmp_path / "Foo_en.lean"
    fr.write_text(
        "/-- Le module français. -/\n"
        "namespace Conway\n"
        "def answer : Nat := 42\n"
        "end Conway\n",
        encoding="utf-8",
    )
    en.write_text(
        "/-- The English mirror. -/\n"
        "import Conway.Foo\n"
        "namespace Conway_en\n"
        "open Conway\n"
        "def answer : Nat := 42\n"
        "end Conway_en\n",
        encoding="utf-8",
    )
    ok, diff = check_pair(fr, en)
    assert ok, diff


def test_check_pair_drift_detected(tmp_path):
    fr = tmp_path / "Bar.lean"
    en = tmp_path / "Bar_en.lean"
    fr.write_text("namespace Conway\ndef answer : Nat := 42\nend Conway\n",
                  encoding="utf-8")
    en.write_text("namespace Conway_en\ndef answer : Nat := 43\nend Conway_en\n",
                  encoding="utf-8")
    ok, diff = check_pair(fr, en)
    assert not ok
    assert "42" in diff and "43" in diff


def test_fr_sibling_naming(tmp_path):
    en = tmp_path / "Widget_en.lean"
    assert fr_sibling(en).name == "Widget.lean"


def test_find_en_files_skips_excluded(tmp_path):
    good = tmp_path / "Good_en.lean"
    good.write_text("x", encoding="utf-8")
    lake = tmp_path / ".lake" / "packages" / "Vendored_en.lean"
    lake.parent.mkdir(parents=True)
    lake.write_text("x", encoding="utf-8")
    found = {p.name for p in find_en_files([tmp_path])}
    assert "Good_en.lean" in found
    assert "Vendored_en.lean" not in found


def test_real_conway_pairs_are_byte_identical():
    """The merged conway_lean rollout must stay clean — regression guard."""
    if not CONWAY_DIR.is_dir():
        return  # tree not present in this checkout; skip silently
    en_files = find_en_files([CONWAY_DIR])
    assert en_files, "expected conway_lean *_en.lean pairs to exist"
    failures = []
    for en in en_files:
        fr = fr_sibling(en)
        if not fr.exists():
            failures.append(f"ORPHAN {en.name}")
            continue
        ok, diff = check_pair(fr, en)
        if not ok:
            failures.append(f"DRIFT {en.name}\n{diff}")
    assert not failures, "\n".join(failures)


def _run_direct() -> int:
    import tempfile

    passed = 0
    for name, fn in sorted(globals().items()):
        if not name.startswith("test_") or not callable(fn):
            continue
        argcount = fn.__code__.co_argcount
        try:
            if argcount == 0:
                fn()
            else:
                with tempfile.TemporaryDirectory() as d:
                    fn(Path(d))
            print(f"PASS {name}")
            passed += 1
        except AssertionError as exc:
            print(f"FAIL {name}: {exc}")
            return 1
    print(f"\n{passed} tests passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(_run_direct())
