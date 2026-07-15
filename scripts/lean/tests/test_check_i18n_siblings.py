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
    imports_fr_sibling,
    normalize_body,
    split_decls,
    strip_comments,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
CONWAY_DIR = (
    REPO_ROOT
    / "MyIA.AI.Notebooks" / "SymbolicAI" / "Lean" / "conway_lean" / "Conway"
)
CONEKERNEL_EN = (
    REPO_ROOT / "MyIA.AI.Notebooks" / "GameTheory" / "game_theory_lean"
    / "CooperativeGames" / "ConeKernel_en.lean"
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
    status, detail = check_pair(fr, en)
    assert status == "OK", detail


def test_check_pair_drift_detected(tmp_path):
    fr = tmp_path / "Bar.lean"
    en = tmp_path / "Bar_en.lean"
    fr.write_text("namespace Conway\ndef answer : Nat := 42\nend Conway\n",
                  encoding="utf-8")
    en.write_text("namespace Conway_en\ndef answer : Nat := 43\nend Conway_en\n",
                  encoding="utf-8")
    status, detail = check_pair(fr, en)
    assert status == "DRIFT"
    assert "42" in detail and "43" in detail


def test_normalize_strips_self_qualifiers_arrow_fp():
    # Arrow_en/#6716 false-positive repro: FR defs at top level disambiguate
    # with `_root_.X`; the EN mirror lives in `namespace SocialChoice_en` and
    # must write `SocialChoice_en.X`. Same reference, two scopes.
    fr = (
        "def is_strictly_best (x : Nat) : Prop := x = 0\n"
        "theorem t (x : Nat) : Prop := _root_.is_strictly_best x\n"
    )
    en = (
        "namespace SocialChoice_en\n"
        "def is_strictly_best (x : Nat) : Prop := x = 0\n"
        "theorem t (x : Nat) : Prop := SocialChoice_en.is_strictly_best x\n"
        "end SocialChoice_en\n"
    )
    assert normalize_body(fr) == normalize_body(en)


def test_self_qualifier_does_not_mask_foreign_prefix():
    # A qualified reference to a namespace NOT declared in the file is body
    # content — it must still surface as drift.
    fr = "theorem t : Prop := Other.f 1\n"
    en = "theorem t : Prop := f 1\n"
    assert normalize_body(fr) != normalize_body(en)


def test_check_pair_consumer_pattern_lattice_fp(tmp_path):
    # Lattice_en false-positive repro: the EN sibling imports the FR canonical
    # module and reuses its defs (no redeclaration); only the theorems it does
    # state must match.
    fr = tmp_path / "Lattice.lean"
    en = tmp_path / "Lattice_en.lean"
    fr.write_text(
        "namespace StableMarriage\n"
        "def joinSpouse (x : Nat) : Nat := x + 1\n"
        "def meetSpouse (x : Nat) : Nat := x - 1\n"
        "theorem join_comm (x : Nat) : joinSpouse x = joinSpouse x := rfl\n"
        "end StableMarriage\n",
        encoding="utf-8",
    )
    en.write_text(
        "import StableMarriage.Lattice\n"
        "namespace StableMarriage_en\n"
        "open StableMarriage\n"
        "theorem join_comm (x : Nat) : joinSpouse x = joinSpouse x := rfl\n"
        "end StableMarriage_en\n",
        encoding="utf-8",
    )
    status, detail = check_pair(fr, en)
    assert status == "OK-CONSUMER", detail
    assert "2 FR declaration block(s) reused" in detail


def test_consumer_pattern_still_flags_novel_en_block(tmp_path):
    # An EN block with no FR counterpart is real drift even under the
    # consumer pattern.
    fr = tmp_path / "Cone.lean"
    en = tmp_path / "Cone_en.lean"
    fr.write_text(
        "namespace Cone\n"
        "theorem a : True := trivial\n"
        "end Cone\n",
        encoding="utf-8",
    )
    en.write_text(
        "import Cooperative.Cone\n"
        "namespace Cone_en\n"
        "theorem a : True := by exact trivial\n"
        "end Cone_en\n",
        encoding="utf-8",
    )
    status, detail = check_pair(fr, en)
    assert status == "DRIFT"
    assert "no FR counterpart" in detail


def test_check_pair_reordered_blocks_ok(tmp_path):
    # C521-L3 / ConeKernel #6727 repro: declaring the same top-level blocks in
    # a different order (the EN port inserted a lemma at a different site) is a
    # legitimate structural divergence, not drift — reordering to match FR has
    # already broken the build once (commit 6788d1d1f).
    fr = tmp_path / "Pair.lean"
    en = tmp_path / "Pair_en.lean"
    fr.write_text(
        "namespace Pair\n"
        "theorem a : True := trivial\n"
        "theorem b : True := trivial\n"
        "theorem c : True := trivial\n"
        "end Pair\n",
        encoding="utf-8",
    )
    en.write_text(
        "namespace Pair_en\n"
        "theorem a : True := trivial\n"
        "theorem c : True := trivial\n"
        "theorem b : True := trivial\n"
        "end Pair_en\n",
        encoding="utf-8",
    )
    status, detail = check_pair(fr, en)
    assert status == "OK-REORDERED", detail
    assert "3 declaration block(s)" in detail


def test_check_pair_real_drift_lists_unique_blocks(tmp_path):
    # A genuinely changed block is NOT OK-REORDERED; the detail lists the
    # blocks unique to each side (the changed block appears on both sides as
    # an old/new counterpart) — actionable diagnostic, cf #6727 step 3.
    fr = tmp_path / "Drift.lean"
    en = tmp_path / "Drift_en.lean"
    fr.write_text(
        "namespace Drift\n"
        "theorem a : True := trivial\n"
        "theorem b : True := trivial\n"
        "end Drift\n",
        encoding="utf-8",
    )
    en.write_text(
        "namespace Drift_en\n"
        "theorem a : True := trivial\n"
        "theorem b : Nat := 1\n"
        "end Drift_en\n",
        encoding="utf-8",
    )
    status, detail = check_pair(fr, en)
    assert status == "DRIFT"
    assert "only in FR" in detail
    assert "only in EN" in detail


def test_split_decls_attribute_line_starts_block():
    body = (
        "def f : Nat := 1\n"
        "@[simp]\n"
        "theorem t : True := trivial\n"
    )
    blocks = split_decls(body)
    assert len(blocks) == 2
    assert blocks[1].startswith("@[simp]")


def test_imports_fr_sibling_matches_last_segment():
    assert imports_fr_sibling("import StableMarriage.Lattice\n", "Lattice")
    assert not imports_fr_sibling("import StableMarriage.Defs\n", "Lattice")


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
        status, detail = check_pair(fr, en)
        if status == "DRIFT":
            failures.append(f"DRIFT {en.name}\n{detail}")
    assert not failures, "\n".join(failures)


def test_real_conekernel_pair_is_reordered_not_drift():
    """ConeKernel #6727 regression guard: the EN mirror declares the same 18
    blocks as the FR canonical in a different order (lemma inserted at a
    different site by port #6575). Must classify as OK-REORDERED, not DRIFT."""
    en = CONEKERNEL_EN
    fr = fr_sibling(en)
    if not en.is_file() or not fr.is_file():
        return  # tree not present in this checkout; skip silently
    status, detail = check_pair(fr, en)
    assert status == "OK-REORDERED", detail


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
