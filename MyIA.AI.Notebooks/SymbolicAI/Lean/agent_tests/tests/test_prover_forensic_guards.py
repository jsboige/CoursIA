"""Unit tests for the prover's forensic anti-gaming guards.

Locks in the pure helper guards that detect the two classic ways an
autonomous prover can *fake* progress instead of genuinely eliminating a
`sorry`:

  1. Axiom-cheat — closing a goal by introducing a fresh ``axiom``
     declaration (`_is_axiom_declaration` / `_count_axiom_declarations`).
     A single new axiom makes any statement provable for free, so the
     axiom count must never silently rise.
  2. Sorry-relocation — creating a new named ``lemma foo := by sorry`` and
     calling it to "close" an existing sorry, so the *local* sorry vanishes
     while the *global* sorry count is unchanged
     (`_find_sorry_definitions` / `_check_sorry_relocation`).

These pure helpers had zero direct coverage. This module is a regression
fence: the guards are the exact charter of the prover-robustness epic
(#1453), and a silent revert of either would let gamed proofs through the
harness undetected. Being pure functions (no LLM, no Lean build, no
network), they are deterministically unit-testable.

Run from `agent_tests/`:
    python -m pytest tests/test_prover_forensic_guards.py -q

See #6790 (prover harness robustness).
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

# Make `prover/` importable regardless of how pytest was invoked
# (mirrors tests/test_prover_guards.py).
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT))

from prover.tools import (  # noqa: E402
    _check_sorry_relocation,
    _count_axiom_declarations,
    _find_sorry_definitions,
    _is_axiom_declaration,
)


# ──────────────────────────────────────────────────────────────────────────
# Axiom-cheat guard — a fresh `axiom` declaration closes any goal for free
# ──────────────────────────────────────────────────────────────────────────


class TestIsAxiomDeclaration:
    def test_bare_axiom(self):
        assert _is_axiom_declaration("axiom foo") is True

    def test_axiom_with_prop(self):
        assert _is_axiom_declaration("axiom bar : Prop") is True

    def test_axiom_with_binders(self):
        assert _is_axiom_declaration("axiom baz (n : Nat) : n = n") is True

    def test_indented_axiom_allowed(self):
        # Leading whitespace is permitted by the `^\s*axiom` anchor.
        assert _is_axiom_declaration("  axiom indented : True") is True

    def test_theorem_is_not_axiom(self):
        assert _is_axiom_declaration("theorem foo : True := trivial") is False

    def test_commented_axiom_is_not_a_declaration(self):
        # A comment mentioning "axiom" must not count as a declaration.
        assert _is_axiom_declaration("-- axiom foo is used below") is False

    def test_axiom_substring_is_not_a_declaration(self):
        # `axiomatic_foo` begins with "axiom" but lacks the required
        # whitespace+word after the keyword, so `axiom\s+\w` must not match.
        assert _is_axiom_declaration("axiomatic_foo : Prop") is False

    def test_keyword_only_no_name(self):
        assert _is_axiom_declaration("axiom") is False


class TestCountAxiomDeclarations:
    def test_counts_multiple(self):
        content = (
            "axiom a : Prop\n"
            "theorem b : True := trivial\n"
            "axiom c : Prop"
        )
        assert _count_axiom_declarations(content) == 2

    def test_zero_when_none(self):
        content = "theorem t : True := trivial\ndef d := 1"
        assert _count_axiom_declarations(content) == 0

    def test_ignores_commented_axiom(self):
        content = "-- axiom sneaky : False\ntheorem t : True := trivial"
        assert _count_axiom_declarations(content) == 0


# ──────────────────────────────────────────────────────────────────────────
# Sorry-definition extraction — names of `lemma/def ... := by sorry`
# ──────────────────────────────────────────────────────────────────────────


class TestFindSorryDefinitions:
    def test_finds_lemma_sorry(self):
        assert _find_sorry_definitions("lemma helper := by sorry") == {"helper"}

    def test_finds_def_sorry(self):
        assert _find_sorry_definitions("def gadget := by sorry") == {"gadget"}

    def test_have_scaffolding_is_excluded(self):
        # `have h := by sorry` is legitimate inline decomposition, NOT a
        # relocation — the guard intentionally ignores it (documented in the
        # `_SORRY_DEF_RE` note).
        assert _find_sorry_definitions("have h := by sorry") == set()

    def test_theorem_sorry_is_not_a_relocation_def(self):
        # Only `lemma`/`def` count; a top-level theorem-with-sorry is the
        # goal under attack, not a relocation target.
        assert _find_sorry_definitions("theorem main := by sorry") == set()

    def test_non_sorry_lemma_ignored(self):
        assert _find_sorry_definitions("lemma proved := by simp") == set()

    def test_multiple_sorry_defs(self):
        content = (
            "lemma a := by sorry\n"
            "lemma b := by sorry\n"
            "lemma c := by simp"
        )
        assert _find_sorry_definitions(content) == {"a", "b"}


class TestFindSorryDefinitionsTypeAnnotated:
    """Type-annotated ``lemma``/``def`` with sorry — the common real-world form.

    `_SORRY_DEF_RE` was broadened from `(?:lemma|def)\\s+(\\w+)\\b[^:]*:=\\s*by`
    to `(?:lemma|def)\\s+(\\w+)\\b(?:[^:=]|:[^=])*?\\s*:=\\s*by` so it can span
    the type-annotation colon without swallowing the `:=` token. The fix was
    verified firsthand on 12 cases before commit (annotation only, nested
    binders `(n m : Nat)`, instance binders `[Monad m]`, type-class binders
    `{α : Type _}`, multi-line, `have`/`theorem` exclusion). The previous
    xfail (PR #6907) is flipped to a passing regression test by this PR.
    Follow-up to #6790 / closes the documented gap from #6907.
    """

    def test_type_annotated_lemma(self):
        assert _find_sorry_definitions("lemma foo : P := by sorry") == {"foo"}

    def test_type_annotated_def(self):
        assert _find_sorry_definitions("def bar : Nat := by sorry") == {"bar"}

    def test_binder_colons_in_signature(self):
        # Nested binders each contain a colon; the regex must allow them.
        assert (
            _find_sorry_definitions("lemma mul (n m : Nat) : Nat := by sorry")
            == {"mul"}
        )

    def test_instance_and_typeclass_binders(self):
        content = (
            "lemma foldl [Monad m] (n : Nat) : Nat := by sorry\n"
            "def mem_iff {α : Type _} (a : α) (as : List α) : Prop := by sorry"
        )
        assert _find_sorry_definitions(content) == {"foldl", "mem_iff"}

    def test_multiline_annotation(self):
        content = "lemma qux\n  : P\n  := by sorry"
        assert _find_sorry_definitions(content) == {"qux"}

    def test_implication_arrow_in_signature(self):
        # `→` is not a `:` or `=`, so the body segment handles it natively.
        assert _find_sorry_definitions("lemma baz : P → Q := by sorry") == {"baz"}


# ──────────────────────────────────────────────────────────────────────────
# Relocation guard — fresh sorry-lemma called to "close" an existing sorry
# ──────────────────────────────────────────────────────────────────────────


class TestCheckSorryRelocation:
    def test_detects_relocation(self):
        # A new `lemma helper := by sorry` appears AND is referenced by the
        # replacement that closed the original sorry → gamed progress.
        original = "theorem main := by sorry"
        new = "lemma helper := by sorry\ntheorem main := by exact helper"
        replaced = "exact helper"
        is_reloc, fresh, called = _check_sorry_relocation(new, original, replaced)
        assert is_reloc is True
        assert "helper" in fresh
        assert "helper" in called

    def test_fresh_sorry_def_not_called_is_not_relocation(self):
        # A new sorry-lemma exists but the replacement does not reference it,
        # so this edit is not itself a relocation; the fresh def is still
        # reported for visibility.
        original = "theorem main := by sorry"
        new = "lemma helper := by sorry\ntheorem main := by simp"
        replaced = "simp"
        is_reloc, fresh, called = _check_sorry_relocation(new, original, replaced)
        assert is_reloc is False
        assert fresh == {"helper"}
        assert called == set()

    def test_preexisting_sorry_def_is_not_fresh(self):
        # `helper` already carried a sorry in the original, so re-using it is
        # not a NEW relocation introduced by this edit.
        original = "lemma helper := by sorry\ntheorem main := by sorry"
        new = "lemma helper := by sorry\ntheorem main := by exact helper"
        replaced = "exact helper"
        is_reloc, fresh, called = _check_sorry_relocation(new, original, replaced)
        assert is_reloc is False
        assert fresh == set()
        assert called == set()

    def test_no_sorry_defs_at_all(self):
        original = "theorem main := by sorry"
        new = "theorem main := by simp"
        is_reloc, fresh, called = _check_sorry_relocation(new, original, "simp")
        assert is_reloc is False
        assert fresh == set()
        assert called == set()
