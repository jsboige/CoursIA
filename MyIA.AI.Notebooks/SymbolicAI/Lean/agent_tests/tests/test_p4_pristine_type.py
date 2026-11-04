"""Unit tests for the pristine elaborated-type control (#1453, track a).

Background. ``_evaluate_final_verify`` answers "does the file compile?". It
does not answer "is the theorem still the same theorem". A prover that
weakens a statement and then proves the weakened form reports a clean build
AND a lower ``sorry`` count, so every gate in the autonomous path stays
green while the delivered artefact proves a different proposition. FX-6
(``_stmt_mutation_guard``) catches the cruder shape -- a sorry drop with
zero build-verified tactic -- but a mutation that came WITH a verifying
tactic passes it.

The control is text-first: two byte-compares decide ``UNCHANGED`` (no
elaboration, the type is the same by construction), anything else escalates
to ``NEEDS_ELABORATION``, where the caller elaborates
``set_option pp.all true in #check @<decl>`` on both contents. The prefix
above the declaration counts as much as the statement itself: a local
``instance`` or ``notation`` inserted above changes how the very same
statement elaborates, so a statement-only comparison would be unsound for a
prover that edits the file it is proving in.

These tests load ``prover/p4_final_verify.py`` by file path, the same way
``test_p4_l1_false_negative.py`` does -- the module is stdlib-only by
design, and importing ``prover/__init__.py`` would drag the LLM stack.

The probes below are real Lean shapes taken from the lakes the harness runs
on (multi-line binders, ``:= by``, ``where`` clauses, ``:=`` inside a
parenthesised argument, comments containing ``:=``).
"""

from __future__ import annotations

import importlib.util
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent

_p4_spec = importlib.util.spec_from_file_location(
    "prover_p4_pristine_type", ROOT / "prover" / "p4_final_verify.py"
)
_p4 = importlib.util.module_from_spec(_p4_spec)
_p4_spec.loader.exec_module(_p4)

_declaration_span = _p4._declaration_span
_pristine_type_decision = _p4._pristine_type_decision
_pristine_type_probe = _p4._pristine_type_probe
_normalise_lean_text = _p4._normalise_lean_text


ORIGINAL = """import Mathlib

open Nat

theorem zero_add_smoke (n : Nat) : 0 + n = n := by
  sorry
"""


# --- span extraction ----------------------------------------------------


def test_span_single_line_statement_stops_at_assign():
    prefix, statement = _declaration_span(ORIGINAL, "zero_add_smoke")
    assert prefix.rstrip().endswith("open Nat"), (
        "The prefix is everything BEFORE the declaration keyword: that is "
        "the part whose instances and notation decide how the statement "
        "elaborates."
    )
    assert "theorem" not in prefix
    assert _normalise_lean_text(statement) == "(n : Nat) : 0 + n = n"


def test_span_multiline_statement_keeps_every_binder():
    content = (
        "theorem chain\n"
        "    (a b c : Nat)\n"
        "    (h1 : a = b)\n"
        "    (h2 : b = c) :\n"
        "    a = c := by\n"
        "  exact h1.trans h2\n"
    )
    prefix, statement = _declaration_span(content, "chain")
    normalised = _normalise_lean_text(statement)
    assert "(a b c : Nat)" in normalised
    assert "(h2 : b = c)" in normalised
    assert "a = c" in normalised
    assert ":=" not in normalised


def test_span_where_clause_ends_the_statement():
    content = (
        "theorem helper (n : Nat) : n = n where\n"
        "  foo := rfl\n"
    )
    _, statement = _declaration_span(content, "helper")
    assert ":=" not in _normalise_lean_text(statement).split("where")[0]


def test_span_assign_inside_parens_does_not_end_the_statement():
    """``:=`` nested in a parenthesised term belongs to the statement."""
    content = (
        "theorem with_default\n"
        "    (f : Nat -> Nat := fun x => x)\n"
        "    (n : Nat) : f n = n := by\n"
        "  rfl\n"
    )
    _, statement = _declaration_span(content, "with_default")
    normalised = _normalise_lean_text(statement)
    assert "(f : Nat -> Nat := fun x => x)" in normalised
    assert normalised.rstrip().endswith("f n = n")


def test_span_line_comment_assign_does_not_end_the_statement():
    """The comment's ``:=`` must not be taken for the body separator: if it
    were, the span would stop mid-statement and the control would compare
    two truncated fragments instead of the two statements."""
    content = (
        "theorem commented (n : Nat) :\n"
        "  -- historical shape was := by trivial\n"
        "  n = n := by\n"
        "  rfl\n"
    )
    _, statement = _declaration_span(content, "commented")
    assert "n = n" in _normalise_lean_text(statement), (
        "The span must run past the comment up to the real ':='."
    )


def test_span_block_comment_assign_does_not_end_the_statement():
    content = (
        "theorem blocked (n : Nat) :\n"
        "  /- old body: := by simpa -/\n"
        "  n = n := by\n"
        "  rfl\n"
    )
    _, statement = _declaration_span(content, "blocked")
    assert "n = n" in _normalise_lean_text(statement)


def test_span_name_prefix_is_not_matched():
    """``foo`` must not resolve to ``foo_bar``'s declaration."""
    content = (
        "theorem foo_bar (n : Nat) : n = n := by\n"
        "  rfl\n"
        "theorem foo (n : Nat) : n + 0 = n := by\n"
        "  simp\n"
    )
    _, statement = _declaration_span(content, "foo")
    assert "n + 0 = n" in _normalise_lean_text(statement)


def test_span_attribute_and_modifiers_are_tolerated():
    content = (
        "@[simp]\n"
        "private theorem attr_decl (n : Nat) : n = n := by\n"
        "  rfl\n"
    )
    prefix, statement = _declaration_span(content, "attr_decl")
    assert "@[simp]" in prefix
    assert "n = n" in _normalise_lean_text(statement)


# --- decision: UNCHANGED ------------------------------------------------


def test_decision_unchanged_when_contents_identical():
    decision = _pristine_type_decision(ORIGINAL, ORIGINAL, "zero_add_smoke")
    assert decision["status"] == "UNCHANGED"
    assert decision["probe"] is None


def test_decision_unchanged_when_only_body_changed():
    """The whole point of the control: a solved body is not a drift."""
    solved = ORIGINAL.replace("  sorry", "  exact Nat.zero_add n")
    decision = _pristine_type_decision(ORIGINAL, solved, "zero_add_smoke")
    assert decision["status"] == "UNCHANGED", (
        "Replacing the body must not escalate: the statement and the prefix "
        "are untouched, so the elaborated type is the same by construction."
    )


def test_decision_unchanged_when_only_body_changed_multiline():
    solved = ORIGINAL.replace("  sorry", "  induction n with\n  | zero => rfl\n  | succ k ih => simp")
    decision = _pristine_type_decision(ORIGINAL, solved, "zero_add_smoke")
    assert decision["status"] == "UNCHANGED"


# --- decision: NEEDS_ELABORATION ---------------------------------------


def test_decision_flags_weakened_statement():
    """``True`` conjunct: the classical way to prove nothing."""
    weakened = ORIGINAL.replace(": 0 + n = n :=", ": 0 + n = n /\\ True :=")
    decision = _pristine_type_decision(ORIGINAL, weakened, "zero_add_smoke")
    assert decision["status"] == "NEEDS_ELABORATION"
    assert decision["statement_drifted"] is True
    assert decision["prefix_drifted"] is False
    assert "True" in decision["current_statement"]
    assert decision["probe"] == "set_option pp.all true in\n#check @zero_add_smoke\n"


def test_decision_flags_dropped_binder():
    dropped = ORIGINAL.replace("(n : Nat)", "(n : Int)")
    decision = _pristine_type_decision(ORIGINAL, dropped, "zero_add_smoke")
    assert decision["status"] == "NEEDS_ELABORATION"
    assert decision["statement_drifted"] is True


def test_decision_flags_prefix_drift_with_identical_statement():
    """A new local instance above the theorem re-elaborates the same text."""
    with_instance = ORIGINAL.replace(
        "open Nat\n",
        "open Nat\n\nlocal instance : Inhabited Nat := ⟨0⟩\n",
    )
    decision = _pristine_type_decision(ORIGINAL, with_instance, "zero_add_smoke")
    assert decision["status"] == "NEEDS_ELABORATION"
    assert decision["statement_drifted"] is False
    assert decision["prefix_drifted"] is True, (
        "The prefix is part of the control: instances and notation inserted "
        "above the theorem change how the statement elaborates."
    )


def test_decision_unchanged_on_cosmetic_reflow():
    """A re-wrap is not a drift: both parts normalise to the same text, so
    the control stays on the cheap path. What escalates is a change the
    normaliser cannot see past (a comment, an attribute, a token)."""
    rewrapped = ORIGINAL.replace(
        "theorem zero_add_smoke (n : Nat) : 0 + n = n := by",
        "theorem zero_add_smoke\n    (n : Nat) :\n    0 + n = n := by",
    )
    decision = _pristine_type_decision(ORIGINAL, rewrapped, "zero_add_smoke")
    assert decision["status"] == "UNCHANGED"


def test_decision_flags_comment_added_inside_statement():
    """Comments are kept in the span, so inserting one inside the statement
    region escalates rather than silently comparing two different slices.
    The elaboration then confirms the type did not move."""
    commented = ORIGINAL.replace(
        "(n : Nat) : 0 + n = n :=",
        "(n : Nat) : -- left-neutral\n    0 + n = n :=",
    )
    decision = _pristine_type_decision(ORIGINAL, commented, "zero_add_smoke")
    assert decision["status"] == "NEEDS_ELABORATION"
    assert decision["probe"] is not None


# --- decision: MISSING --------------------------------------------------


def test_decision_missing_when_absent_from_original():
    decision = _pristine_type_decision(ORIGINAL, ORIGINAL, "not_there")
    assert decision["status"] == "MISSING"
    assert decision["side"] == "original"
    assert decision["probe"] is None


def test_decision_missing_when_deleted_from_current():
    emptied = ORIGINAL.replace("theorem zero_add_smoke", "theorem renamed_away")
    decision = _pristine_type_decision(ORIGINAL, emptied, "zero_add_smoke")
    assert decision["status"] == "MISSING"
    assert decision["side"] == "current", (
        "A theorem that disappeared must be reported on the current side: "
        "the control must never read as a pass when the declaration is gone."
    )


# --- probe --------------------------------------------------------------


def test_probe_uses_pp_all():
    """Without pp.all Lean prints the pretty form: instance arguments are
    hidden and a different-but-defeq type can print identically."""
    probe = _pristine_type_probe("my_thm")
    assert probe.startswith("set_option pp.all true in")
    assert "#check @my_thm" in probe
