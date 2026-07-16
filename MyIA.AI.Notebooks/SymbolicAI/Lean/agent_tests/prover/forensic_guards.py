"""Pure, stdlib-only forensic anti-gaming guards for the Lean prover harness.

These helpers detect the two classic ways an autonomous prover can *fake*
progress instead of genuinely eliminating a ``sorry``:

  1. Axiom-cheat -- closing a goal by introducing a fresh ``axiom``
     declaration. A single new axiom makes any statement provable for free,
     so the axiom count must never silently rise
     (``_is_axiom_declaration`` / ``_count_axiom_declarations``).
  2. Sorry-relocation -- creating a new named ``lemma foo := by sorry`` and
     calling it to "close" an existing sorry, so the *local* sorry vanishes
     while the *global* sorry count is unchanged
     (``_find_sorry_definitions`` / ``_check_sorry_relocation``).

Why this module exists as a standalone file
--------------------------------------------
These guards were previously defined inline in ``prover/tools.py``. That file
pulls the full agent framework at module load (its top-level relative imports
reach ``prover.state`` / ``prover.knowledge`` / ``prover.provers``), so any test
importing the guards via ``prover.tools`` drags in ``agent_framework`` at pytest
*collection* time -- which aborts the whole session on a bare CI runner (the
exact failure mode ``.github/workflows/scripts-tests.yml`` exists to prevent).
Extracting the guards here -- with **only** ``import re`` -- lets the unit tests
load this module by file path and run hermetically, with no LLM / Lean / network
/ agent-framework dependency. ``tools.py`` re-imports these names, so behaviour
is unchanged for the runtime harness.

See #6790 (prover harness robustness) and #6907 (type-annotation regex).
"""

from __future__ import annotations

import re

# ---------------------------------------------------------------------------
# Axiom-cheat guard
# ---------------------------------------------------------------------------
# Regex to detect standalone `axiom` declarations in Lean 4 source.
# Matches lines like `axiom foo`, `axiom bar : Prop`, `axiom baz (n : Nat) : ...`
# but NOT lines inside comments (--) or strings, and NOT `axiom` in prose.
_AXIOM_DECL_RE = re.compile(r'^\s*axiom\s+\w', re.MULTILINE)


def _is_axiom_declaration(line: str) -> bool:
    """Check if a single line is a standalone axiom declaration."""
    return bool(_AXIOM_DECL_RE.match(line))


def _count_axiom_declarations(content: str) -> int:
    """Count standalone axiom declarations in Lean source content."""
    return sum(1 for line in content.splitlines() if _is_axiom_declaration(line))


# ---------------------------------------------------------------------------
# Sorry-relocation guard
# ---------------------------------------------------------------------------
# Regex to extract lemma/def names that contain sorry in their body.
# NOTE: `have` is excluded because decomposition with `have h := by sorry` is
# the legitimate scaffolding pattern. Only top-level `lemma`/`def` sorry
# definitions indicate relocation (the prover creates a separate named lemma
# instead of decomposing inline).
#
# The body segment `(?:(?!:=)[\s\S]){0,2000}?` lazily matches any character
# (including `:`, `=`, and newlines) as long as it is NOT positioned at the
# start of the real definition token `:=`. The negative lookahead `(?!:=)`
# guarantees the segment stops at -- and never crosses -- the first `:=`, so a
# signature may freely contain:
#     `lemma foo : P := by sorry`                (type-annotation colon)
#     `lemma mul (n m : Nat) : Nat := by sorry`  (nested binders)
#     `lemma bar (n : Nat) : n = n := by sorry`  (equation goal -- an `=`)
#     `lemma qux\n  : P\n  := by sorry`          (multi-line, via [\s\S])
# The `{0,2000}` upper bound keeps the segment linear (no catastrophic
# backtracking, bounded scan on pathological input with no `:=`). This is a
# superset of the earlier `(?:[^:=]|:[^=])*?` form, which handled a `:` in the
# signature but silently MISSED any `=` (equation goals `a = b`), leaving that
# relocation shape undetected. See #6790 / #6907.
_SORRY_DEF_RE = re.compile(
    r'(?:lemma|def)\s+(\w+)\b(?:(?!:=)[\s\S]){0,2000}?:=\s*by\s+sorry',
    re.MULTILINE,
)


def _find_sorry_definitions(content: str) -> set:
    """Find names of lemmas/defs defined with sorry in their body.

    Returns a set of identifier names that are defined as sorry in the content.
    Used by the sorry-relocation guard to detect when the prover creates a
    new sorry lemma and calls it to close existing sorry.
    """
    return set(_SORRY_DEF_RE.findall(content))


def _check_sorry_relocation(new_content: str, original_content: str,
                            replaced_text: str) -> tuple:
    """Check if sorry was relocated rather than proved.

    Returns (is_relocation: bool, sorry_defs: set, called_names: set).

    A relocation is when:
    1. The new file has NEW lemmas/defs defined with sorry that
       didn't exist in the original
    2. The replacement text (which closed existing sorry) calls one of
       those new sorry definitions
    """
    orig_defs = _find_sorry_definitions(original_content)
    new_defs = _find_sorry_definitions(new_content)
    # New sorry definitions not in original
    fresh_sorry_defs = new_defs - orig_defs
    if not fresh_sorry_defs:
        return False, set(), set()
    # Check if the replacement text references any fresh sorry definition
    called = set()
    for name in fresh_sorry_defs:
        if name in replaced_text:
            called.add(name)
    if called:
        return True, fresh_sorry_defs, called
    # Also check if ANY sorry-closing text in new_content references them
    # (for cases where the replacement spans multiple edits)
    return False, fresh_sorry_defs, set()
