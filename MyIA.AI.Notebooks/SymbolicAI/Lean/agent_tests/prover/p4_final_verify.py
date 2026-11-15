"""P4 fuller L1 false-negative fix (#7477 forensic, #6790 '(b)/(c) await').

Lives in its own stdlib-only module so the unit tests can load it by file
path without dragging ``agent_framework`` / ``agent_framework_openai`` /
``prover.tools`` at pytest collection time. Mirrors the pattern used by
``prover/heartbeat_budget.py`` (P5a, #7502) and ``prover/forensic_guards.py``
(#6790 / #6907).

Founding incident (DEMO 62 conway_lean L2892, 2026-07-16): the autonomous
prover final-verify gate at ``provers.py ~1828-1870`` formerly keyed on
``verify_result["level_1_build"]`` alone, a manifest/cache-sensitive signal
(see ``tools.py::compile``). When the worktree emitted ``warning: manifest
out of date`` Lean's ``verifier.success`` flipped to False while the regex
error parser returned ``error_count == 0`` on the exact same content. The
blind revert destroyed a real 5-sub-goal decomposition (structural progress
lost, exhumed only by manual span extraction).

Fix (#7477 P4): promote the authoritative ``": error:"`` substring contract
(#6831, ``prover.tools._parse_lean_errors``) to the PRIMARY signal of a clean
build and fully demote ``level_1_build`` -- it is no longer read at all, not
as a gate and not as a cross-check (see ``_evaluate_final_verify`` below). A
genuine build failure ALWAYS produces >=1 parseable compile error in the
verifier's raw output, so promoting the substring contract does not mask real
breakage; a ``level_1_build`` disagreeing with the substring verdict (the DEMO
62 false-negative pattern) is expected to remain silent -- the substring
contract is authoritative.

The multi-agent path (#870-919) already calls ``_reverify_compiles_clean``
+ ``_final_verify_is_false_negative`` for the same purpose -- this helper is
the parity-clean version for the autonomous path. The call-site (provers.py
~1882 and ~1902) replaces its two ``verify_result.get("level_1_build",
False)`` reads with a single ``_evaluate_final_verify(verify_result)`` call.
"""

from __future__ import annotations

import re

# Local import is at function scope so the test loader can stub
# ``prover.tools._parse_lean_errors`` via ``sys.modules`` without having to
# import the LLM stack. See tests/test_p4_l1_false_negative.py for the
# import-side stub pattern (C677-L2 ★★ late-import mock).


def _evaluate_final_verify(verify_result: dict) -> bool:
    """P4 fuller fix -- see module docstring.

    Args:
        verify_result: dict from ``json.loads(tactic_tools.compile())``,
            carrying at least ``level_1_build: bool``, ``raw_output: str``
            (preferred) or ``errors: list`` (fallback), and ``error_count``.

    Returns:
        True iff ``_parse_lean_errors`` reports zero errors in the raw
        output. False on a genuine build failure (>=1 parseable error).
        ``level_1_build`` is intentionally NOT consulted as a gate -- the
        substring contract is authoritative (DEMO 62 founding incident).
    """
    # Late-import so the test harness can stub _parse_lean_errors via
    # sys.modules without pulling the full LLM stack at module load.
    from prover.tools import _parse_lean_errors
    raw = verify_result.get("raw_output", "") or verify_result.get("errors", "")
    substring_errors = _parse_lean_errors(raw)
    if len(substring_errors) == 0:
        # No compile error in the raw lake output -> the build ACTUALLY passed.
        # level_1 may still be False (worktree manifest out-of-date, cache
        # state -- DEMO 62) but the substring contract is authoritative: do
        # NOT trust level_1 alone when it disagrees with zero parsed errors.
        return True
    # >=1 parseable error -> real build failure regardless of level_1_build.
    return False


# --- pristine elaborated-type control (track a, #1453) ------------------
#
# Why: ``_evaluate_final_verify`` answers "does the file still compile?".
# It does not answer "is the theorem still the SAME theorem?". A prover that
# weakens a statement (``n + 0 = n`` -> ``n + 0 = n + 0``, a dropped binder,
# a ``True`` conjunct) and then proves the weakened form reports a clean
# build and a lower ``sorry`` count: every gate above stays green and the
# result is a proof of a different proposition. The existing FX-6
# ``_stmt_mutation_guard`` catches the CRUDER shape (sorry drop with zero
# verified tactic); it cannot see a mutation that came WITH a verifying
# tactic.
#
# The control is text-first, because elaboration is the expensive part:
#
#   * statement text identical AND file prefix before the declaration
#     identical  -> the elaborated type is provably the same (same imports,
#     same preceding definitions and instances, same statement source).
#     Cost: two substring compares.
#   * anything else -> ``NEEDS_ELABORATION``: the caller elaborates
#     ``set_option pp.all true in #check @<decl>`` on both contents and
#     compares the printed types.
#
# The prefix matters as much as the statement: a new local instance or
# notation inserted ABOVE the theorem changes how the very same statement
# elaborates, so comparing the statement alone would be unsound for a
# prover that edits the file it is proving in.

_DECL_HEAD_RE = re.compile(
    r"(?m)^[ \t]*(?:@\[[^\]]*\][ \t]*)?"
    r"(?:(?:private|protected|noncomputable|partial|unsafe)[ \t]+)*"
    r"(?:theorem|lemma)[ \t]+(?P<name>[A-Za-z_][A-Za-z0-9_'!?.]*)"
)

_WHERE_RE = re.compile(r"where(?![A-Za-z0-9_'])")


def _normalise_lean_text(text: str) -> str:
    """Collapse whitespace so an indentation/line-wrap edit is not a drift."""
    return " ".join(text.split())


def _declaration_span(content: str, decl_name: str):
    """Return ``(prefix, statement)`` for ``decl_name``, or ``None``.

    ``prefix`` is everything before the declaration keyword (imports,
    options, previous definitions); ``statement`` runs from after the
    declaration's name up to the body separator (``:=`` or ``where``) at
    bracket depth 0. Line and block comments are skipped while scanning so
    a ``:=`` inside a comment cannot end the statement early.
    """
    for match in _DECL_HEAD_RE.finditer(content):
        if match.group("name") != decl_name:
            continue
        start = match.end()
        end = _statement_end(content, start)
        if end is None:
            return None
        return content[: match.start()], content[start:end]
    return None


def _statement_end(text: str, start: int):
    """Index of the body separator after ``start``, or ``None``."""
    depth = 0
    index = start
    length = len(text)
    while index < length:
        char = text[index]
        if char in "([{":
            depth += 1
        elif char in ")]}":
            depth = max(0, depth - 1)
        elif char == "-" and text.startswith("--", index):
            newline = text.find("\n", index)
            index = length if newline == -1 else newline
            continue
        elif char == "/" and text.startswith("/-", index):
            close = text.find("-/", index + 2)
            index = length if close == -1 else close + 2
            continue
        elif depth == 0:
            if text.startswith(":=", index):
                return index
            if _WHERE_RE.match(text, index):
                return index
        index += 1
    return None


def _pristine_type_decision(
    original_content: str, current_content: str, decl_name: str
) -> dict:
    """Decide whether a resolved theorem's elaborated type can be trusted.

    Returns a dict with ``status``:

    * ``"UNCHANGED"`` -- statement and prefix are text-identical: the
      elaborated type of ``decl_name`` is the same by construction, no
      elaboration needed.
    * ``"NEEDS_ELABORATION"`` -- either part drifted; the caller must run
      ``set_option pp.all true in #check @<decl>`` on both contents and
      compare. Re-wrapping and indentation do NOT land here -- the
      normaliser collapses whitespace, so they stay on the cheap path. What
      lands here is a change the normaliser cannot see past: a comment or an
      attribute inside the span, a token, an added binder. The elaboration
      is what tells a semantic change from a cosmetic one, and guessing
      here would either fail a real proof or accept a weakened one.
    * ``"MISSING"`` -- the declaration is absent from the original or from
      the current content. Not a verdict on the type; the caller must not
      treat this as a pass.

    ``probe`` carries the Lean source to elaborate for ``NEEDS_ELABORATION``
    (``None`` otherwise), so the caller does not rebuild it differently.
    """
    original = _declaration_span(original_content, decl_name)
    if original is None:
        return {
            "status": "MISSING",
            "decl": decl_name,
            "side": "original",
            "probe": None,
        }
    current = _declaration_span(current_content, decl_name)
    if current is None:
        return {
            "status": "MISSING",
            "decl": decl_name,
            "side": "current",
            "probe": None,
        }

    original_prefix, original_statement = original
    current_prefix, current_statement = current
    same_statement = (
        _normalise_lean_text(original_statement)
        == _normalise_lean_text(current_statement)
    )
    same_prefix = (
        _normalise_lean_text(original_prefix) == _normalise_lean_text(current_prefix)
    )
    if same_statement and same_prefix:
        return {
            "status": "UNCHANGED",
            "decl": decl_name,
            "side": None,
            "probe": None,
        }
    return {
        "status": "NEEDS_ELABORATION",
        "decl": decl_name,
        "side": None,
        "statement_drifted": not same_statement,
        "prefix_drifted": not same_prefix,
        "original_statement": _normalise_lean_text(original_statement),
        "current_statement": _normalise_lean_text(current_statement),
        "probe": _pristine_type_probe(decl_name),
    }


def _pristine_type_probe(decl_name: str) -> str:
    """Lean source that prints the fully elaborated type of ``decl_name``.

    ``pp.all`` is what makes the comparison meaningful: without it Lean
    prints the pretty form, where a different but defeq type and the
    original can look identical, and where instance arguments are hidden.
    """
    return f"set_option pp.all true in\n#check @{decl_name}\n"


# Text-failure markers of a ``#check`` that produced no type. Kept narrow on
# purpose: a warning ("declaration uses 'sorry'") does not invalidate the
# printed type, an error does. Reading the marker anywhere in the output is
# conservative -- a blocker on a false negative is cheaper than a pass on a
# failed elaboration.
_CHECK_FAILURE_MARKERS = (
    "error:",
    "unknown identifier",
    "unknown constant",
    "unknown declaration",
    "failed to synthesize",
)


def _elaborated_type_text(output: str, decl_name: str):
    """Return the printed type from a ``#check`` output, or ``None``.

    ``None`` means "no type came out" -- an empty output, a Lean error, or a
    line that does not carry ``decl : ...``. It never means "the same type":
    a caller that reads ``None`` as equality would turn a failed elaboration
    into a pass, which is the one direction this control must not fail in.
    """
    if not output:
        return None
    lowered = output.lower()
    for marker in _CHECK_FAILURE_MARKERS:
        if marker in lowered:
            return None
    normalised = _normalise_lean_text(output)
    pattern = r"(?<![\w.'])@?" + re.escape(decl_name) + r"\s*:\s*"
    match = re.search(pattern, normalised)
    if match is None:
        return None
    return normalised[match.end() :]


def _pristine_type_elaboration_decision(
    original_output: str, current_output: str, decl_name: str
) -> dict:
    """Compare the two elaborated types printed for ``decl_name``.

    Statuses: ``"SAME_TYPE"``, ``"TYPE_DRIFTED"``, ``"ELABORATION_ERROR"``.
    The comparison is on the ``pp.all`` text: instance arguments, universe
    levels and implicit binders are all in it, so two types that differ only
    by an implicit argument or by the instance they picked are reported as
    drifted -- which is the point.
    """
    original_type = _elaborated_type_text(original_output, decl_name)
    current_type = _elaborated_type_text(current_output, decl_name)
    if original_type is None or current_type is None:
        failed_side = "original" if original_type is None else "current"
        return {
            "status": "ELABORATION_ERROR",
            "decl": decl_name,
            "side": failed_side,
            "original_type": original_type,
            "current_type": current_type,
        }
    if original_type == current_type:
        return {
            "status": "SAME_TYPE",
            "decl": decl_name,
            "side": None,
            "original_type": original_type,
            "current_type": current_type,
        }
    return {
        "status": "TYPE_DRIFTED",
        "decl": decl_name,
        "side": None,
        "original_type": original_type,
        "current_type": current_type,
    }


def _pristine_type_check(
    original_content: str,
    current_content: str,
    decl_name: str,
    elaborate,
) -> dict:
    """Full control: text-first, elaboration only when the text drifted.

    ``elaborate(probe, content)`` must run the probe against ``content`` and
    return the raw Lean output. It is injected rather than imported so this
    module stays stdlib-only and the decision logic is unit-testable without
    a toolchain.

    Returns the decision with ``elaborated`` telling the caller which path
    produced the verdict -- a ``SAME_TYPE`` reached without elaboration and
    one reached through it are both valid, but they cost differently and the
    report should be able to say which was paid.
    """
    decision = _pristine_type_decision(original_content, current_content, decl_name)
    if decision["status"] == "UNCHANGED":
        return {
            "status": "SAME_TYPE",
            "decl": decl_name,
            "side": None,
            "elaborated": False,
            "original_type": None,
            "current_type": None,
        }
    if decision["status"] == "MISSING":
        return {
            "status": "MISSING",
            "decl": decl_name,
            "side": decision["side"],
            "elaborated": False,
            "original_type": None,
            "current_type": None,
        }
    probe = decision["probe"]
    verdict = _pristine_type_elaboration_decision(
        elaborate(probe, original_content),
        elaborate(probe, current_content),
        decl_name,
    )
    verdict["elaborated"] = True
    verdict["text_decision"] = decision
    return verdict
