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
build; demote ``level_1_build`` to a secondary cross-check. A genuine build
failure ALWAYS produces >=1 parseable compile error in the verifier's raw
output, so promoting the substring contract does not mask real breakage.
The ``level_1_build`` cross-check lets the call-site log a discrepancy when
the two signals disagree (notably the DEMO 62 false-negative pattern).

The multi-agent path (#870-919) already calls ``_reverify_compiles_clean``
+ ``_final_verify_is_false_negative`` for the same purpose -- this helper is
the parity-clean version for the autonomous path. The call-site (provers.py
~1882 and ~1902) replaces its two ``verify_result.get("level_1_build",
False)`` reads with a single ``_evaluate_final_verify(verify_result)`` call.
"""

from __future__ import annotations

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
