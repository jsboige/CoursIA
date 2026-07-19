"""P5a (#7477 forensic): classify Lean heartbeat-budget exhaustion.

The structural wall on DEMO 62 (Hashlife P5) is a whnf blowup that hits
Lean's ``maxHeartbeats`` ceiling (default 200000): a tactic that is
*correct* becomes unaffordable, and the ``lake build`` output surfaces it
as

    (deterministic) timeout, maximum heartbeats (200000)

Without a typed verdict, the prover harness sinks these runs into
``no_progress`` or a generic timeout, hiding a proof-engineering wall
(confirmed model-independent by ai-01's A-B, c.681: glm-5.2, gpt-5.6-sol
and kimi-k3 all hit it) under a label that reads as "the agent gave up".

This module is stdlib-only and self-contained so it can be unit-tested by
file-path load on a bare CPU runner that lacks the ``agent_framework`` LLM
stack (same pattern as ``forensic_guards.py``). The verdict is surfaced on
the prover's result dict as ``heartbeat_budget_exceeded`` (See #7477,
See #1453), distinct from ``no_progress`` (the agent did attempt) and from
a generic provider / wall-clock timeout.

P5b (factor-lemma / ``set_option maxHeartbeats`` hint) is a SEPARATE grain
and intentionally not handled here.
"""

from __future__ import annotations

import re
from typing import Optional

__all__ = ["output_indicates_heartbeat_budget_exceeded"]

# Lean surfaces maxHeartbeats exhaustion via one of two signatures in the
# `lake build` output. Both mean the proposition/tactic is *correct but
# unaffordable* under the heartbeat budget, not that the agent is wrong.
#   - "(deterministic) timeout, maximum heartbeats (N)"  (Lean 4 core)
#   - bare "maximum heartbeats" (truncated / wrapped variants)
# Case-insensitive: capitalization varies across Lean versions / wrappers.
_HEARTBEAT_SIGNATURES = (
    re.compile(r"maximum heartbeats", re.IGNORECASE),
    re.compile(r"\(deterministic\)\s+timeout", re.IGNORECASE),
)


def output_indicates_heartbeat_budget_exceeded(text: Optional[str]) -> bool:
    """Return True iff ``text`` carries a Lean maxHeartbeats-exhaustion signature.

    ``text`` is any build-output fragment the harness captured: the raw
    ``lake build`` output (``final_verify["raw_output"]``), the per-attempt
    error string (``TacticAttempt.error``, where a submitted tactic blew the
    budget), or an error-message excerpt. ``None`` / empty -> ``False``
    (no evidence, do not classify as a heartbeat wall).
    """
    if not text:
        return False
    return any(sig.search(text) for sig in _HEARTBEAT_SIGNATURES)
