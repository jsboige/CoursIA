"""P3 (#7477 forensic): classify decomposition-regression honestly.

The Hashlife/conway family macro-signal (forensic #7477, 11 dedup'd runs,
~16,800s aggregate): **``verified_tactic_count == 0`` in all 11 runs**, and
the net sorry delta is *negative* (regressions outweigh wins). The founding
incident (L2551, grew 4->8) scored ``structural_only`` /
``structural_progress: true`` -- a net sorry-INCREASE decomposition with
ZERO build-verified tactics, labelled as *progress*. That mis-label corrupts
forensic ROI: a run that sprayed unproven sub-sorries looks indistinguishable
from a run that genuinely restructured a hard goal.

P3 separates the two: a net-sorry-INCREASE decomposition is *structural
progress* only when at least one tactic was build-verified
(``verified_tactic_count > 0``); with zero verified tactics it is a
**decomposition-regression** -- more sorries than it started with and nothing
proved. Surfacing the typed verdict lets ``analyze_traces`` rank these runs
honestly instead of counting them as progress.

The per-edit ``sorry guard`` ceiling (``tools.py`` decomposition-budget) lets
a within-budget increase through on purpose (a legitimate decomposition
raises the count while the sub-goals compile); this module is the RUN-LEVEL
terminal check that re-classifies the outcome when none of those sub-goals
was actually *verified closed*. It does not revert the committed snapshot
(reversion is a separate, riskier decision) -- it classifies.

Stdlib-only and self-contained so it is unit-testable by file-path load on a
bare CPU runner that lacks the ``agent_framework`` LLM stack (same pattern as
``heartbeat_budget.py`` / ``forensic_guards.py``).

See #7477 (prover harness forensic). See #1453 (prover co-evolution epic).
"""

from __future__ import annotations

from typing import Optional

__all__ = ["is_decomposition_regression"]


def is_decomposition_regression(
    final_sorry: int,
    original_sorry_count: int,
    verified_tactic_count: Optional[int],
) -> bool:
    """Return True iff the run is a net-sorry-INCREASE decomposition with zero
    build-verified tactics (the #7477 P3 regression pattern).

    Conditions (all required):
      - ``final_sorry > original_sorry_count`` -- the sorry count grew (a
        pure decomposition: same/lower count is never a regression by this
        signal; a drop is real progress, a same-count is handled by the
        FX-8 / statement-mutation guard).
      - ``verified_tactic_count == 0`` -- no tactic was build-verified. A
        decomposition that produced at least one compiling, verified sub-goal
        is genuine structural progress and is NOT flagged.
      - ``verified_tactic_count is None`` returns ``False`` (legacy caller
        that does not track verified tactics -- cannot classify, preserve
        prior behaviour rather than guess).
    """
    if verified_tactic_count is None:
        return False
    return final_sorry > original_sorry_count and verified_tactic_count == 0
