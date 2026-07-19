"""Target-line guard for the prover launcher — DO NOT TARGET enforcement.

#7477 P2b (forensic, child of #1453). The DEMO descriptions that guide the
multi-agent prover sometimes mark a sorry locus as ``DO NOT TARGET`` because
it has already been factored into a private lemma (founder case: DEMO 62
marks the NW quadrant ``DO NOT TARGET NW`` — the residual sorry was consumed
by ``p4_nw_shift_lemma``, #6869). A baseline run that nonetheless aimed at
that locus was correctly refused 4x by the agent but still scored
``no_progress`` and burned to ``iteration_cap`` — the launcher fed it a
target the description itself forbade.

This module parses the ``DO NOT TARGET`` markers out of a DEMO description
and resolves the effective target line so the launcher can refuse (or
auto-redirect to the DEMO's CURRENT TARGET) BEFORE launching the workflow.
Pure stdlib (``re`` only) so it is unit-testable with no prover runtime.

Scope (#7477 P2b): target resolution only. Does NOT touch retry
classification (P1b) or heartbeat diagnostics (P5).
"""

from __future__ import annotations

import re
from typing import Optional

# Exit code the launcher uses when a target line is refused (distinct from
# 2 = bad demo_id, 3 = tree locked, 130 = died). Harvest scripts can tell a
# DO_NOT_TARGET refusal from a real prover failure.
DO_NOT_TARGET_EXIT = 4

# Compass-quadrant region tokens used by the hashlife / quadrant-lemma
# convention (DEMO 62: nw/ne/sw/se). Extend if a future DEMO names other
# regions (e.g. mpr) as DO NOT TARGET.
_REGION_TOKENS = r"(?:nw|ne|sw|se)"

# Quadrant -> line map, e.g. "nw L2970", "ne L2973". The DEMO body lists the
# quadrant sorry-loci with their line numbers; the DO NOT TARGET marker then
# names the forbidden quadrant.
_REGION_LINE_RE = re.compile(rf"\b({_REGION_TOKENS})\s+L(\d+)\b", re.IGNORECASE)

# "DO NOT TARGET <region>" — names the forbidden quadrant.
_DO_NOT_TARGET_REGION_RE = re.compile(
    rf"do not target\s+({_REGION_TOKENS})\b", re.IGNORECASE
)

# Direct form: "DO NOT TARGET L1234" (line named right after the marker, no
# region token). Generalises beyond the quadrant convention.
_DO_NOT_TARGET_LINE_RE = re.compile(r"do not target\s+L(\d+)\b", re.IGNORECASE)


def parse_do_not_target_lines(description: Optional[str]) -> set[int]:
    """Return the line numbers the DEMO ``description`` marks DO NOT TARGET.

    Handles two conventions (both present-then-resolved in DEMO 62):

    1. Region form — a quadrant->line map (``nw L2970, ne L2973``) plus a
       ``DO NOT TARGET <region>`` declaration. The forbidden region's mapped
       line is returned.
    2. Direct form — ``DO NOT TARGET L<digits>`` names the forbidden line
       inline.

    Returns an empty set when the description is absent or declares nothing.
    """
    if not description:
        return set()
    region_to_line: dict[str, int] = {}
    for m in _REGION_LINE_RE.finditer(description):
        region_to_line[m.group(1).lower()] = int(m.group(2))
    forbidden: set[int] = set()
    for m in _DO_NOT_TARGET_REGION_RE.finditer(description):
        region = m.group(1).lower()
        if region in region_to_line:
            forbidden.add(region_to_line[region])
    for m in _DO_NOT_TARGET_LINE_RE.finditer(description):
        forbidden.add(int(m.group(1)))
    return forbidden


def resolve_target_line(
    demo: dict, override: Optional[int] = None
) -> tuple[Optional[int], str]:
    """Resolve the effective target line, enforcing DO NOT TARGET.

    Parameters
    ----------
    demo : dict
        A DEMO entry (needs ``line`` and ``description`` keys).
    override : int, optional
        A ``--line`` CLI override. ``None`` means use the DEMO default.

    Returns
    -------
    (line, status) where status is one of:
      - ``"ok"``         — the requested line is allowed (or no DO NOT TARGET
                           declaration exists); ``line`` is what to aim at.
      - ``"redirected"`` — the requested line is forbidden; auto-redirected
                           to the DEMO's CURRENT TARGET (its default ``line``).
      - ``"refused"``    — the requested line is forbidden AND no safe
                           CURRENT TARGET exists (the default is itself
                           forbidden, absent, or identical); ``line`` is None
                           and the launcher should exit ``DO_NOT_TARGET_EXIT``.
    """
    forbidden = parse_do_not_target_lines(demo.get("description"))
    default = demo.get("line")
    requested = override if override is not None else default
    if requested is None:
        return None, "ok"
    if not forbidden or requested not in forbidden:
        return requested, "ok"
    # Requested line is forbidden — try to fall back to the DEMO's CURRENT
    # TARGET (its default line), provided that default is itself safe.
    if (
        default is not None
        and default != requested
        and default not in forbidden
    ):
        return default, "redirected"
    return None, "refused"
