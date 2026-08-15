"""Tests for check_twin_parity --per-pair classification (_classify_per_pair).

Pins the edge-case fix for ADDED pairs (forensic po-2026 c.709, executable proof).

Before the fix, a pair ADDED by the PR (absent from the base-ref registry,
base_status="MISSING") that was NOT OK at HEAD (head_status="DRIFT") was
mis-classified as DRIFT_PRE_EXISTING -- which does NOT fail the gate (the gate
fails only on DRIFT_INTRODUCED). So a PR that added a new twin_pairs.yaml entry
with driftant SHAs passed the per-pair gate. That contradicted the inline comment
("paire ajoutee -> si pas OK au HEAD, c'est du drift introduit") and the
"sound edge case" LGTM claim.

The fix: a pair absent from the base-ref has NO pre-existing state -- its HEAD
state IS what the PR introduces. So MISSING+DRIFT -> DRIFT_INTRODUCED (gate
fails), and MISSING+OK -> OK (not the misleading DRIFT_RESOLVED).

All 9 combos of base_status x head_status are pinned here so the classification
table is regression-locked.
"""
from __future__ import annotations

import os
import sys

import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from check_twin_parity import _classify_per_pair  # noqa: E402


# --- the full 9-combo classification table (base_status x head_status) --------
# (base, head) -> (verdict, fails_gate)
# fails_gate = True iff verdict == "DRIFT_INTRODUCED" (the --check --per-pair exit 1).
EXPECTED = {
    # Existing pair, clean at base
    ("OK", "OK"): ("OK", False),
    ("OK", "DRIFT"): ("DRIFT_INTRODUCED", True),
    ("OK", "MISSING"): ("DRIFT_INTRODUCED", True),
    # Existing pair, already driftant at base
    ("DRIFT", "OK"): ("DRIFT_RESOLVED", False),
    ("DRIFT", "DRIFT"): ("DRIFT_PRE_EXISTING", False),
    ("DRIFT", "MISSING"): ("DRIFT_PRE_EXISTING", False),
    # Pair ADDED by the PR (absent at base) -- the fixed edge cases
    ("MISSING", "OK"): ("OK", False),              # PR adds a clean pair
    ("MISSING", "DRIFT"): ("DRIFT_INTRODUCED", True),   # <-- the bug: was PRE_EXISTING
    ("MISSING", "MISSING"): ("DRIFT_INTRODUCED", True), # <-- the bug: was PRE_EXISTING
}


@pytest.mark.parametrize("base,head", sorted(EXPECTED.keys()))
def test_classify_all_combos(base, head):
    verdict, fails_gate = EXPECTED[(base, head)]
    got = _classify_per_pair(base, head)
    assert got == verdict, (
        f"_classify_per_pair({base!r}, {head!r}) = {got!r}, expected {verdict!r}"
    )
    # The gate (--check --per-pair) returns 1 iff there is >=1 DRIFT_INTRODUCED.
    assert (got == "DRIFT_INTRODUCED") == fails_gate


# --- the two founding-bug cases, spelled out explicitly ----------------------


def test_added_pair_driftant_at_head_fails_gate():
    """The founding bug: an ADDED pair (base MISSING) that is DRIFT at HEAD must
    be classified DRIFT_INTRODUCED (gate fails), NOT DRIFT_PRE_EXISTING (gate pass).
    """
    assert _classify_per_pair("MISSING", "DRIFT") == "DRIFT_INTRODUCED"


def test_added_pair_with_missing_files_at_head_fails_gate():
    """Same bug, files-missing variant: ADDED pair whose files don't exist at HEAD
    must be DRIFT_INTRODUCED, not silently passed as PRE_EXISTING."""
    assert _classify_per_pair("MISSING", "MISSING") == "DRIFT_INTRODUCED"


def test_added_clean_pair_is_OK_not_resolved():
    """An ADDED pair that is OK at HEAD is OK (the PR adds a clean pair), NOT
    DRIFT_RESOLVED (nothing was resolved -- there was no prior driftant state)."""
    assert _classify_per_pair("MISSING", "OK") == "OK"


def test_pre_existing_drift_does_not_fail_gate():
    """Sanity: a pair driftant at BOTH base and HEAD is PRE_EXISTING (not the PR's
    fault) and must NOT fail the gate. This is the whole point of --per-pair mode."""
    assert _classify_per_pair("DRIFT", "DRIFT") == "DRIFT_PRE_EXISTING"


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-v"]))
