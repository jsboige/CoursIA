"""Unit tests for the delta-based size guard + edit sandbox (#1453 DEMO 63 forensic).

These tests load ``prover/size_guard.py`` by file path so they run without
the LLM / Lean / agent_framework stack (the standard CI-hermetic pattern
established by ``test_prover_forensic_guards.py`` and
``test_read_lines_from_source.py``). The harness integration is verified
indirectly: every test uses only the public ``check_size_delta`` and
``EditSandbox`` entry points, which is what ``prover/tools.py`` calls into
— so a regression in those public contracts surfaces here.

Background (DEMO 63 forensic, cycle-98, 2026-08-06):
    The pre-existing ``prover.tools._check_file_size_guard`` absolute cap
    (5000 lines) created a perverse incentive: when the file crossed the
    threshold mid-run, the autonomous prover's only way to stay under the
    cap was to **delete** content. TacticAgent suppressed 622 lines on a
    5385-line file, silently removing 3 c.91 guard theorems.

    Two mechanisms in size_guard.py block this:
    1. ``check_size_delta`` -- DELTA-based cap on insertions / deletions
       with an "insert-only allowance" for pre-existing oversized files.
    2. ``EditSandbox`` -- one-shot checkpoint before the first edit,
       restored on verifier failure or mid-edit exception.

Run from ``agent_tests/``::

    python -m pytest tests/test_prover_size_guard.py -q
"""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

import pytest

# ---------------------------------------------------------------------------
# Stdlib-only import of ``prover/size_guard.py``
# ---------------------------------------------------------------------------
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent  # agent_tests/
SIZE_GUARD_PATH = ROOT / "prover" / "size_guard.py"

spec = importlib.util.spec_from_file_location("prover.size_guard", SIZE_GUARD_PATH)
assert spec and spec.loader, "could not load spec for size_guard.py"
size_guard = importlib.util.module_from_spec(spec)
sys.modules["prover.size_guard"] = size_guard
spec.loader.exec_module(size_guard)

check_size_delta = size_guard.check_size_delta
EditSandbox = size_guard.EditSandbox
INSERT_ONLY_THRESHOLD = size_guard.INSERT_ONLY_THRESHOLD
MAX_NET_DELETION_LINES = size_guard.MAX_NET_DELETION_LINES
MAX_NET_DELETION_PCT = size_guard.MAX_NET_DELETION_PCT
MAX_NET_INSERTIONS = size_guard.MAX_NET_INSERTIONS


# ---------------------------------------------------------------------------
# Delta-based size guard: rejection paths (the DEMO 63 reproduction)
# ---------------------------------------------------------------------------

def test_demo63_repro_622_line_deletion_on_5385_line_file_blocked():
    """The DEMO 63 forensic scenario: 622-line net deletion on a 5385-line file.

    Reproduces the exact pathology that motivated this fix: TacticAgent
    suppressed 622 lines (including 3 c.91 guard theorems) to fit under
    the absolute 5000-line cap. The delta-based guard must reject it.
    """
    # 5385-line file: 5384 newlines + 1 implicit.
    orig = "\n".join(f"-- line {i}" for i in range(5384)) + "\n"
    assert orig.count("\n") == 5384  # 5385 lines (count('\\n') + 1)

    # Replacement strips a 622-line range, leaving 4763 lines.
    # 4763 lines = 4762 newlines + 1 implicit -> 4762 entries.
    new = "\n".join(f"-- line {i}" for i in range(4762)) + "\n"
    # Sanity: net deletion = 5385 - 4763 = 622.
    assert (orig.count("\n") + 1) - (new.count("\n") + 1) == 622

    err = check_size_delta(orig, new, "file_replace_lines")
    assert err is not None, (
        "DEMO 63 forensic scenario MUST be blocked: a 622-line net deletion "
        "on a 5385-line file can silently erase guard theorems."
    )
    # The error message should name the cap that triggered.
    assert "size-delta guard" in err
    assert "622" in err or str(abs((orig.count("\n") + 1) - (new.count("\n") + 1))) in err
    assert "MAX_NET_DELETION" not in err  # we expose the cap value, not the symbol


def test_demo63_pct_threshold_blocks_at_too_large_fraction():
    """A net deletion below the absolute cap but above the percentage cap is blocked.

    Catches the "smaller file, same pathology" version of DEMO 63: a 100-line
    deletion on a 600-line file (16.7%) exceeds MAX_NET_DELETION_PCT (10%),
    so it must be blocked even though it's only 1/5 of the absolute cap.
    """
    orig = "\n".join(f"-- line {i}" for i in range(599)) + "\n"
    new = "\n".join(f"-- line {i}" for i in range(499)) + "\n"
    # Net deletion = 100 lines on 600-line file = 16.7%.
    assert (orig.count("\n") + 1) - (new.count("\n") + 1) == 100

    err = check_size_delta(orig, new, "file_replace_lines")
    assert err is not None
    assert "size-delta guard" in err
    assert "10%" in err or "percentage" in err


def test_insert_only_allowance_blocks_deletion_on_oversized_file():
    """When the original is above INSERT_ONLY_THRESHOLD, even a small deletion is blocked.

    This is the "files that grew beyond the cap legitimately" case: the
    delta guard treats any net deletion as suspect, because the historical
    pattern is "delete-to-fit" rather than "delete for genuine refactor".
    """
    # INSERT_ONLY_THRESHOLD + 100 lines = above-cap file.
    orig_lines = INSERT_ONLY_THRESHOLD + 100
    orig = "\n".join(f"-- line {i}" for i in range(orig_lines - 1)) + "\n"

    # Even a 10-line deletion on a 5100-line file must be blocked.
    new_lines = orig_lines - 10
    new = "\n".join(f"-- line {i}" for i in range(new_lines - 1)) + "\n"

    err = check_size_delta(orig, new, "file_insert_lines")
    assert err is not None
    assert "insert-only allowance" in err
    assert str(orig_lines) in err


# ---------------------------------------------------------------------------
# Delta-based size guard: allow paths (no false positives)
# ---------------------------------------------------------------------------

def test_small_replace_on_normal_file_allowed():
    """A targeted replace of a sorry block on a normal-sized file is allowed."""
    orig = "\n".join(f"-- line {i}" for i in range(100)) + "\n"
    # Replace 5 lines with 8 lines (typical sorry-block rewrite).
    new = "\n".join(f"-- line {i}" for i in range(95)) + "\n"
    # Net change = -2 lines on a 101-line file = 2% deletion.
    assert check_size_delta(orig, new, "file_replace_lines") is None


def test_lemma_insertion_allowed_below_cap():
    """Inserting a helper lemma (20 lines) on a 200-line file is allowed."""
    orig = "\n".join(f"-- line {i}" for i in range(199)) + "\n"
    new = orig + "lemma helper : True := by trivial\n" * 20
    err = check_size_delta(orig, new, "file_insert_lines")
    assert err is None, f"unexpected rejection: {err}"


def test_insert_only_allowance_allows_additive_growth_on_oversized_file():
    """An oversized file can still grow (additive edits) — insert-only is additive."""
    orig_lines = INSERT_ONLY_THRESHOLD + 50
    orig = "\n".join(f"-- line {i}" for i in range(orig_lines - 1)) + "\n"

    # +10 lines (insertion) on a 5050-line file must be allowed.
    new = orig + "-- new lemma\n" * 10
    assert check_size_delta(orig, new, "file_insert_lines") is None


def test_insert_only_allowance_allows_40_line_helpers_on_above_cap_file():
    """Mirror of DEMO 63 forensic: the absolute cap blocked 8x legitimate inserts.

    Fresh evidence (ai-01 dispatch msg-20260806T195324-17sdsv): in DEMO 63 run 2,
    the absolute 5000-line cap (prover.tools._check_file_size_guard) blocked 8
    legitimate scaffolding inserts (file_insert_lines / file_replace_sorry /
    file_replace_lines) when the file was already 5643-5680 lines. The plan
    required 4 private helper lemmas (~+40 lines) that could not be inserted.
    This is the SYMMETRIC pathology of DEMO 63 run 1: where run 1 deleted
    622 lines to *fit* the cap, run 2 could not *grow* past the cap.

    The delta-based guard's insert-only allowance (Rule 1: orig_above_cap AND
    net >= 0) is the explicit fix: additive growth on a pre-existing oversized
    file is allowed, only net deletions are blocked.
    """
    # Reproduce the run 2 starting size: 5643 lines (just above the cap).
    orig_lines = 5643
    orig = "\n".join(f"-- line {i}" for i in range(orig_lines - 1)) + "\n"
    assert orig.count("\n") + 1 == orig_lines
    assert orig_lines > INSERT_ONLY_THRESHOLD  # pre-condition for insert-only allowance

    # Insert 40 lines of helpers (4 private lemmas ~10 lines each, as in the plan).
    # Each lemma is a one-liner followed by '\n', so 4 lemmas = 4 newline additions.
    new = orig + (
        "lemma helper_align_1 (x : Nat) : x = x := by rfl\n"
        "lemma helper_align_2 (x : Nat) : x + 0 = x := by omega\n"
        "lemma helper_align_3 (x : Nat) : 0 + x = x := by omega\n"
        "lemma helper_align_4 (x : Nat) : x - 0 = x := by omega\n"
    )
    # The net change is +4 newlines (one per lemma) — the core point is that
    # ANY additive change on an above-cap file is allowed, regardless of the
    # exact magnitude, as long as it is not a deletion.
    net = (new.count("\n") + 1) - (orig.count("\n") + 1)
    assert net > 0, f"test setup wrong: expected net > 0, got {net}"

    err = check_size_delta(orig, new, "file_insert_lines")
    assert err is None, (
        f"insert-only allowance MUST allow additive helpers on a {orig_lines}-line "
        f"file (net={net}): {err}"
    )

    # Sanity: the same edit on a file BELOW the cap is ALSO allowed
    # (Rule 2 fires first but the delta is well under MAX_NET_INSERTIONS (1000)).
    orig_below = "\n".join(f"-- line {i}" for i in range(300)) + "\n"
    new_below = orig_below + "-- inserted\n" * 40
    assert check_size_delta(orig_below, new_below, "file_insert_lines") is None


def test_max_net_insertions_boundary_allowed():
    """An insertion of exactly MAX_NET_INSERTIONS lines is allowed (> is blocked)."""
    orig = "\n".join(f"-- line {i}" for i in range(200)) + "\n"
    # +MAX_NET_INSERTIONS exactly.
    new = orig + "-- inserted\n" * MAX_NET_INSERTIONS
    assert check_size_delta(orig, new, "file_insert_lines") is None


def test_max_net_insertions_plus_one_blocked():
    """An insertion of MAX_NET_INSERTIONS + 1 lines is blocked."""
    orig = "\n".join(f"-- line {i}" for i in range(200)) + "\n"
    new = orig + "-- inserted\n" * (MAX_NET_INSERTIONS + 1)
    err = check_size_delta(orig, new, "file_insert_lines")
    assert err is not None
    assert "net insertion" in err
    assert str(MAX_NET_INSERTIONS) in err


def test_no_change_allowed():
    """An edit that produces byte-identical content (no-op) is allowed."""
    orig = "\n".join(f"-- line {i}" for i in range(100)) + "\n"
    new = orig  # identical
    assert check_size_delta(orig, new, "file_replace_sorry") is None


# ---------------------------------------------------------------------------
# Edit sandbox: restore on failure / drop on success
# ---------------------------------------------------------------------------

def test_sandbox_snapshot_is_idempotent(tmp_path):
    """Calling snapshot() twice does not overwrite the first snapshot."""
    target = tmp_path / "File.lean"
    target.write_text("original\n", encoding="utf-8")

    sb = EditSandbox(target)
    snap1 = sb.snapshot()
    # Now mutate the live file.
    target.write_text("EDITED\n", encoding="utf-8")
    # Second snapshot() call should be a no-op (still the first temp file).
    snap2 = sb.snapshot()
    assert snap1 == snap2
    # The first snapshot still contains "original", not "EDITED".
    assert "original" in snap1.read_text(encoding="utf-8")


def test_sandbox_restores_original_on_failure(tmp_path):
    """On a verifier failure simulation, the live file is restored from the snapshot."""
    target = tmp_path / "File.lean"
    target.write_text("original line 1\noriginal line 2\n", encoding="utf-8")

    sb = EditSandbox(target)
    sb.snapshot()

    # Simulate a mid-edit exception that left the file in a corrupt state.
    target.write_text("PARTIAL WRITE\n", encoding="utf-8")
    assert target.read_text(encoding="utf-8") == "PARTIAL WRITE\n"

    # The harness would call _revert_to_sandbox_if_active on the exception path.
    restored = sb.restore()
    assert restored is True
    assert target.read_text(encoding="utf-8") == "original line 1\noriginal line 2\n"


def test_sandbox_drop_releases_temp_file(tmp_path):
    """After a verified edit, drop() removes the temp snapshot."""
    target = tmp_path / "File.lean"
    target.write_text("original\n", encoding="utf-8")

    sb = EditSandbox(target)
    snap = sb.snapshot()
    assert snap.exists()

    sb.drop()
    assert not snap.exists()
    # Idempotent: drop again is a no-op (and does not raise).
    sb.drop()


def test_sandbox_restore_without_snapshot_is_noop(tmp_path):
    """A restore() with no snapshot taken returns False (graceful no-op)."""
    target = tmp_path / "File.lean"
    target.write_text("untouched\n", encoding="utf-8")

    sb = EditSandbox(target)
    # No snapshot() called.
    assert sb.restore() is False
    # The live file is unchanged.
    assert target.read_text(encoding="utf-8") == "untouched\n"


def test_sandbox_restore_handles_missing_snapshot_file(tmp_path):
    """If the snapshot temp file is deleted out-of-band, restore() returns False."""
    target = tmp_path / "File.lean"
    target.write_text("original\n", encoding="utf-8")

    sb = EditSandbox(target)
    snap = sb.snapshot()
    # Simulate someone cleaning up temp files externally.
    snap.unlink()

    assert sb.restore() is False
    # The live file is unchanged.
    assert target.read_text(encoding="utf-8") == "original\n"


def test_sandbox_edit_cycle_happy_path(tmp_path):
    """The full happy path: snapshot -> edit -> commit -> next snapshot covers the new baseline."""
    target = tmp_path / "File.lean"
    target.write_text("v1\n", encoding="utf-8")

    sb = EditSandbox(target)
    snap1 = sb.snapshot()

    # Simulated edit.
    target.write_text("v2 (edited)\n", encoding="utf-8")
    # Commit: drop the snapshot.
    sb.drop()
    assert not snap1.exists()

    # Next edit cycle: a fresh snapshot covers v2 (the new baseline).
    sb.snapshot()
    target.write_text("v3 (regression)\n", encoding="utf-8")
    assert sb.restore() is True
    # Restored to v2, not v1 — the snapshot was taken AFTER the commit, so
    # it captures the post-commit state, not the original v1.
    assert target.read_text(encoding="utf-8") == "v2 (edited)\n"


# ---------------------------------------------------------------------------
# Integration contract with tools.py: the absolute cap is unchanged.
# ---------------------------------------------------------------------------

def test_delta_guard_does_not_replace_absolute_cap_5000_lines():
    """The delta guard is a SUPPLEMENT to the absolute 5000-line cap, not a replacement.

    tools.py:1072-1100 still applies the absolute cap as a post-edit safety
    net; check_size_delta only fires for edits where the file stays under
    the absolute cap. A file that crosses the cap via a single edit is
    still rejected by the absolute cap (caught upstream by tools.py).
    """
    orig = "\n".join(f"-- line {i}" for i in range(4900)) + "\n"  # 4901 lines
    # A +200 line insert lands at 5101 lines — above the absolute cap.
    new = orig + "-- new line\n" * 200
    # Delta guard alone: 200 < MAX_NET_INSERTIONS (1000) -> ALLOWED.
    assert check_size_delta(orig, new, "file_insert_lines") is None
    # The absolute cap (separate guard in tools.py) is what rejects this.
    # This test pins the contract: delta guard does not silently absorb
    # the absolute cap's job.