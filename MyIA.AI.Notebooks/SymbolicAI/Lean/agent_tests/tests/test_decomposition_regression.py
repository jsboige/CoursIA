"""Unit tests for the decomposition-regression classifier (P3, #7477 forensic).

Loads ``decomposition_regression.py`` DIRECTLY by file path, bypassing
``prover/__init__.py`` (which cascades the ``agent_framework`` LLM stack,
absent on a bare CPU runner). The classifier is stdlib-only and
self-contained, so these tests run everywhere (no agent_framework / Lean /
network). Mirrors ``tests/test_heartbeat_budget.py``'s file-path load.

The founding incident (forensic #7477): L2551 grew 4->8 (net +4 sorry) with
``verified_tactic_count == 0`` in all 11 Hashlife/conway family runs, yet
scored ``structural_progress: true`` -- a net sorry-INCREASE decomposition
with ZERO build-verified tactics, mis-labelled as progress. This corrupts
forensic ROI: an unproven sub-sorry spray looks indistinguishable from a
genuine restructuring.

P3 separates the two: an increase is structural progress only when at least
one tactic was build-verified; with zero verified tactics it is a
decomposition-regression. The macro-signal ``verified_tactic_count == 0`` is
the forensic's own cited diagnostic.

Run from `agent_tests/`:
    python -m pytest tests/test_decomposition_regression.py -q

See #7477 (prover harness forensic), See #1453 (prover co-evolution epic).
"""

from __future__ import annotations

import importlib.util
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent

_spec = importlib.util.spec_from_file_location(
    "prover_decomposition_regression",
    ROOT / "prover" / "decomposition_regression.py",
)
_dr = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_dr)

classify = _dr.is_decomposition_regression
same_count_churn = _dr.is_same_count_zero_verified
worsened_unproven = _dr.is_worsened_unproven


# ── Acceptance: the founder incident classifies as regression ──────────────

class TestRegressionDetected:
    """A net-sorry-INCREASE with zero verified tactics IS a regression."""

    def test_founder_l2551_four_to_eight(self):
        """The exact forensic #7477 founding incident: 4 -> 8, verified=0."""
        assert classify(8, 4, 0) is True

    def test_large_runaway_spray(self):
        """1 -> 10 with nothing verified is runaway sub-sorry spraying."""
        assert classify(10, 1, 0) is True

    def test_minimal_increase_one(self):
        """Even a minimal 4 -> 5 with zero verified is a regression
        (the signal is the unproven growth, not its magnitude)."""
        assert classify(5, 4, 0) is True

    def test_huge_original_with_growth(self):
        """100 -> 101, verified=0 -- still a regression (growth + unproven)."""
        assert classify(101, 100, 0) is True


# ── Negative: legitimate progress must NOT be mis-labelled ────────────────

class TestLegitimateProgressNotFlagged:
    """A decomposition with at least one verified tactic is real structural
    progress and must stay unflagged (preserves the FX-8 comment's explicit
    intent: 'a decomposition (final > original, any verified count) ... stay
    structural progress')."""

    def test_decomposition_with_two_verified(self):
        """4 -> 6 with 2 build-verified sub-goals = genuine restructuring."""
        assert classify(6, 4, 2) is False

    def test_decomposition_with_one_verified(self):
        """Even a single verified tactic means the decomposition produced a
        compiling, verified sub-goal -- not a spray."""
        assert classify(6, 4, 1) is False

    def test_large_increase_with_verified(self):
        """1 -> 10 but 1 tactic verified: the agent proved something in the
        decomposition, so it is not a pure regression."""
        assert classify(10, 1, 1) is False


class TestNonIncreaseNotFlagged:
    """A same-count or drop is NEVER a regression by this signal (the
    increase is the defining condition). Same-count is the FX-8 /
    statement-mutation guard's territory; a drop is real progress."""

    def test_same_count_zero_verified(self):
        """4 -> 4, verified=0 is handled by FX-8 / stmt-mutation, not P3."""
        assert classify(4, 4, 0) is False

    def test_drop_zero_verified(self):
        """A sorry DROP is never a regression here (it is progress, even if
        the FX-6 guard separately demotes a drop with 0 verified)."""
        assert classify(2, 4, 0) is False

    def test_drop_to_zero(self):
        assert classify(0, 4, 1) is False

    def test_same_count_with_verified(self):
        assert classify(4, 4, 2) is False


# ── Legacy / contract ──────────────────────────────────────────────────────

class TestLegacyAndContract:
    def test_none_verified_preserves_prior_behaviour(self):
        """A legacy caller that does not track verified tactics (None) cannot
        be classified -- preserve prior behaviour rather than guess."""
        assert classify(8, 4, None) is False

    def test_exports_classify_function(self):
        assert "is_decomposition_regression" in _dr.__all__
        assert callable(classify)

    def test_returns_bool_not_truthy(self):
        """The verdict is persisted to JSON traces and consumed by
        ``if result['decomposition_regression']``; it must be a real bool."""
        assert type(classify(8, 4, 0)) is bool
        assert type(classify(6, 4, 2)) is bool


# ── #11421: same-count + vtc=0 symmetry guard ──────────────────────────────

class TestSameCountZeroVerified:
    """#11421: P3 covers the net-INCREASE case; a kept SAME-COUNT snapshot
    (provers.py:890-898) also needs >= 1 verified tactic to count as
    structural progress. final == original with vtc=0 is text churn."""

    def test_same_count_zero_verified_flags_churn(self):
        assert same_count_churn(4, 4, 0) is True

    def test_same_count_with_verified_is_progress(self):
        assert same_count_churn(4, 4, 1) is False
        assert same_count_churn(4, 4, 3) is False

    def test_increase_is_not_this_guards_territory(self):
        """A net increase is P3's case, not this equality guard's."""
        assert same_count_churn(8, 4, 0) is False

    def test_drop_is_not_this_guards_territory(self):
        """A drop is FX-6's territory (statement-mutation guard)."""
        assert same_count_churn(2, 4, 0) is False

    def test_none_verified_preserves_prior_behaviour(self):
        """Legacy caller with no verified-tactic tracking: cannot classify."""
        assert same_count_churn(4, 4, None) is False

    def test_returns_real_bool(self):
        assert type(same_count_churn(4, 4, 0)) is bool

    def test_exported_in_all(self):
        assert "is_same_count_zero_verified" in _dr.__all__

# ── #1453 iter-2: never persist a worsened state ───────────────────────────

class TestWorsenedUnproven:
    """The write-guard predicate: a run that ENDED with MORE sorries than it
    started and proved nothing must be reverted + marked REGRESSED, never
    persisted as success (L2551 4->8, L849 10->11)."""

    def test_flags_l2551_founder(self):
        """The founding incident: 4 -> 8 with no proof is a worsened unproven
        state (the file was persisted as structural_only, success=True)."""
        assert worsened_unproven(8, 4, False) is True

    def test_flags_l849_increase(self):
        """10 -> 11, no proof -- same class, smaller magnitude."""
        assert worsened_unproven(11, 10, False) is True

    def test_same_count_not_its_territory(self):
        """final == original is not a worsened state (FX-8 / equality guard)."""
        assert worsened_unproven(4, 4, False) is False

    def test_drop_not_its_territory(self):
        """A sorry DROP is real progress, never a worsened state."""
        assert worsened_unproven(2, 4, False) is False

    def test_proof_found_exempt(self):
        """Proving the target IS progress even if collateral sorries grew --
        reverting would throw away the proof."""
        assert worsened_unproven(8, 4, True) is False

    def test_returns_real_bool(self):
        assert type(worsened_unproven(8, 4, False)) is bool

    def test_exported_in_all(self):
        assert "is_worsened_unproven" in _dr.__all__



# ── #1453 iter-3: build-aware blind spot ─────────────────────────────────────

class TestBuildAwareBlindSpot:
    """#1453 iter-3: the write-guard compared TEXT counts, so a build that
    reveals an implicit sorry (apply?/exact?/solve_by_elim finding nothing)
    grows the BUILD-AWARE count 2->3 while the text stays 2==2. The text guard
    passes and the kept-snapshot branch persists a file whose effective count
    rose. The guard must therefore be re-checked with the build-aware count,
    which is exactly what is_worsened_unproven does once given that count."""

    def test_text_same_count_passes_old_guard(self):
        """2 == 2 text: the iter-2 guard sees no worsening (the blind spot)."""
        assert worsened_unproven(2, 2, False) is False

    def test_buildaware_rise_flags_with_build_count(self):
        """Build reveals 2 -> 3: the SAME predicate flags it once fed the
        build-aware count. This is the iter-3 re-check."""
        assert worsened_unproven(3, 2, False) is True

    def test_buildaware_rise_still_respects_proof_exemption(self):
        """A build-aware rise with a proof is still exempt (revert would throw
        the proof away)."""
        assert worsened_unproven(3, 2, True) is False
