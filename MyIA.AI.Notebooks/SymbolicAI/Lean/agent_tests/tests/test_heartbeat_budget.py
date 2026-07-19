"""Unit tests for the heartbeat-budget classifier (P5a, #7477 forensic).

Loads ``heartbeat_budget.py`` DIRECTLY by file path, bypassing
``prover/__init__.py`` (which cascades the ``agent_framework`` LLM stack,
absent on a bare CPU runner). The classifier is stdlib-only and
self-contained, so these tests run everywhere (no agent_framework / Lean /
network). Mirrors ``tests/test_prover_forensic_guards.py``'s file-path
load of ``forensic_guards.py``.

Acceptance (a) of the P5a steer (ai-01 msg-...ek0f1x): a build output
containing ``maximum heartbeats (200000)`` classifies
``heartbeat_budget_exceeded`` (True), NOT ``no_progress``. The classifier
itself is the source of truth provers.py surfaces on the result dict; the
DEMO 62 Hashlife P5 wall (model-independent per ai-01 A-B c.681) must be
distinguishable from a genuinely lazy/lost agent.

Run from `agent_tests/`:
    python -m pytest tests/test_heartbeat_budget.py -q

See #7477 (prover harness forensic), See #1453 (prover co-evolution epic).
"""

from __future__ import annotations

import importlib.util
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent

_spec = importlib.util.spec_from_file_location(
    "prover_heartbeat_budget", ROOT / "prover" / "heartbeat_budget.py"
)
_hb = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_hb)

classify = _hb.output_indicates_heartbeat_budget_exceeded


# ── Acceptance (a): the DEMO 62 founder signature classifies True ──────────

class TestHeartbeatSignatureDetected:
    """Lean maxHeartbeats exhaustion MUST classify as heartbeat wall."""

    def test_founder_dem62_max_heartbeats_200000(self):
        """The exact DEMO 62 probe signature (ai-01 A-B c.681): each probe
        at L3199 timed out with this message."""
        out = ("info: ./Conway/Life/Hashlife/P5.lean:3199:0: "
               "(deterministic) timeout, maximum heartbeats (200000)")
        assert classify(out) is True

    def test_bare_maximum_heartbeats_with_count(self):
        assert classify("maximum heartbeats (200000)") is True

    def test_deterministic_timeout_alone(self):
        """The '(deterministic) timeout' half (without the explicit count).

        Lean wraps the same exhaustion this way in some output paths; both
        halves of the signature are equally diagnostic."""
        assert classify("(deterministic) timeout") is True

    def test_case_insensitive(self):
        """Capitalization varies across Lean versions / wrappers."""
        assert classify("MAXIMUM HEARTBEATS (200000)") is True
        assert classify("(Deterministic) Timeout") is True

    def test_embedded_in_multiline_build_output(self):
        """Signature embedded among other build lines is still detected
        (the per-attempt error carries the full lake output, not just the
        signature line)."""
        out = (
            "info: building...\n"
            "info: compiling Conway.Life.Hashlife.P5\n"
            "info: ./P5.lean:42:3: (deterministic) timeout, maximum heartbeats (200000)\n"
            "info: some unrelated warning\n"
        )
        assert classify(out) is True

    def test_non_default_heartbeat_budget(self):
        """A raised ceiling (set_option maxHeartbeats 400000) that is STILL
        exhausted surfaces with the higher count -- still the same wall."""
        assert classify("maximum heartbeats (400000)") is True


# ── Negative: non-heartbeat failures must NOT be mis-labelled ──────────────

class TestNonHeartbeatNotClassified:
    """A failure without the heartbeat signature must stay False, so the
    verdict does not mask a genuinely lazy/lost agent or a provider issue
    (each is its own failure class with its own ROI)."""

    def test_no_progress_prose(self):
        """A run that made no progress but never hit the heartbeat ceiling
        must NOT be flagged -- that would mis-rank a lazy agent as a
        heartbeat wall."""
        assert classify("agent produced no tactic, sorry count unchanged") is False

    def test_compile_error(self):
        assert classify("./Foo.lean:10:3: error: unknown identifier 'bar'") is False

    def test_provider_timeout_is_not_heartbeat(self):
        """A wall-clock / provider timeout (HTTP 504, no Lean heartbeat
        signature) is the provider_outage / generic-timeout class, NOT the
        heartbeat wall. The two verdicts must stay distinct (P5a rationale)."""
        assert classify("Request timed out after 300s (HTTP 504)") is False

    def test_empty_and_none(self):
        assert classify("") is False
        assert classify(None) is False

    def test_heartbeat_word_in_unrelated_prose(self):
        """The bare word 'heartbeat' (without the Lean signature shape) must
        not trigger -- guards against false positives in error prose."""
        assert classify("the agent's heartbeat monitor reported healthy") is False
        assert classify("heartbeat: 72bpm") is False


# ── Public API contract ────────────────────────────────────────────────────

class TestPublicApi:
    def test_exports_classify_function(self):
        assert "output_indicates_heartbeat_budget_exceeded" in _hb.__all__
        assert callable(classify)

    def test_returns_bool_not_truthy(self):
        """The verdict must be a real ``bool`` (consumers do
        ``if result['heartbeat_budget_exceeded']`` and persist it to JSON
        traces), not a truthy regex match object."""
        assert type(classify("maximum heartbeats (200000)")) is bool
        assert type(classify("no signature here")) is bool
