# -*- coding: utf-8 -*-
"""Unit tests for the prover P1b hang-prone-provider timeout policy (#7477).

``_is_transient_error`` (prover/workflow.py) classifies which provider/network
errors are worth retrying at the workflow layer. Forensic #7477 showed that a
*hanging* local endpoint (vLLM / qwen3.6 GPU stall) burned the whole wall-clock
budget on a single logical call: the OpenAI SDK retried the timeout
``max_retries`` times (each re-burning ``request_timeout_s``), then the
workflow layer re-classified the timeout as transient and retried
``TRANSIENT_RETRY_MAX`` (5) more times — span evidence ``[ERROR] chat qwen3.6
1206.9s``, ``invoke_agent SearchAgent 2299.7s``.

P1a (config.py, #7482) capped the SDK retries for ``local`` to 1. P1b (this
change) stops the *workflow* layer from multiplying the burn: for a
hang-prone provider (``HANG_PRONE_PROVIDERS = {"local"}``) a timeout is a
definitive provider failure (non-transient), so it flows to the
``_provider_failed`` branch and the outage-breaker (``PROVIDER_OUTAGE_BREAKER``)
terminates the run cleanly instead of retrying.

These tests pin the provider-aware carve-out. Non-vacuous: on the unpatched
``_is_transient_error`` (no ``provider`` arg), every local-timeout case below
returns ``True`` (transient → retried 5×) — the exact burn we eliminate.

Run from `agent_tests/`:
    python -m pytest tests/test_prover_p1b_timeout.py -q

See #7477 (prover forensic) and #1453 (prover robustness epic).
"""

from __future__ import annotations

import sys
from pathlib import Path

# Make `prover/` importable regardless of how pytest was invoked (same
# bootstrap convention as test_prover_guards.py).
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT))

from prover.workflow import (  # noqa: E402
    HANG_PRONE_PROVIDERS,
    _is_transient_error,
)
from prover.agents import _stamp_provider  # noqa: E402


class _FakeStatusError(Exception):
    """An exception exposing a structured ``status_code`` (httpx/openai-style)."""

    def __init__(self, message: str, status_code: int):
        super().__init__(message)
        self.status_code = status_code


# ---------------------------------------------------------------------------
# P1b core: hang-prone provider timeout = NOT transient (the fix).
# ---------------------------------------------------------------------------

def test_hang_prone_providers_contains_local():
    """The carve-out targets exactly the local vLLM provider."""
    assert "local" in HANG_PRONE_PROVIDERS


def test_local_timeout_is_not_transient():
    """A local-provider timeout is a GPU-stall hang — must NOT be retried.

    Non-vacuous: on the unpatched function (no provider arg) this returns True
    (the 1206.9s burn). With P1b it returns False → flows to _provider_failed
    → outage-breaker.
    """
    for msg in ("Read timed out", "read timeout", "connect timeout",
                "The request timed out.", "Operation timed out after 240s"):
        assert _is_transient_error(RuntimeError(msg), provider="local") is False, (
            f"local timeout must not be transient (msg={msg!r})"
        )


def test_local_timeout_not_transient_even_with_default_provider_arg():
    """provider defaults to None → unknown provider → keep retry behavior.

    Backward-compat guard: an agent WITHOUT the stamp (e.g. a test fixture or
    a future agent not built via create_*_agent) keeps the legacy
    timeout=transient behavior. Only an explicit hang-prone provider opts out.
    """
    assert _is_transient_error(RuntimeError("read timeout")) is True
    assert _is_transient_error(RuntimeError("read timeout"), provider=None) is True


# ---------------------------------------------------------------------------
# P1b does NOT weaken the remote-provider retry behavior (regression fence).
# ---------------------------------------------------------------------------

def test_remote_timeout_still_transient():
    """Remote providers (zai/openrouter/mistral) keep retrying timeouts — a
    remote 504 / read-timeout can resolve on retry (cheap fast-fail)."""
    for provider in ("zai", "openrouter", "mistral"):
        assert _is_transient_error(
            RuntimeError("read timeout"), provider=provider
        ) is True, f"remote {provider} timeout must stay transient"


def test_local_5xx_still_transient():
    """P1b carves out ONLY timeouts for local providers. A genuine 5xx from
    a local server (rare, but possible on a restart) still retries."""
    assert _is_transient_error(
        RuntimeError("500 internal server error"), provider="local"
    ) is True


def test_local_connection_reset_still_transient():
    """Connection reset is a transient transport blip, not a hang — still
    retried even for local providers."""
    assert _is_transient_error(
        RuntimeError("connection reset by peer"), provider="local"
    ) is True


# ---------------------------------------------------------------------------
# 4xx guard + structured-status path take priority over the timeout carve-out.
# ---------------------------------------------------------------------------

def test_4xx_guard_wins_over_local_timeout():
    """A 404 (config bug) is never transient, even for a local provider and
    even when the message also contains 'timeout'."""
    assert _is_transient_error(
        RuntimeError("404 not found: model timeout"), provider="local"
    ) is False


def test_structured_504_is_transient_regardless_of_provider():
    """A structured status_code=504 (gateway timeout) is transient via the
    status-code path (step 1) — provider is irrelevant there. A local server
    never serves a structured 504, but if agent_framework surfaces one it is
    still treated as transient (the carve-out only catches string timeouts)."""
    err = _FakeStatusError("gateway timeout", status_code=504)
    assert _is_transient_error(err, provider="local") is True
    assert _is_transient_error(err, provider="openrouter") is True


def test_structured_404_not_transient_regardless_of_provider():
    """A structured 4xx (config bug) is never transient, for any provider."""
    err = _FakeStatusError("not found", status_code=404)
    assert _is_transient_error(err, provider="local") is False
    assert _is_transient_error(err, provider="openrouter") is False


# ---------------------------------------------------------------------------
# _stamp_provider (agents.py) tags the agent so the retry site can read it.
# ---------------------------------------------------------------------------

def test_stamp_provider_sets_attribute():
    """_stamp_provider tags an arbitrary object with _prover_provider and
    returns it (the Agent object allows attribute assignment — no __slots__)."""

    class _FakeAgent:
        pass

    agent = _FakeAgent()
    assert not hasattr(agent, "_prover_provider")
    returned = _stamp_provider(agent, "local")
    assert returned is agent  # returns the same object
    assert agent._prover_provider == "local"
