"""Unit tests for ``prover.config.create_client`` provider-aware retry policy.

Covers the #7477 P1 transport fix: a hanging endpoint (server accepts the
connection then stalls) burns ``max_retries + 1`` full per-attempt timeouts.
With the legacy flat ``max_retries=4`` a single hung ``local`` (vLLM/qwen3.6)
call cost up to ``5 x 240s = 1200s`` — confirmed by forensic span evidence
``[ERROR] chat qwen3.6 1206.9s`` (#7477). The fix makes ``max_retries``
provider-aware: remote APIs keep 4 (z.ai 5xx/reset resilience, 2026-05-12),
the ``local`` vLLM drops to 1 (a local server's failure mode is a GPU-stall
hang, not 5xx; retrying just re-burns the timeout).

Run from ``agent_tests/``::

    python -m pytest tests/test_config_create_client.py -q
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

# Make `prover/` importable regardless of how pytest was invoked (same
# bootstrap convention as tests/test_prover_guards.py).
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT))

from prover import config as cfg  # noqa: E402


# ──────────────────────────────────────────────────────────────────────────
# Test fakes — capture the kwargs that create_client forwards to the OpenAI
# SDK + the agent-framework client wrapper, without any network I/O.
# ──────────────────────────────────────────────────────────────────────────


class _RecordingAsyncOpenAI:
    """Stand-in for ``openai.AsyncOpenAI`` that records construction kwargs."""

    def __init__(self, **kwargs):
        self.kwargs = kwargs


class _NoopFrameworkClient:
    """Stand-in for ``OpenAIChatCompletionClient`` — store kwargs, do nothing."""

    def __init__(self, *args, **kwargs):
        self.args = args
        self.kwargs = kwargs


@pytest.fixture
def isolated_create_client(monkeypatch):
    """Patch the two construction sites create_client touches.

    ``create_client`` resolves ``AsyncOpenAI`` via a local
    ``from openai import AsyncOpenAI`` at call time, so patching the
    ``openai.AsyncOpenAI`` attribute is picked up. ``OpenAIChatCompletionClient``
    is a module-level binding inside ``prover.config``, so patch it there.
    """
    monkeypatch.setattr("openai.AsyncOpenAI", _RecordingAsyncOpenAI)
    monkeypatch.setattr(cfg, "OpenAIChatCompletionClient", _NoopFrameworkClient)
    yield


# ──────────────────────────────────────────────────────────────────────────
# Policy shape (pins the documented #7477 P1 contract)
# ──────────────────────────────────────────────────────────────────────────


def test_provider_retry_policy_dict_shape():
    """The policy dict names exactly the local provider, default 4 for the rest."""
    assert cfg.PROVIDER_MAX_RETRIES == {"local": 1}
    assert cfg._DEFAULT_MAX_RETRIES == 4


def test_local_hang_cost_bounded_under_policy():
    """Documented #7477 P1 bound: a hung local call is now capped under the
    forensic 1200s burn.

    Before the fix a hung ``local`` call cost ``(1 + 4) * 240 = 1200s``; under
    the policy it costs ``(1 + 1) * 240 = 480s``. This test pins the intent so
    a future bump of the local retry count trips it.
    """
    local_retries = cfg.PROVIDER_MAX_RETRIES["local"]
    import inspect
    timeout_default = inspect.signature(cfg.create_client).parameters[
        "request_timeout_s"
    ].default
    worst_case_hang_s = (1 + local_retries) * timeout_default
    assert worst_case_hang_s <= 600, (
        f"local hang worst-case {worst_case_hang_s}s exceeds the 600s P1 bound; "
        "bumping local max_retries re-introduces the 1200s forensic burn (#7477)."
    )
    # And it is strictly better than the pre-fix 1200s baseline.
    assert worst_case_hang_s < 1200


# ──────────────────────────────────────────────────────────────────────────
# Per-provider max_retries resolution
# ──────────────────────────────────────────────────────────────────────────


def test_local_provider_drops_to_one_retry(isolated_create_client):
    """The local (vLLM) provider resolves to max_retries=1 (hang-bounded)."""
    client = cfg.create_client("local")
    # _RecordingAsyncOpenAI stored its kwargs on the instance; the framework
    # wrapper received that instance as async_client.
    async_client = client.kwargs["async_client"]
    assert async_client.kwargs["max_retries"] == 1


@pytest.mark.parametrize("provider", ["zai", "openrouter", "mistral"])
def test_remote_providers_keep_default_four_retries(provider, isolated_create_client):
    """Remote API providers keep max_retries=4 (z.ai 5xx/reset resilience)."""
    client = cfg.create_client(provider)
    async_client = client.kwargs["async_client"]
    assert async_client.kwargs["max_retries"] == 4


def test_explicit_max_retries_overrides_provider_policy(isolated_create_client):
    """An explicit max_retries wins over the per-provider default — even for local."""
    client = cfg.create_client("local", max_retries=3)
    async_client = client.kwargs["async_client"]
    assert async_client.kwargs["max_retries"] == 3


def test_explicit_zero_max_retries_honored(isolated_create_client):
    """max_retries=0 is a legitimate explicit override (no SDK retries)."""
    client = cfg.create_client("zai", max_retries=0)
    async_client = client.kwargs["async_client"]
    assert async_client.kwargs["max_retries"] == 0


# ──────────────────────────────────────────────────────────────────────────
# Non-retry kwargs still flow through (regression guards)
# ──────────────────────────────────────────────────────────────────────────


def test_request_timeout_passed_through(isolated_create_client):
    """The request_timeout_s kwarg still reaches the SDK client."""
    client = cfg.create_client("zai", request_timeout_s=99.0)
    async_client = client.kwargs["async_client"]
    assert async_client.kwargs["timeout"] == 99.0


def test_model_and_base_url_wired_from_providers(isolated_create_client):
    """model (framework client) + base_url/api_key (SDK client) come from PROVIDERS."""
    client = cfg.create_client("local", model_key="reasoning")
    # Framework wrapper received the model id from PROVIDERS.
    assert client.kwargs["model"] == cfg.PROVIDERS["local"]["models"]["reasoning"]
    # SDK client received the provider's base_url + api_key.
    async_client = client.kwargs["async_client"]
    assert async_client.kwargs["base_url"] == cfg.PROVIDERS["local"]["base_url"]
    assert async_client.kwargs["api_key"] == cfg.PROVIDERS["local"]["api_key"]


def test_signature_accepts_optional_max_retries():
    """The signature exposes max_retries as Optional (None => provider policy).

    Guards against an accidental revert to a flat ``int = 4`` default, which
    would silently re-introduce the 1200s local-hang burn for every caller
    that relies on the default (all 7 call sites in agents.py/provers.py).
    """
    import inspect

    sig = inspect.signature(cfg.create_client)
    assert sig.parameters["max_retries"].default is None
