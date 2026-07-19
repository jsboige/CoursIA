"""Unit tests for the prover deadline / retry-bounding fix (#7477 P1, #1453).

Covers TWO independent wall-clock multipliers that turned a single hanging
LLM endpoint into a 1200s+ (SDK) or 2300s+ (SDK + harness) burn per call:

1. config.py `create_client` passed `max_retries=4` universally to the
   OpenAI SDK. The SDK retries a transient failure `max_retries` times,
   each waiting the FULL `request_timeout_s` (240s) — so a hanging `local`
   endpoint burned 240x5 = 1200s per call (forensic span
   `chat qwen3.6 1206.9s`). Fix: a per-provider `max_retries` override;
   the `local` provider sets 1 (a local server hangs, it does not blip).

2. workflow.py `_is_transient_error` classified read/connect timeouts as
   transient, so once the SDK finally surfaced a TimeoutError the harness
   `_is_transient_error` retry loop re-invoked `agent.run` up to
   TRANSIENT_RETRY_MAX (5) more times — each call burning another full SDK
   retry chain (forensic span `invoke_agent SearchAgent 2299.7s`). Fix: a
   dedicated `_is_timeout_error` routes timeouts to the provider-failure
   path (counted toward PROVIDER_OUTAGE_BREAKER) instead of the retry loop.

Self-contained: the heavy deps (`agent_framework` / `agent_framework_openai`
/ `dotenv` / `openai`) and the real `prover` package are stubbed in
`conftest.py` BEFORE collection. This module loads `config.py` /
`workflow.py` directly by file path via importlib.
"""

import importlib.util
import sys
import types
from pathlib import Path

import pytest

_PROVER_DIR = Path(__file__).resolve().parent


# ──────────────────────────────────────────────────────────────────────
# Submodule stubs for workflow.py's relative imports (.state / .trace /
# .knowledge / .lean_utils). conftest.py already preempted the `prover`
# package and stubbed the top-level heavy deps.
# ──────────────────────────────────────────────────────────────────────

class _GenericBase:
    """Permissive base class / callable for any stubbed symbol."""
    def __init__(self, *args, **kwargs):
        pass


def _stub_submodule(name: str, **attrs) -> types.ModuleType:
    mod = types.ModuleType(name)
    for key, value in attrs.items():
        setattr(mod, key, value)
    sys.modules[name] = mod
    return mod


# workflow.py: `from .state import SorryContext` etc. — resolve against the
# conftest-preempted `prover` package.
_stub_submodule("prover.state", SorryContext=_GenericBase)
_stub_submodule("prover.trace", TraceLogger=_GenericBase)
_stub_submodule("prover.knowledge", ProofKnowledgeBase=_GenericBase)
_stub_submodule("prover.lean_utils", count_real_sorries=lambda *a, **kw: 0)


def _load_module(name: str, path: Path):
    """importlib path-load (self-contained, no sys.path mutation)."""
    spec = importlib.util.spec_from_file_location(name, str(path))
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


# config.py has no relative imports → load as a top-level module.
config = _load_module("prover_deadline_config", _PROVER_DIR / "config.py")
# workflow.py uses relative imports (.state / .trace / ...) → load as
# `prover.workflow` so they resolve against the stubbed `prover` package.
workflow = _load_module("prover.workflow", _PROVER_DIR / "workflow.py")


# ──────────────────────────────────────────────────────────────────────
# Fake OpenAI AsyncOpenAI — records the kwargs create_client passes.
# conftest made `openai` a permissive stub; we OVERRIDE AsyncOpenAI on it
# so `from openai import AsyncOpenAI` (inside create_client) gets our fake.
# ──────────────────────────────────────────────────────────────────────

class _FakeAsyncOpenAI:
    """Records the last ctor kwargs; installed as `openai.AsyncOpenAI`."""
    last_kwargs = None

    def __init__(self, **kwargs):
        _FakeAsyncOpenAI.last_kwargs = dict(kwargs)


def _install_fake_async_openai():
    # Normal attribute set wins over the conftest permissive __getattr__
    # (PEP 562: __getattr__ fires only when normal lookup misses).
    sys.modules["openai"].AsyncOpenAI = _FakeAsyncOpenAI
    _FakeAsyncOpenAI.last_kwargs = None


# ══════════════════════════════════════════════════════════════════════
# Fix 1 — config.py create_client per-provider max_retries
# ══════════════════════════════════════════════════════════════════════

class TestCreateClientMaxRetries:
    """The `local` provider override (max_retries=1) must reach the SDK so a
    hanging local endpoint fails fast instead of burning 240s x 5."""

    def setup_method(self):
        _install_fake_async_openai()

    def test_local_provider_uses_override_max_retries_1(self):
        # The per-provider override caps a hang at 2xtimeout (480s), not 5x.
        config.create_client("local")
        assert _FakeAsyncOpenAI.last_kwargs is not None
        assert _FakeAsyncOpenAI.last_kwargs["max_retries"] == 1

    def test_remote_provider_keeps_default_max_retries_4(self):
        # zai has no `max_retries` key → function default (4) applies.
        config.create_client("zai")
        assert _FakeAsyncOpenAI.last_kwargs["max_retries"] == 4

    def test_explicit_arg_respected_when_no_provider_override(self):
        # mistral has no override → an explicit max_retries arg wins.
        config.create_client("mistral", max_retries=2)
        assert _FakeAsyncOpenAI.last_kwargs["max_retries"] == 2

    def test_provider_override_wins_over_function_arg(self):
        # The override is authoritative: even an explicit max_retries=4 cannot
        # re-introduce the 1200s hang on the local provider.
        config.create_client("local", max_retries=4)
        assert _FakeAsyncOpenAI.last_kwargs["max_retries"] == 1

    def test_timeout_passed_through_unchanged(self):
        # The fix changes only max_retries, NOT the per-call timeout (legit
        # deep reasoning still gets the full 240s).
        config.create_client("local", request_timeout_s=240.0)
        assert _FakeAsyncOpenAI.last_kwargs["timeout"] == 240.0


# ══════════════════════════════════════════════════════════════════════
# Fix 2a — workflow.py _is_timeout_error classifies sustained hangs
# ══════════════════════════════════════════════════════════════════════

class TestIsTimeoutError:
    """A timeout surfacing at the harness layer has already been retried by
    the SDK — `_is_timeout_error` must recognise it so it is NOT re-retried."""

    @pytest.mark.parametrize("message", [
        "ReadTimeout",
        "connect timeout",
        "ReadTimeoutError: timed out",
        "PoolTimeout: Pool exhausted",
        "Request timed out",
    ])
    def test_matches_timeout_markers(self, message):
        class _Exc(Exception):
            pass
        assert workflow._is_timeout_error(_Exc(message)) is True

    @pytest.mark.parametrize("message", [
        "internal server error",
        "connection reset by peer",
        "Not Found",
        "unauthorized",
    ])
    def test_does_not_match_non_timeout(self, message):
        class _Exc(Exception):
            pass
        assert workflow._is_timeout_error(_Exc(message)) is False


# ══════════════════════════════════════════════════════════════════════
# Fix 2b — workflow.py _is_transient_error no longer retries timeouts
# ══════════════════════════════════════════════════════════════════════

class TestTransientErrorExcludesTimeouts:
    """Regression guard: timeouts must NOT be classified transient (else the
    harness retry loop multiplies the SDK hang)."""

    def test_still_matches_5xx_status(self):
        class _Exc(Exception):
            status_code = 503
        assert workflow._is_transient_error(_Exc()) is True

    def test_still_matches_connection_reset(self):
        class _Exc(Exception):
            pass
        assert workflow._is_transient_error(
            _Exc("Connection reset by peer")
        ) is True

    def test_still_excludes_404(self):
        # A 404 is a config bug (bad model_id) — must never be retried.
        class _Exc(Exception):
            status_code = 404
        assert workflow._is_transient_error(_Exc()) is False

    @pytest.mark.parametrize("message", [
        "ReadTimeout",
        "connect timeout",
        "Request timed out",
    ])
    def test_no_longer_classifies_timeout_as_transient(self, message):
        # THE FIX (was True before #7477 P1): a timeout has already been
        # retried by the SDK; the harness must not re-retry it.
        class _Exc(Exception):
            pass
        assert workflow._is_transient_error(_Exc(message)) is False


# ══════════════════════════════════════════════════════════════════════
# Routing invariant — timeout and transient are mutually exclusive
# ══════════════════════════════════════════════════════════════════════

class TestTimeoutTransientMutualExclusion:
    """A timeout routes to provider_failed (skip harness retry); a 5xx /
    connection-reset routes to the retry loop. The two never overlap, so the
    AgentExecutor `elif _is_timeout_error` / `elif _is_transient_error`
    branches are unambiguous."""

    def test_timeout_is_only_timeout_not_transient(self):
        class _Exc(Exception):
            pass
        exc = _Exc("ReadTimeout: timed out")
        assert workflow._is_timeout_error(exc) is True
        assert workflow._is_transient_error(exc) is False

    def test_5xx_is_only_transient_not_timeout(self):
        class _Exc(Exception):
            status_code = 502
        exc = _Exc()
        assert workflow._is_transient_error(exc) is True
        assert workflow._is_timeout_error(exc) is False
