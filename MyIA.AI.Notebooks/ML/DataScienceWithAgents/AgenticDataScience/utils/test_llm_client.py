#!/usr/bin/env python3
"""Pytest suite for `AgenticDataScience/utils/llm_client.py` (LLMClient + litellm wrapper).

Co-located with the module under `utils/`. CPU-only, no network, no real LLM
call. The module imports `litellm` at top level (not installed on every worker
machine) and `config.providers` via a relative package import, so this suite:

  1. Installs a fake `litellm` module in `sys.modules` BEFORE importing
     `utils.llm_client` (same mocking pattern as `Argument_Analysis/tests/
     test_runner.py` uses for `semantic_kernel`).
  2. Puts the `AgenticDataScience/` dir on `sys.path` so both `config` and
     `utils` packages resolve the way the notebook runtime expects.

The module is the unified LLM client consumed by 10 Lab notebooks (Day4-Day7,
Lab8-Lab17) and had 0 dedicated Python test coverage before this PR.

A captured-call fixture (monkeypatching `litellm.completion`) lets us assert
exactly how `LLMClient` builds the `call_kwargs` per provider (api_base for
vLLM/LM Studio, api_key threading, system/prompt ordering, max_tokens) without
any real HTTP traffic.
"""
from __future__ import annotations

import sys
import types
from pathlib import Path

import pytest

# --------------------------------------------------------------------------
# Module bootstrap: mock litellm, put AgenticDataScience on sys.path, import.
# --------------------------------------------------------------------------

_AGDS_DIR = Path(__file__).resolve().parent.parent  # .../AgenticDataScience/


@pytest.fixture(autouse=True)
def _isolate_default_client(monkeypatch):
    """Reset the module-level singleton so tests do not leak client state."""
    if "utils.llm_client" in sys.modules:
        sys.modules["utils.llm_client"]._default_client = None
    yield
    if "utils.llm_client" in sys.modules:
        sys.modules["utils.llm_client"]._default_client = None


def _ensure_loaded():
    """Idempotently mock litellm + load utils.llm_client via package path."""
    if "litellm" not in sys.modules:
        fake = types.ModuleType("litellm")
        fake.completion = lambda **kw: _FakeResponse("mocked")
        sys.modules["litellm"] = fake
    if str(_AGDS_DIR) not in sys.path:
        sys.path.insert(0, str(_AGDS_DIR))
    if "utils.llm_client" not in sys.modules:
        import importlib
        mod = importlib.import_module("utils.llm_client")
        return mod
    return sys.modules["utils.llm_client"]


class _FakeMessage:
    def __init__(self, content):
        self.content = content


class _FakeChoice:
    def __init__(self, content):
        self.message = _FakeMessage(content)


class _FakeResponse:
    def __init__(self, content):
        self.choices = [_FakeChoice(content)]


_ensure_loaded()
llm_client = sys.modules["utils.llm_client"]
providers = sys.modules["config.providers"]
ProviderConfig = providers.ProviderConfig
ProviderType = providers.ProviderType
LLMClient = llm_client.LLMClient


# --------------------------------------------------------------------------
# Helpers
# --------------------------------------------------------------------------


def _capturing_completion(calls):
    """Return a fake litellm.completion that records its kwargs."""

    def _impl(**kwargs):
        calls.append(kwargs)
        return _FakeResponse("RESPONSE")

    return _impl


def _cfg(provider, **overrides):
    base = dict(provider=provider, model="m", base_url="http://x/v1", api_key=None)
    base.update(overrides)
    return ProviderConfig(**base)


# --------------------------------------------------------------------------
# __init__ / __repr__
# --------------------------------------------------------------------------


def test_init_explicit_config_threads_model():
    cfg = _cfg(ProviderType.OPENAI, model="gpt-4o")
    c = LLMClient(config=cfg)
    assert c.config is cfg
    assert c.model == "openai/gpt-4o"  # litellm prefix for OpenAI


def test_init_vllm_model_uses_openai_prefix():
    cfg = _cfg(ProviderType.VLLM, model="qwen3.6-35b-a3b")
    c = LLMClient(config=cfg)
    assert c.model == "openai/qwen3.6-35b-a3b"  # vLLM is OpenAI-API compatible


def test_repr_includes_provider_and_model():
    cfg = _cfg(ProviderType.GEMINI, model="gemini-3.1-pro")
    c = LLMClient(config=cfg)
    r = repr(c)
    assert "gemini" in r
    assert "gemini-3.1-pro" in r


# --------------------------------------------------------------------------
# generate() — call_kwargs construction per provider
# --------------------------------------------------------------------------


def test_generate_passes_model_and_temperature(monkeypatch):
    calls = []
    monkeypatch.setattr(llm_client, "completion", _capturing_completion(calls))
    c = LLMClient(config=_cfg(ProviderType.OPENAI))
    out = c.generate("hello", temperature=0.1)
    assert out == "RESPONSE"
    assert calls[0]["model"] == "openai/m"
    assert calls[0]["temperature"] == 0.1


def test_generate_orders_system_before_user(monkeypatch):
    calls = []
    monkeypatch.setattr(llm_client, "completion", _capturing_completion(calls))
    c = LLMClient(config=_cfg(ProviderType.OPENAI))
    c.generate("user prompt", system="system prompt")
    msgs = calls[0]["messages"]
    assert msgs == [
        {"role": "system", "content": "system prompt"},
        {"role": "user", "content": "user prompt"},
    ]


def test_generate_no_system_message_when_absent(monkeypatch):
    calls = []
    monkeypatch.setattr(llm_client, "completion", _capturing_completion(calls))
    c = LLMClient(config=_cfg(ProviderType.OPENAI))
    c.generate("user prompt")
    assert calls[0]["messages"] == [{"role": "user", "content": "user prompt"}]


def test_generate_omits_api_base_for_openai(monkeypatch):
    calls = []
    monkeypatch.setattr(llm_client, "completion", _capturing_completion(calls))
    c = LLMClient(config=_cfg(ProviderType.OPENAI, base_url="http://openai/v1"))
    c.generate("hi")
    assert "api_base" not in calls[0]


def test_generate_adds_api_base_for_vllm(monkeypatch):
    calls = []
    monkeypatch.setattr(llm_client, "completion", _capturing_completion(calls))
    c = LLMClient(config=_cfg(ProviderType.VLLM, base_url="http://localhost:8000/v1"))
    c.generate("hi")
    assert calls[0]["api_base"] == "http://localhost:8000/v1"


def test_generate_adds_api_base_for_lmstudio(monkeypatch):
    calls = []
    monkeypatch.setattr(llm_client, "completion", _capturing_completion(calls))
    c = LLMClient(config=_cfg(ProviderType.LMSTUDIO, base_url="http://localhost:1234/v1"))
    c.generate("hi")
    assert calls[0]["api_base"] == "http://localhost:1234/v1"


def test_generate_threads_api_key_when_present(monkeypatch):
    calls = []
    monkeypatch.setattr(llm_client, "completion", _capturing_completion(calls))
    c = LLMClient(config=_cfg(ProviderType.OPENAI, api_key="sk-test"))
    c.generate("hi")
    assert calls[0]["api_key"] == "sk-test"


def test_generate_omits_api_key_when_none(monkeypatch):
    calls = []
    monkeypatch.setattr(llm_client, "completion", _capturing_completion(calls))
    c = LLMClient(config=_cfg(ProviderType.OPENAI, api_key=None))
    c.generate("hi")
    assert "api_key" not in calls[0]


# --------------------------------------------------------------------------
# max_tokens handling — regression on the falsy-zero bug
# --------------------------------------------------------------------------


def test_generate_max_tokens_positive_is_passed(monkeypatch):
    calls = []
    monkeypatch.setattr(llm_client, "completion", _capturing_completion(calls))
    c = LLMClient(config=_cfg(ProviderType.OPENAI))
    c.generate("hi", max_tokens=128)
    assert calls[0]["max_tokens"] == 128


def test_generate_max_tokens_none_is_omitted(monkeypatch):
    calls = []
    monkeypatch.setattr(llm_client, "completion", _capturing_completion(calls))
    c = LLMClient(config=_cfg(ProviderType.OPENAI))
    c.generate("hi")  # max_tokens defaults to None
    assert "max_tokens" not in calls[0]


def test_generate_max_tokens_zero_is_passed_not_swallowed(monkeypatch):
    """Regression: `if max_tokens:` used to treat 0 as falsy and silently drop
    it. The fix uses `if max_tokens is not None:` so max_tokens=0 (a valid
    int, = generate zero tokens) is forwarded to litellm as documented by the
    `max_tokens: Limite de tokens` docstring contract.
    """
    calls = []
    monkeypatch.setattr(llm_client, "completion", _capturing_completion(calls))
    c = LLMClient(config=_cfg(ProviderType.OPENAI))
    c.generate("hi", max_tokens=0)
    assert calls[0]["max_tokens"] == 0


def test_generate_extra_kwargs_are_forwarded(monkeypatch):
    calls = []
    monkeypatch.setattr(llm_client, "completion", _capturing_completion(calls))
    c = LLMClient(config=_cfg(ProviderType.OPENAI))
    c.generate("hi", top_p=0.9, stop=["END"])
    assert calls[0]["top_p"] == 0.9
    assert calls[0]["stop"] == ["END"]


# --------------------------------------------------------------------------
# chat() — messages list passthrough
# --------------------------------------------------------------------------


def test_chat_passes_messages_list(monkeypatch):
    calls = []
    monkeypatch.setattr(llm_client, "completion", _capturing_completion(calls))
    c = LLMClient(config=_cfg(ProviderType.OPENAI))
    history = [
        {"role": "user", "content": "q1"},
        {"role": "assistant", "content": "a1"},
        {"role": "user", "content": "q2"},
    ]
    out = c.chat(history, temperature=0.3)
    assert out == "RESPONSE"
    assert calls[0]["messages"] == history
    assert calls[0]["temperature"] == 0.3


def test_chat_adds_api_base_for_lmstudio(monkeypatch):
    calls = []
    monkeypatch.setattr(llm_client, "completion", _capturing_completion(calls))
    c = LLMClient(config=_cfg(ProviderType.LMSTUDIO, base_url="http://lmstudio/v1"))
    c.chat([{"role": "user", "content": "x"}])
    assert calls[0]["api_base"] == "http://lmstudio/v1"


# --------------------------------------------------------------------------
# get_client / generate module-level helpers — singleton
# --------------------------------------------------------------------------


def test_get_client_is_singleton(monkeypatch):
    # Patch completion so LLMClient() never hits the network during construction
    # (it only builds config; generate/chat call completion).
    monkeypatch.setattr(llm_client, "completion", _capturing_completion([]))
    # get_client() with no .env uses Settings defaults (active_provider=vllm);
    # that is fine — we only assert identity, not the provider value.
    a = llm_client.get_client()
    b = llm_client.get_client()
    assert a is b


def test_module_generate_uses_singleton(monkeypatch):
    calls = []
    monkeypatch.setattr(llm_client, "completion", _capturing_completion(calls))
    out = llm_client.generate("hi", max_tokens=5)
    assert out == "RESPONSE"
    assert calls[0]["messages"] == [{"role": "user", "content": "hi"}]
    assert calls[0]["max_tokens"] == 5
