"""Unit tests for utils/llm_client.py (Track2-GoogleADK unified LLM client).

Covers the deterministic, network-free logic of LLMClient:
  - __init__ explicit config (no .env)
  - generate(): message assembly (system optional, user), call_kwargs assembly
    (api_base ONLY for vllm/lmstudio, api_key conditional, max_tokens conditional,
    **kwargs merge), response extraction
  - chat(): same kwargs assembly over a provided message list
  - __repr__ format
  - get_client() singleton behavior
  - module-level generate() delegating to the singleton

litellm.completion is a live network call requiring API keys and a reachable
provider, so it is mocked (unittest.mock.patch). The module under test is
exercised in full; only the network boundary is stubbed — standard unit-test
practice for a thin client wrapper. No real API calls are made.
"""
import sys
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

# Make the Track2-GoogleADK package importable (config/ + utils/ siblings).
_PKG = Path(__file__).resolve().parent.parent
if str(_PKG) not in sys.path:
    sys.path.insert(0, str(_PKG))

from config.providers import ProviderConfig, ProviderType  # noqa: E402
from utils import llm_client  # noqa: E402
from utils.llm_client import LLMClient, get_client  # noqa: E402


def _cfg(provider, model=None, api_key=None, base_url=None):
    """Build an explicit ProviderConfig (no .env)."""
    return ProviderConfig(
        provider=provider,
        model=model or "gpt-4o",
        api_key=api_key,
        base_url=base_url,
    )


def _fake_response(text="pong"):
    """A litellm-style response object exposing choices[0].message.content."""
    msg = MagicMock()
    msg.content = text
    choice = MagicMock()
    choice.message = msg
    resp = MagicMock()
    resp.choices = [choice]
    return resp


# --- LLMClient.__init__ ----------------------------------------------------

def test_init_explicit_config_sets_model():
    c = _cfg(ProviderType.OPENAI, model="gpt-4o")
    client = LLMClient(config=c)
    assert client.config is c
    # LiteLLM models are prefixed with the provider key: openai/gpt-4o.
    assert client.model == "openai/gpt-4o"


def test_init_gemini_provider_prefix():
    client = LLMClient(config=_cfg(ProviderType.GEMINI, model="gemini-3.1-pro"))
    assert client.model.startswith("gemini/")


# --- generate(): message assembly ------------------------------------------

@patch("utils.llm_client.completion")
def test_generate_user_only_message(mock_completion):
    mock_completion.return_value = _fake_response("hello")
    client = LLMClient(config=_cfg(ProviderType.OPENAI))
    out = client.generate("hi")
    assert out == "hello"
    sent = mock_completion.call_args.kwargs
    assert sent["messages"] == [{"role": "user", "content": "hi"}]


@patch("utils.llm_client.completion")
def test_generate_prepends_system_message(mock_completion):
    mock_completion.return_value = _fake_response("ok")
    client = LLMClient(config=_cfg(ProviderType.OPENAI))
    client.generate("hi", system="be brief")
    sent = mock_completion.call_args.kwargs
    assert sent["messages"] == [
        {"role": "system", "content": "be brief"},
        {"role": "user", "content": "hi"},
    ]


@patch("utils.llm_client.completion")
def test_generate_empty_system_is_not_added(mock_completion):
    """system=None/empty must not create an empty system message."""
    mock_completion.return_value = _fake_response("ok")
    client = LLMClient(config=_cfg(ProviderType.OPENAI))
    client.generate("hi", system="")
    sent = mock_completion.call_args.kwargs
    assert sent["messages"] == [{"role": "user", "content": "hi"}]


@patch("utils.llm_client.completion")
def test_generate_temperature_forwarded(mock_completion):
    mock_completion.return_value = _fake_response("ok")
    client = LLMClient(config=_cfg(ProviderType.OPENAI))
    client.generate("hi", temperature=0.1)
    assert mock_completion.call_args.kwargs["temperature"] == 0.1


# --- generate(): call_kwargs assembly (provider branching) -----------------

@patch("utils.llm_client.completion")
def test_generate_openai_omits_api_base(mock_completion):
    """OpenAI has no base_url → no api_base kwarg (provider not vllm/lmstudio)."""
    mock_completion.return_value = _fake_response("ok")
    client = LLMClient(config=_cfg(ProviderType.OPENAI, base_url="https://api.openai.com/v1"))
    client.generate("hi")
    assert "api_base" not in mock_completion.call_args.kwargs


@patch("utils.llm_client.completion")
def test_generate_vllm_adds_api_base(mock_completion):
    """vllm provider with a base_url → api_base forwarded."""
    mock_completion.return_value = _fake_response("ok")
    client = LLMClient(
        config=_cfg(ProviderType.VLLM, model="qwen3.6-35b-a3b",
                    base_url="http://localhost:8000/v1")
    )
    client.generate("hi")
    assert mock_completion.call_args.kwargs["api_base"] == "http://localhost:8000/v1"


@patch("utils.llm_client.completion")
def test_generate_lmstudio_adds_api_base(mock_completion):
    mock_completion.return_value = _fake_response("ok")
    client = LLMClient(
        config=_cfg(ProviderType.LMSTUDIO, model="local-model",
                    base_url="http://localhost:1234/v1")
    )
    client.generate("hi")
    assert mock_completion.call_args.kwargs["api_base"] == "http://localhost:1234/v1"


@patch("utils.llm_client.completion")
def test_generate_api_key_conditional(mock_completion):
    """api_key forwarded when present, omitted when None."""
    mock_completion.return_value = _fake_response("ok")
    client = LLMClient(config=_cfg(ProviderType.OPENAI, api_key="sk-test"))
    client.generate("hi")
    assert mock_completion.call_args.kwargs["api_key"] == "sk-test"

    client2 = LLMClient(config=_cfg(ProviderType.OPENAI, api_key=None))
    client2.generate("hi")
    # Second call (client2) should have no api_key.
    assert "api_key" not in mock_completion.call_args_list[-1].kwargs


@patch("utils.llm_client.completion")
def test_generate_max_tokens_conditional(mock_completion):
    mock_completion.return_value = _fake_response("ok")
    client = LLMClient(config=_cfg(ProviderType.OPENAI))

    client.generate("hi", max_tokens=128)
    assert mock_completion.call_args.kwargs["max_tokens"] == 128

    client.generate("hi")  # no max_tokens
    assert "max_tokens" not in mock_completion.call_args_list[-1].kwargs


@pytest.mark.xfail(strict=True, reason="max_tokens=0 swallowed by `if max_tokens:` guard (buggy on main); fixed in po-2025 #7394")
@patch("utils.llm_client.completion")
def test_generate_max_tokens_zero_is_forwarded(mock_completion):
    """REGRESSION PIN: max_tokens=0 is a valid int and must be forwarded.

    The legacy `if max_tokens:` guard treated 0 as falsy and silently dropped
    it (max_tokens never reached litellm). `if max_tokens is not None:` is the
    correct guard. xfail(strict=True): currently FAILS on main (xfail = green),
    will XPASS once the sibling fix lands (po-2025 PR #7394) and flip to
    strict-failure as a reminder to drop the marker. See #7394.
    """
    mock_completion.return_value = _fake_response("ok")
    client = LLMClient(config=_cfg(ProviderType.OPENAI))
    client.generate("hi", max_tokens=0)
    assert mock_completion.call_args.kwargs["max_tokens"] == 0


@patch("utils.llm_client.completion")
def test_generate_extra_kwargs_merged(mock_completion):
    """**kwargs are merged into call_kwargs and override defaults."""
    mock_completion.return_value = _fake_response("ok")
    client = LLMClient(config=_cfg(ProviderType.OPENAI))
    client.generate("hi", top_p=0.9, temperature=0.2)
    sent = mock_completion.call_args.kwargs
    assert sent["top_p"] == 0.9
    assert sent["temperature"] == 0.2  # kwargs override the default


@patch("utils.llm_client.completion")
def test_generate_model_forwarded(mock_completion):
    mock_completion.return_value = _fake_response("ok")
    client = LLMClient(config=_cfg(ProviderType.OPENAI, model="gpt-4o"))
    client.generate("hi")
    assert mock_completion.call_args.kwargs["model"] == "openai/gpt-4o"


# --- chat() ----------------------------------------------------------------

@patch("utils.llm_client.completion")
def test_chat_forwards_message_list(mock_completion):
    mock_completion.return_value = _fake_response("reply")
    client = LLMClient(config=_cfg(ProviderType.OPENAI))
    msgs = [{"role": "user", "content": "a"}, {"role": "assistant", "content": "b"}]
    out = client.chat(msgs)
    assert out == "reply"
    assert mock_completion.call_args.kwargs["messages"] == msgs


@patch("utils.llm_client.completion")
def test_chat_vllm_api_base(mock_completion):
    """chat() mirrors generate()'s provider-branching for api_base."""
    mock_completion.return_value = _fake_response("ok")
    client = LLMClient(
        config=_cfg(ProviderType.VLLM, base_url="http://localhost:8000/v1")
    )
    client.chat([{"role": "user", "content": "x"}])
    assert mock_completion.call_args.kwargs["api_base"] == "http://localhost:8000/v1"


# --- __repr__ --------------------------------------------------------------

def test_repr_format():
    client = LLMClient(config=_cfg(ProviderType.OPENAI, model="gpt-4o"))
    r = repr(client)
    assert r == "LLMClient(provider=openai, model=gpt-4o)"


def test_repr_vllm_provider():
    client = LLMClient(config=_cfg(ProviderType.VLLM, model="qwen3.6"))
    assert "provider=vllm" in repr(client)


# --- get_client() singleton ------------------------------------------------

def test_get_client_is_singleton(monkeypatch):
    """get_client() returns the same instance across calls (module-level cache)."""
    monkeypatch.setattr(llm_client, "_default_client", None)  # reset cache
    # Patch LLMClient.__init__ so the singleton does not read .env.
    with patch.object(LLMClient, "__init__", return_value=None):
        c1 = get_client()
        c2 = get_client()
    assert c1 is c2


def test_get_client_caches_in_module_global(monkeypatch):
    """First call populates _default_client; second call reuses it."""
    monkeypatch.setattr(llm_client, "_default_client", None)
    sentinel = MagicMock(spec=LLMClient)
    with patch.object(llm_client, "LLMClient", return_value=sentinel):
        assert get_client() is sentinel
        # Second call must NOT construct again.
        assert get_client() is sentinel
        assert llm_client._default_client is sentinel


# --- module-level generate() helper ----------------------------------------

@patch("utils.llm_client.completion")
def test_module_generate_delegates_to_singleton(mock_completion, monkeypatch):
    mock_completion.return_value = _fake_response("via-helper")
    monkeypatch.setattr(llm_client, "_default_client", None)
    client = LLMClient(config=_cfg(ProviderType.OPENAI))
    monkeypatch.setattr(llm_client, "_default_client", client)
    out = llm_client.generate("hi")
    assert out == "via-helper"
    assert mock_completion.call_args.kwargs["messages"] == [{"role": "user", "content": "hi"}]
