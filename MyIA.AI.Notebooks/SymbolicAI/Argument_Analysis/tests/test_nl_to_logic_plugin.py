"""Tests for argumentation_lib._nl_to_logic_plugin (See #18390).

Verifies the NLToLogicPlugin adapter: LLM translation text->PL validated
by the real parser. Uses fake LLM service + fake parse_fn (no SK, no JVM).
"""
from __future__ import annotations

import asyncio
import json
import os
import sys
from types import ModuleType, SimpleNamespace

import pytest

# Make `argumentation_lib` importable
_TESTS_DIR = os.path.dirname(os.path.abspath(__file__))
_ARG_ANALYSIS_DIR = os.path.dirname(_TESTS_DIR)
if _ARG_ANALYSIS_DIR not in sys.path:
    sys.path.insert(0, _ARG_ANALYSIS_DIR)


def _install_sk_mock():
    """Minimal SK mock for the imports the plugin needs."""
    if "semantic_kernel" in sys.modules and getattr(
        sys.modules["semantic_kernel"], "_coursia_mock", False
    ):
        return

    sk = ModuleType("semantic_kernel")
    sk._coursia_mock = True

    functions = ModuleType("semantic_kernel.functions")

    def kernel_function(*args, **kwargs):
        def decorator(func):
            return func
        if args and callable(args[0]) and not kwargs:
            return args[0]
        return decorator

    functions.kernel_function = kernel_function
    sk.functions = functions
    sk.kernel_function = kernel_function

    contents = ModuleType("semantic_kernel.contents")
    mod_hist = ModuleType("semantic_kernel.contents.chat_history")

    class ChatHistory:
        def __init__(self):
            self.messages = []
        def add_user_message(self, content):
            self.messages.append(content)

    mod_hist.ChatHistory = ChatHistory
    contents.chat_history = mod_hist
    sk.contents = contents

    for name, mod in {
        "semantic_kernel": sk,
        "semantic_kernel.functions": functions,
        "semantic_kernel.contents": contents,
        "semantic_kernel.contents.chat_history": mod_hist,
    }.items():
        sys.modules[name] = mod


_install_sk_mock()

from argumentation_lib._nl_to_logic_plugin import NLToLogicPlugin  # noqa: E402


# ---------------------------------------------------------------------------
# Fake LLM service
# ---------------------------------------------------------------------------

_TRANSLATION_RESPONSE = json.dumps({
    "propositions": ["socrates_man", "socrates_mortal"],
    "formulas": ["socrates_man", "socrates_man => socrates_mortal"],
})

_QUERIES_RESPONSE = json.dumps({
    "query_ideas": ["socrates_mortal"],
})


class FakeChatService:
    """Fake AIChatCompletion returning canned responses."""

    def __init__(self, responses):
        self._responses = list(responses)

    async def get_chat_message_contents(self, chat_history, **kwargs):
        content = self._responses.pop(0) if self._responses else "{}"
        return [SimpleNamespace(content=content)]


def _fake_parse_ok(formula):
    """Accept any formula (simulates Tweety PlParser)."""
    return formula


def _fake_parse_reject_arrow(formula):
    """Reject formulas containing '->' (simulates Tweety refusing '->')."""
    if "->" in formula:
        raise ValueError(f"General parsing error: {formula}")
    return formula


# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------


def test_translate_to_pl_happy_path():
    """Translation returns propositions + validated formulas."""
    service = FakeChatService([_TRANSLATION_RESPONSE])
    plugin = NLToLogicPlugin(llm_service=service, parse_fn=_fake_parse_ok)
    result = json.loads(asyncio.run(plugin.translate_to_pl("Socrate est un homme.")))
    assert result["propositions"] == ["socrates_man", "socrates_mortal"]
    assert "socrates_man" in result["formulas"]
    assert "socrates_man => socrates_mortal" in result["formulas"]
    assert result["rejected"] == []


def test_translate_to_pl_rejects_bad_syntax():
    """Formulas refused by the parser land in `rejected`."""
    response = json.dumps({
        "propositions": ["a", "b"],
        "formulas": ["a", "a -> b"],
    })
    service = FakeChatService([response])
    plugin = NLToLogicPlugin(llm_service=service, parse_fn=_fake_parse_reject_arrow)
    result = json.loads(asyncio.run(plugin.translate_to_pl("test")))
    assert "a" in result["formulas"]
    assert "a -> b" not in result["formulas"]
    assert len(result["rejected"]) == 1
    assert result["rejected"][0]["formula"] == "a -> b"


def test_translate_to_pl_filters_undeclared_propositions():
    """Formulas using undeclared propositions are filtered out."""
    response = json.dumps({
        "propositions": ["a"],
        "formulas": ["a", "b"],
    })
    service = FakeChatService([response])
    plugin = NLToLogicPlugin(llm_service=service, parse_fn=_fake_parse_ok)
    result = json.loads(asyncio.run(plugin.translate_to_pl("test")))
    assert "a" in result["formulas"]
    assert "b" not in result["formulas"]


def test_generate_queries():
    """Query generation returns a list of formulas."""
    service = FakeChatService([_QUERIES_RESPONSE])
    plugin = NLToLogicPlugin(llm_service=service, parse_fn=_fake_parse_ok)
    result = json.loads(asyncio.run(plugin.generate_queries(
        "Socrate est mortel.",
        '["socrates_man", "socrates_mortal"]',
        '["socrates_man", "socrates_man => socrates_mortal"]',
    )))
    assert "socrates_mortal" in result


def test_plugin_construction_requires_service_and_parser():
    """Missing collaborators are refused before an agent can use the plugin."""
    with pytest.raises(ValueError, match="llm_service"):
        NLToLogicPlugin(llm_service=None, parse_fn=_fake_parse_ok)
    with pytest.raises(TypeError, match="parse_fn"):
        NLToLogicPlugin(llm_service=FakeChatService([]), parse_fn=None)

    service = FakeChatService([_TRANSLATION_RESPONSE])
    plugin = NLToLogicPlugin(llm_service=service, parse_fn=_fake_parse_ok)
    assert plugin._llm_service is service
    assert plugin._parse_fn is _fake_parse_ok
