"""Unit tests for provider response parsing in lean_runner.py."""

import sys
from pathlib import Path
from types import SimpleNamespace

import pytest

LEAN_DIR = Path(__file__).resolve().parents[2]
if str(LEAN_DIR) not in sys.path:
    sys.path.insert(0, str(LEAN_DIR))

from lean_runner import LLMClient  # noqa: E402


class FakeMessages:
    def __init__(self, response):
        self.response = response

    def create(self, **_kwargs):
        return self.response


def make_client(content):
    client = LLMClient.__new__(LLMClient)
    client.model = "claude-sonnet-4-5"
    response = SimpleNamespace(
        content=content,
        model=client.model,
        usage=SimpleNamespace(input_tokens=12, output_tokens=7),
    )
    client.client = SimpleNamespace(messages=FakeMessages(response))
    return client


def test_anthropic_joins_text_blocks_after_thinking_block():
    client = make_client([
        SimpleNamespace(type="thinking", thinking="Analyse interne"),
        SimpleNamespace(type="text", text="```lean\nby simp\n```"),
        SimpleNamespace(type="text", text="Vérification terminée."),
    ])

    result = client._generate_anthropic("prompt", "system", 0.3)

    assert result["content"] == "```lean\nby simp\n```\nVérification terminée."
    assert result["tokens"] == {"prompt": 12, "completion": 7, "total": 19}


def test_anthropic_rejects_response_without_text_block():
    client = make_client([
        SimpleNamespace(type="thinking", thinking="Analyse interne"),
    ])

    with pytest.raises(RuntimeError, match="aucun bloc texte"):
        client._generate_anthropic("prompt", "system", 0.3)
