"""Tests for the real Google ADK runtime foundation."""

import sys
from pathlib import Path
from typing import ClassVar
from unittest.mock import AsyncMock, MagicMock, patch

import pytest

_PKG = Path(__file__).resolve().parent.parent
if str(_PKG) not in sys.path:
    sys.path.insert(0, str(_PKG))

from config.providers import ProviderConfig, ProviderType

from utils import adk_runtime
from utils.adk_runtime import (
    AdkRuntimeUnavailable,
    build_adk_model,
    dataset_profile,
)


def _config(
    provider=ProviderType.VLLM,
    *,
    model="qwen3.6-35b-a3b",
    base_url="https://llm.example.test/v1",
    api_key=None,
):
    return ProviderConfig(
        provider=provider,
        model=model,
        base_url=base_url,
        api_key=api_key,
    )


def test_dataset_profile_computes_deterministic_statistics():
    assert dataset_profile(120, 8) == {
        "rows": 120,
        "columns": 8,
        "cells": 960,
        "rows_per_column": 15.0,
    }


def test_dataset_profile_rejects_nonpositive_shape_without_exception():
    assert dataset_profile(0, 8)["cells"] == 0
    assert dataset_profile(120, -1)["rows_per_column"] == 0.0


def test_build_adk_model_maps_vllm_to_openai_compatible_litellm():
    model = build_adk_model(_config())
    assert model.model == "openai/qwen3.6-35b-a3b"
    assert model._additional_args["api_base"] == "https://llm.example.test/v1"
    assert model._additional_args["api_key"] == "local-endpoint-no-auth"
    assert model._additional_args["drop_params"] is True


def test_build_adk_model_forwards_real_key_without_logging_it():
    model = build_adk_model(_config(api_key="configured-test-key"))
    assert model._additional_args["api_key"] == "configured-test-key"


def test_build_adk_model_forwards_qwen_generation_budget():
    model = build_adk_model(
        _config(
            ProviderType.QWEN,
            model="qwen3.6-flash",
            api_key="configured-test-key",
        ).model_copy(update={"max_tokens": 512})
    )
    assert model.model == "openai/qwen3.6-flash"
    assert model._additional_args["max_tokens"] == 512


def test_build_adk_model_openai_uses_provider_mapping():
    model = build_adk_model(
        _config(
            ProviderType.OPENAI,
            model="gpt-4o-mini",
            base_url="https://api.openai.com/v1",
            api_key="configured-test-key",
        )
    )
    assert model.model == "openai/gpt-4o-mini"


def test_build_data_agent_uses_public_adk_agent_and_real_tool():
    agent = adk_runtime.build_data_agent(_config())
    assert agent.name == "dataset_profile_agent"
    assert isinstance(agent.model, adk_runtime.LiteLlm)
    assert len(agent.tools) == 1
    assert agent.tools[0] is dataset_profile


def test_build_agent_supports_distinct_pedagogical_roles():
    agent = adk_runtime.build_agent(
        name="planner_agent",
        description="Planifie une analyse.",
        instruction="Produis un plan court.",
        tools=(dataset_profile,),
        config=_config(),
    )
    assert agent.name == "planner_agent"
    assert agent.description == "Planifie une analyse."
    assert agent.instruction == "Produis un plan court."
    assert agent.tools[0] is dataset_profile


class _Event:
    def __init__(self, *, final=False, content=None, calls=(), responses=()):
        self._final = final
        self.content = content
        self._calls = calls
        self._responses = responses

    def is_final_response(self):
        return self._final

    def get_function_calls(self):
        return self._calls

    def get_function_responses(self):
        return self._responses


class _Runner:
    instances: ClassVar[list["_Runner"]] = []

    def __init__(self, **kwargs):
        self.kwargs = kwargs
        self.close = AsyncMock()
        self.instances.append(self)

    async def run_async(self, **kwargs):
        self.run_kwargs = kwargs
        call = MagicMock(name="call")
        call.name = "dataset_profile"
        response = MagicMock(name="response")
        response.name = "dataset_profile"
        yield _Event(calls=(call,))
        yield _Event(responses=(response,))
        yield _Event(
            final=True,
            content=adk_runtime.types.Content(
                role="model", parts=[adk_runtime.types.Part(text="960 cellules")]
            ),
        )


def test_run_data_agent_creates_session_and_collects_adk_evidence():
    async def exercise():
        service = MagicMock()
        service.create_session = AsyncMock()
        _Runner.instances.clear()
        with (
            patch.object(adk_runtime, "InMemorySessionService", return_value=service),
            patch.object(adk_runtime, "Runner", _Runner),
            patch.object(adk_runtime, "build_data_agent", return_value=MagicMock()),
        ):
            result = await adk_runtime.run_data_agent(
                "120 lignes, 8 colonnes", _config(), session_id="session-test"
            )

        service.create_session.assert_awaited_once_with(
            app_name=adk_runtime.APP_NAME,
            user_id="track2-user",
            session_id="session-test",
        )
        runner = _Runner.instances[0]
        assert runner.run_kwargs["session_id"] == "session-test"
        assert result.response_text == "960 cellules"
        assert result.event_count == 3
        assert result.tool_calls == ("dataset_profile",)
        assert result.tool_responses == ("dataset_profile",)
        assert result.tool_was_invoked
        runner.close.assert_awaited_once()

    adk_runtime.asyncio.run(exercise())


def test_run_agent_turn_uses_the_supplied_adk_agent():
    async def exercise():
        service = MagicMock()
        service.create_session = AsyncMock()
        agent = MagicMock(name="planner_agent")
        _Runner.instances.clear()
        with (
            patch.object(adk_runtime, "InMemorySessionService", return_value=service),
            patch.object(adk_runtime, "Runner", _Runner),
        ):
            result = await adk_runtime.run_agent_turn(
                agent,
                "Planifie cette analyse",
                session_id="planner-session",
            )

        runner = _Runner.instances[0]
        assert runner.kwargs["agent"] is agent
        assert runner.run_kwargs["session_id"] == "planner-session"
        assert result.response_text == "960 cellules"
        runner.close.assert_awaited_once()

    adk_runtime.asyncio.run(exercise())


class _FailingRunner(_Runner):
    async def run_async(self, **kwargs):
        if False:
            yield None
        raise ConnectionError("provider unavailable")


class _ErrorEventRunner(_Runner):
    async def run_async(self, **kwargs):
        event = _Event()
        event.error_code = "MAX_TOKENS"
        event.error_message = "generation limit reached"
        yield event


class _HangingRunner(_Runner):
    async def run_async(self, **kwargs):
        await adk_runtime.asyncio.sleep(1)
        if False:
            yield None


def test_run_data_agent_fails_loudly_without_simulated_fallback():
    async def exercise():
        service = MagicMock()
        service.create_session = AsyncMock()
        _FailingRunner.instances.clear()
        with (
            patch.object(adk_runtime, "InMemorySessionService", return_value=service),
            patch.object(adk_runtime, "Runner", _FailingRunner),
            patch.object(adk_runtime, "build_data_agent", return_value=MagicMock()),
            pytest.raises(AdkRuntimeUnavailable, match="RECOVERABLE-LOCAL"),
        ):
            await adk_runtime.run_data_agent("prompt", _config())

        _FailingRunner.instances[0].close.assert_awaited_once()

    adk_runtime.asyncio.run(exercise())


def test_run_data_agent_reports_adk_event_error():
    async def exercise():
        service = MagicMock()
        service.create_session = AsyncMock()
        with (
            patch.object(adk_runtime, "InMemorySessionService", return_value=service),
            patch.object(adk_runtime, "Runner", _ErrorEventRunner),
            patch.object(adk_runtime, "build_data_agent", return_value=MagicMock()),
            pytest.raises(
                AdkRuntimeUnavailable,
                match="MAX_TOKENS: generation limit reached",
            ),
        ):
            await adk_runtime.run_data_agent("prompt", _config())

    adk_runtime.asyncio.run(exercise())


def test_run_data_agent_times_out_and_closes_runner():
    async def exercise():
        service = MagicMock()
        service.create_session = AsyncMock()
        _HangingRunner.instances.clear()
        with (
            patch.object(adk_runtime, "InMemorySessionService", return_value=service),
            patch.object(adk_runtime, "Runner", _HangingRunner),
            patch.object(adk_runtime, "build_data_agent", return_value=MagicMock()),
            pytest.raises(AdkRuntimeUnavailable, match="expire apres 0.01 s"),
        ):
            await adk_runtime.run_data_agent(
                "prompt", _config(), timeout_seconds=0.01
            )

        _HangingRunner.instances[0].close.assert_awaited_once()

    adk_runtime.asyncio.run(exercise())


def test_smoke_reports_missing_qwen_config_without_traceback(capsys):
    async def exercise():
        with (
            patch.object(
                adk_runtime,
                "_parse_args",
                return_value=MagicMock(prompt="prompt"),
            ),
            patch.object(
                adk_runtime,
                "run_data_agent",
                side_effect=ValueError(
                    "Configuration Qwen cloud incomplete : QWEN_API_KEY"
                ),
            ),
        ):
            assert await adk_runtime._smoke() == 2

    adk_runtime.asyncio.run(exercise())
    assert capsys.readouterr().out.startswith("RECOVERABLE-LOCAL:")


def test_runtime_unavailable_exposes_sota_verdict():
    assert AdkRuntimeUnavailable.verdict == "RECOVERABLE-LOCAL"
