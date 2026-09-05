"""Google ADK runtime backed by the track's configured LLM provider.

This module is deliberately separate from :mod:`llm_client`: it constructs and
runs a real Google ADK agent, including its session, runner, events and tools.
There is no simulated response path. A missing or unreachable provider raises
``AdkRuntimeUnavailable`` with the SOTA verdict ``RECOVERABLE-LOCAL``.
"""

from __future__ import annotations

import argparse
import asyncio
from dataclasses import dataclass
from uuid import uuid4

from config.providers import (
    ProviderConfig,
    ProviderType,
    get_litellm_model,
    get_provider_config,
)
from google.adk.agents import Agent
from google.adk.models.lite_llm import LiteLlm
from google.adk.runners import Runner
from google.adk.sessions import InMemorySessionService
from google.genai import types

APP_NAME = "track2_google_adk"


class AdkRuntimeUnavailable(RuntimeError):
    """The configured real ADK/LLM runtime cannot currently be reached."""

    verdict = "RECOVERABLE-LOCAL"


@dataclass(frozen=True)
class AdkUsage:
    """Jetons consommes par un appel LLM, remontes depuis l'event ADK.

    Contrat C6 (#14058) -- tracabilite : ADK produit ``usage_metadata`` sur
    ses events LLM (natif), mais le runtime du depot ne le remontait pas.
    Chaque appel LLM d'un tour contribue un snapshot ; la consommation
    devient observable depuis ``AdkRunResult``.
    """

    prompt_tokens: int = 0
    completion_tokens: int = 0
    total_tokens: int = 0

    def __add__(self, other: "AdkUsage") -> "AdkUsage":
        return AdkUsage(
            prompt_tokens=self.prompt_tokens + other.prompt_tokens,
            completion_tokens=self.completion_tokens + other.completion_tokens,
            total_tokens=self.total_tokens + other.total_tokens,
        )


@dataclass(frozen=True)
class AdkRunResult:
    """Observable evidence produced by a complete ADK invocation."""

    response_text: str
    event_count: int
    tool_calls: tuple[str, ...]
    tool_responses: tuple[str, ...]
    usage_turns: tuple[AdkUsage, ...] = ()

    @property
    def tool_was_invoked(self) -> bool:
        """Whether ADK emitted both a tool request and its response."""
        return bool(self.tool_calls and self.tool_responses)

    @property
    def usage_total(self) -> AdkUsage:
        """Somme des jetons consommes par les appels LLM du tour."""
        total = AdkUsage()
        for usage in self.usage_turns:
            total = total + usage
        return total


def dataset_profile(rows: int, columns: int) -> dict[str, int | float]:
    """Return deterministic shape statistics for a tabular dataset."""
    if rows <= 0 or columns <= 0:
        return {
            "rows": rows,
            "columns": columns,
            "cells": 0,
            "rows_per_column": 0.0,
        }
    return {
        "rows": rows,
        "columns": columns,
        "cells": rows * columns,
        "rows_per_column": round(rows / columns, 2),
    }


def build_adk_model(config: ProviderConfig) -> LiteLlm:
    """Map a track provider configuration to ADK's public LiteLLM model."""
    kwargs: dict[str, str | bool | int] = {"drop_params": True}
    if config.base_url:
        kwargs["api_base"] = config.base_url
    if config.api_key:
        kwargs["api_key"] = config.api_key
    elif config.provider in {ProviderType.VLLM, ProviderType.LMSTUDIO}:
        # LiteLLM's OpenAI adapter requires a non-empty protocol credential,
        # even when a local OpenAI-compatible endpoint disables authentication.
        kwargs["api_key"] = "local-endpoint-no-auth"
    if config.max_tokens is not None:
        kwargs["max_tokens"] = config.max_tokens

    return LiteLlm(model=get_litellm_model(config), **kwargs)


def build_agent(
    name: str,
    description: str,
    instruction: str,
    *,
    tools: tuple = (),
    config: ProviderConfig | None = None,
) -> Agent:
    """Construct a real Google ADK agent for one pedagogical role."""
    provider = config or get_provider_config()
    return Agent(
        name=name,
        description=description,
        instruction=instruction,
        model=build_adk_model(provider),
        tools=list(tools),
    )


def build_data_agent(config: ProviderConfig | None = None) -> Agent:
    """Construct a real Google ADK agent with a deterministic Python tool."""
    return build_agent(
        name="dataset_profile_agent",
        description="Analyse la forme d'un jeu de données tabulaire.",
        instruction=(
            "Tu es un agent data science. Pour toute question contenant un "
            "nombre de lignes et de colonnes, appelle obligatoirement l'outil "
            "dataset_profile, puis explique brièvement son résultat."
        ),
        tools=(dataset_profile,),
        config=config,
    )


def _part_text(content: types.Content | None) -> str:
    if not content or not content.parts:
        return ""
    return "".join(part.text or "" for part in content.parts).strip()


def _event_usage(event) -> AdkUsage | None:
    """Snapshot C6 d'un event : son usage LLM, ou None s'il n'en porte pas.

    Un event sans appel LLM (message utilisateur, reponse d'outil) n'emet
    pas d'usage ; un provider qui ne compte pas ses jetons emet un usage
    nul -- dans les deux cas la tracabilite reste honnete (rien invente).
    """
    metadata = getattr(event, "usage_metadata", None)
    if metadata is None:
        return None
    snapshot = AdkUsage(
        prompt_tokens=metadata.prompt_token_count or 0,
        completion_tokens=metadata.candidates_token_count or 0,
        total_tokens=metadata.total_token_count or 0,
    )
    if snapshot == AdkUsage():
        return None
    return snapshot


async def run_agent_turn(
    agent: Agent,
    prompt: str,
    *,
    app_name: str = APP_NAME,
    user_id: str = "track2-user",
    session_id: str | None = None,
    timeout_seconds: float = 120.0,
) -> AdkRunResult:
    """Run one real ADK agent turn and return its observable evidence."""
    session_id = session_id or f"session-{uuid4().hex}"
    session_service = InMemorySessionService()
    runner = Runner(
        agent=agent,
        app_name=app_name,
        session_service=session_service,
    )
    await session_service.create_session(
        app_name=app_name,
        user_id=user_id,
        session_id=session_id,
    )

    message = types.Content(role="user", parts=[types.Part(text=prompt)])
    response_text = ""
    tool_calls: list[str] = []
    tool_responses: list[str] = []
    usage_turns: list[AdkUsage] = []
    event_errors: list[str] = []
    event_count = 0

    async def consume_events() -> None:
        nonlocal event_count, response_text
        async for event in runner.run_async(
            user_id=user_id,
            session_id=session_id,
            new_message=message,
        ):
            event_count += 1
            tool_calls.extend(
                call.name for call in event.get_function_calls() if call.name
            )
            tool_responses.extend(
                response.name
                for response in event.get_function_responses()
                if response.name
            )
            usage = _event_usage(event)
            if usage is not None:
                usage_turns.append(usage)
            error_code = getattr(event, "error_code", None)
            error_message = getattr(event, "error_message", None)
            if error_code or error_message:
                event_errors.append(
                    ": ".join(
                        detail
                        for detail in (error_code, error_message)
                        if detail
                    )
                )
            if event.is_final_response():
                response_text = _part_text(event.content)

    try:
        await asyncio.wait_for(consume_events(), timeout=timeout_seconds)
    except asyncio.TimeoutError as exc:
        raise AdkRuntimeUnavailable(
            f"RECOVERABLE-LOCAL: runtime ADK expire apres {timeout_seconds:g} s"
        ) from exc
    except Exception as exc:
        detail = str(exc).strip()
        suffix = f": {detail}" if detail else ""
        raise AdkRuntimeUnavailable(
            f"RECOVERABLE-LOCAL: echec du runtime ADK reel "
            f"({type(exc).__name__}){suffix}"
        ) from exc
    finally:
        await runner.close()

    if not response_text:
        detail = f" ({'; '.join(event_errors)})" if event_errors else ""
        raise AdkRuntimeUnavailable(
            "RECOVERABLE-LOCAL: ADK n'a produit aucune reponse LLM finale" + detail
        )

    return AdkRunResult(
        response_text=response_text,
        event_count=event_count,
        tool_calls=tuple(tool_calls),
        tool_responses=tuple(tool_responses),
        usage_turns=tuple(usage_turns),
    )


async def run_data_agent(
    prompt: str,
    config: ProviderConfig | None = None,
    *,
    app_name: str = APP_NAME,
    user_id: str = "track2-user",
    session_id: str | None = None,
    timeout_seconds: float = 120.0,
) -> AdkRunResult:
    """Run the track's dataset agent through the generic ADK turn."""
    return await run_agent_turn(
        build_data_agent(config),
        prompt,
        app_name=app_name,
        user_id=user_id,
        session_id=session_id,
        timeout_seconds=timeout_seconds,
    )


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Smoke test Google ADK + LLM reel")
    parser.add_argument(
        "--prompt",
        default=(
            "Un dataset contient 120 lignes et 8 colonnes. "
            "Appelle dataset_profile et interprète le résultat."
        ),
    )
    return parser.parse_args()


async def _smoke() -> int:
    args = _parse_args()
    try:
        result = await run_data_agent(args.prompt)
    except (AdkRuntimeUnavailable, ValueError) as exc:
        detail = str(exc)
        if not detail.startswith("RECOVERABLE-LOCAL"):
            detail = f"RECOVERABLE-LOCAL: {detail}"
        print(detail)
        return 2

    print(f"ADK events: {result.event_count}")
    print(f"ADK tool calls: {', '.join(result.tool_calls) or 'aucun'}")
    print(f"ADK tool responses: {', '.join(result.tool_responses) or 'aucune'}")
    print(f"LLM response: {result.response_text}")
    if not result.tool_was_invoked:
        print("RECOVERABLE-LOCAL: le LLM n'a pas invoqué l'outil ADK")
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(asyncio.run(_smoke()))
