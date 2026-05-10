"""Agent factory functions for the 4 specialized proof agents.

Each agent gets its own tools subset and model configuration.
"""

from agent_framework import Agent, ChatOptions

from .config import create_client
from .instructions import (
    SEARCH_AGENT_INSTRUCTIONS,
    TACTIC_AGENT_INSTRUCTIONS,
    CRITIC_AGENT_INSTRUCTIONS,
    COORDINATOR_AGENT_INSTRUCTIONS,
)
from .tools import SearchTools, TacticTools, CriticTools, CoordinatorTools

# Generous max_tokens budget: thinking models (z.ai GLM-5.1, Qwen3.6) burn
# 90-99% of their output budget in `reasoning_content` before producing a
# visible response. With max_tokens=2048 z.ai routinely returns
# `finish_reason: "length"` on trivial smoke tests. 16384 leaves room for the
# model to actually finish reasoning AND emit a tactic.
REASONING_MAX_TOKENS = 16384
FAST_MAX_TOKENS = 8192


def _reasoning_options() -> ChatOptions:
    return ChatOptions(max_tokens=REASONING_MAX_TOKENS)


def _fast_options() -> ChatOptions:
    return ChatOptions(max_tokens=FAST_MAX_TOKENS)


def create_search_agent(tools: SearchTools, provider: str = "local") -> Agent:
    """SearchAgent: finds Mathlib lemmas. Uses fast local model."""
    client = create_client(provider, model_key="fast")
    return Agent(
        client=client,
        instructions=SEARCH_AGENT_INSTRUCTIONS,
        tools=[
            tools.search_mathlib_lemmas,
            tools.lookup_proven_pattern,
            tools.get_proof_state,
            tools.add_discovered_lemma,
            tools.file_read_lines,
        ],
        name="SearchAgent",
        default_options=_fast_options(),
    )


def create_tactic_agent(tools: TacticTools, provider: str = "zai") -> Agent:
    """TacticAgent: generates tactics + decomposition. Uses reasoning model."""
    client = create_client(provider, model_key="reasoning")
    return Agent(
        client=client,
        instructions=TACTIC_AGENT_INSTRUCTIONS,
        tools=[
            tools.generate_tactics,
            tools.submit_tactic,
            tools.submit_decomposition,
            tools.file_read_lines,
            tools.file_find_sorry_lines,
            tools.file_replace_lines,
            tools.file_replace_sorry,
            tools.compile_probe_goal,
            tools.compile,
            tools.verify_sorry_replacement,
        ],
        name="TacticAgent",
        default_options=_reasoning_options(),
    )


def create_critic_agent(tools: CriticTools, provider: str = "zai") -> Agent:
    """CriticAgent: analyzes failures, decides routing. Uses fast model."""
    client = create_client(provider, model_key="fast")
    return Agent(
        client=client,
        instructions=CRITIC_AGENT_INSTRUCTIONS,
        tools=[
            tools.analyze_failure,
            tools.get_proof_state,
            tools.designate_next_agent,
        ],
        name="CriticAgent",
        default_options=_fast_options(),
    )


def create_coordinator_agent(tools: CoordinatorTools, provider: str = "zai") -> Agent:
    """CoordinatorAgent: strategic escalation. Uses reasoning model."""
    client = create_client(provider, model_key="reasoning")
    return Agent(
        client=client,
        instructions=COORDINATOR_AGENT_INSTRUCTIONS,
        tools=[
            tools.get_proof_state,
            tools.set_attack_plan,
            tools.advance_plan,
            tools.file_read_lines,
            tools.search_mathlib_lemmas,
        ],
        name="CoordinatorAgent",
        default_options=_reasoning_options(),
    )
