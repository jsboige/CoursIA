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
    DIRECTOR_AGENT_INSTRUCTIONS,
    augment_instructions,
)
from .tools import SearchTools, TacticTools, CriticTools, CoordinatorTools

# Generous max_tokens budget: thinking models (z.ai GLM-5.1, Qwen3.6) burn
# 90-99% of their output budget in `reasoning_content` before producing a
# visible response. With max_tokens=2048 z.ai routinely returns
# `finish_reason: "length"` on trivial smoke tests. 16384 leaves room for the
# model to actually finish reasoning AND emit a tactic.
#
# 2026-05-11 BG iter 2 trace showed SearchAgent (local Qwen3.6) at
# 8192 budget hit `finish_reason: length` with `parts: []` (empty response).
# Burned 100% of output in reasoning_content. Bumped fast = same as reasoning
# so local thinking models have headroom on Search work too.
REASONING_MAX_TOKENS = 16384
FAST_MAX_TOKENS = 16384


def _reasoning_options() -> ChatOptions:
    return ChatOptions(max_tokens=REASONING_MAX_TOKENS)


def _fast_options() -> ChatOptions:
    return ChatOptions(max_tokens=FAST_MAX_TOKENS)


def create_search_agent(tools: SearchTools, provider: str = "local",
                        goal: str = "") -> Agent:
    """SearchAgent: finds Mathlib lemmas. Uses fast local model."""
    client = create_client(provider, model_key="fast")
    return Agent(
        client=client,
        instructions=augment_instructions(SEARCH_AGENT_INSTRUCTIONS, goal=goal),
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


def create_tactic_agent(tools: TacticTools, provider: str = "zai",
                        goal: str = "") -> Agent:
    """TacticAgent: generates tactics + decomposition. Uses reasoning model."""
    client = create_client(provider, model_key="reasoning")
    return Agent(
        client=client,
        instructions=augment_instructions(TACTIC_AGENT_INSTRUCTIONS, goal=goal),
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
        # #1081: the Coordinator sets the attack plan — ground it in the
        # committed reference docs (mmaaz-git strategies, ported defs).
        instructions=augment_instructions(
            COORDINATOR_AGENT_INSTRUCTIONS, include_references=True),
        tools=[
            tools.get_proof_state,
            tools.set_attack_plan,
            tools.advance_plan,
            tools.file_read_lines,
            tools.search_mathlib_lemmas,
            tools.mark_sorry_intractable,
        ],
        name="CoordinatorAgent",
        default_options=_reasoning_options(),
    )


# 512 was too tight: a frontier reasoning model (Opus 4.7 / GPT-5.5) needs
# room to emit an APPROACH + a concrete TACTICS block, and on extended-thinking
# routes part of the budget is spent before the visible answer. 2048 lets the
# Director actually deliver actionable guidance; it is still called at most 3x
# per session so the cost stays bounded.
DIRECTOR_MAX_TOKENS = 2048


def create_director_agent(provider: str = "openrouter") -> Agent:
    """DirectorAgent: external frontier LLM providing strategic guidance.

    Runs on the strongest model available via OpenRouter (Opus 4.7 /
    GPT-5.5 high / DeepSeek v4 Pro — see prover/config.py + .env
    OPENROUTER_CHAT_MODEL_ID). Steers the local z.ai/Qwen agents when they
    stall: no tools, pure text output with a structured APPROACH + TACTICS
    block grounded in the reference material embedded in the shared state
    (mmaaz-git stable-marriage proofs, project definitions, lessons learned).

    Budget: max 2048 tokens, max 3 calls per session.
    """
    client = create_client(provider, model_key="reasoning")
    return Agent(
        client=client,
        # #1081: the whole point of the frontier Director is grounded guidance
        # — inject the committed reference docs (mmaaz-git proofs, ported defs,
        # project tactic patterns) into its instructions.
        instructions=augment_instructions(
            DIRECTOR_AGENT_INSTRUCTIONS, include_references=True),
        tools=[],
        name="DirectorAgent",
        default_options=ChatOptions(max_tokens=DIRECTOR_MAX_TOKENS),
    )
