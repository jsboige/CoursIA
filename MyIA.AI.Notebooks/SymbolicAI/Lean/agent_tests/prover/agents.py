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
    DIAGNOSIS_AGENT_INSTRUCTIONS,
    augment_instructions,
)
from .tools import SearchTools, TacticTools, CriticTools, CoordinatorTools, DiagnosisTools

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


def _stamp_provider(agent: Agent, provider: str) -> Agent:
    """Tag an Agent with its provider for the workflow-layer timeout policy (#7477 P1b).

    ``_is_transient_error`` (workflow.py) reads ``getattr(agent,
    "_prover_provider", None)`` so that a timeout from a hang-prone provider
    (local vLLM / qwen3.6 — whose failure mode is a GPU-stall hang, not a
    transient 5xx/reset) is treated as a *definitive* provider failure
    instead of being retried at the workflow layer. Each retry would
    re-burn ``request_timeout_s`` (config.py P1: ~480s per hung local call
    after max_retries=1), so the pre-P1b workflow multiplied that burn
    ``TRANSIENT_RETRY_MAX`` (5) times. Stamping the provider here lets the
    outage-breaker terminate the run cleanly instead. Forensic #7477:
    ``[ERROR] chat qwen3.6 1206.9s`` (5x240s pre-P1a on one logical call).
    """
    agent._prover_provider = provider  # type: ignore[attr-defined]
    return agent


def create_search_agent(tools: SearchTools, provider: str = "zai",
                        goal: str = "", name: str = "SearchAgent") -> Agent:
    """SearchAgent: finds Mathlib lemmas. Uses fast z.ai (GLM-5.2 workhorse).

    #7477 P6: historical default was ``provider="local"`` (Qwen3.6) which
    has documented ``finish_reason: length`` empties on Search workloads
    (2026-05-11 BG iter 2 trace L849). The #1289 follow-up intended the
    GLM-5.2 workhorse (``zai``) for fast-class agents (Search/Critic/
    Diagnosis) but the default here was never updated. P6 fuller fix
    routes Search to ``zai`` so the workhorse upgrade is exercised where
    search *is* needed."""
    client = create_client(provider, model_key="fast")
    # Forensic #1453 (2026-07-02, traces L849/L180): when the lean-explore
    # client is not installed, search_leanexplore is a 0.0s no-op — yet the
    # agent invoked it 11x/5x per run (span noise + one LLM decision each).
    # Probe availability once (cached module-global) and only register the
    # tool when it can actually answer.
    from .tools import _get_leanexplore_client
    _, _le_available = _get_leanexplore_client()
    agent_tools = [
        tools.search_mathlib_lemmas,
        *([tools.search_leanexplore] if _le_available else []),
        tools.lookup_proven_pattern,
        tools.get_proof_state,
        tools.add_discovered_lemma,
        tools.file_read_lines,
        tools.file_load,
    ]
    return _stamp_provider(Agent(
        client=client,
        instructions=augment_instructions(SEARCH_AGENT_INSTRUCTIONS, goal=goal),
        tools=agent_tools,
        name=name,
        default_options=_fast_options(),
    ), provider)


def create_tactic_agent(tools: TacticTools, provider: str = "openrouter",
                        goal: str = "") -> Agent:
    """TacticAgent: generates tactics + decomposition. Uses reasoning model."""
    client = create_client(provider, model_key="reasoning")
    return _stamp_provider(Agent(
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
            tools.file_insert_lines,
            tools.compile_probe_goal,
            tools.compile,
            tools.verify_sorry_replacement,
        ],
        name="TacticAgent",
        default_options=_reasoning_options(),
    ), provider)


def create_critic_agent(tools: CriticTools, provider: str = "zai") -> Agent:
    """CriticAgent: analyzes failures, decides routing. Uses fast z.ai workhorse.

    #7477 P6: historical default was ``provider="openrouter"`` (Anthropic
    Haiku 4.5 fast) which is overkill for a routing-decision agent and
    burns Anthropic budget at scale. The #1289 follow-up intended the
    GLM-5.2 workhorse (``zai``) for fast-class agents. P6 fuller fix
    routes Critic to ``zai`` — keeps cost bounded while the model is
    fast enough for routing decisions."""
    client = create_client(provider, model_key="fast")
    return _stamp_provider(Agent(
        client=client,
        instructions=CRITIC_AGENT_INSTRUCTIONS,
        tools=[
            tools.analyze_failure,
            tools.get_proof_state,
            tools.designate_next_agent,
        ],
        name="CriticAgent",
        default_options=_fast_options(),
    ), provider)


def create_coordinator_agent(tools: CoordinatorTools, provider: str = "openrouter") -> Agent:
    """CoordinatorAgent: strategic escalation. Uses reasoning model."""
    client = create_client(provider, model_key="reasoning")
    return _stamp_provider(Agent(
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
            # B3 (issue #1225): constructive existential heuristic. Tries
            # exact ⟨constructor, validator⟩ on existential goals before
            # escalating to Director or marking intractable.
            tools.try_constructive_existential,
            # F9 (2026-05-17): Director consultation gate. The Coordinator
            # MUST call request_director_guidance before mark_sorry_intractable
            # (gated server-side in tools.py). C37 forensic confirmed without
            # this tool the Coordinator had no functional path to the Director.
            tools.request_director_guidance,
            tools.mark_sorry_intractable,
        ],
        name="CoordinatorAgent",
        default_options=_reasoning_options(),
    ), provider)


# 512 was too tight: a frontier reasoning model (Opus 4.7 / GPT-5.5) needs
# room to emit an APPROACH + a concrete TACTICS block, and on extended-thinking
# routes part of the budget is spent before the visible answer. 2048 lets the
# Director actually deliver actionable guidance; it is still called at most 3x
# per session so the cost stays bounded.
DIRECTOR_MAX_TOKENS = 2048


def create_director_agent(provider: str = "openrouter",
                          target_file: str = "") -> Agent:
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
    return _stamp_provider(Agent(
        client=client,
        # #1081: the whole point of the frontier Director is grounded guidance
        # — inject the committed reference docs (mmaaz-git proofs, ported defs,
        # project tactic patterns) into its instructions.
        instructions=augment_instructions(
            DIRECTOR_AGENT_INSTRUCTIONS, include_references=True,
            target_file=target_file),
        tools=[],
        name="DirectorAgent",
        default_options=ChatOptions(max_tokens=DIRECTOR_MAX_TOKENS),
    ), provider)


def create_diagnosis_agent(tools: DiagnosisTools, provider: str = "zai") -> Agent:
    """DiagnosisAgent: qualitative verification. Uses fast z.ai workhorse.

    #7477 P6: historical default was ``provider="local"`` (Qwen3.6).
    Same root cause as SearchAgent — diagnosis is fast-class
    verification work that benefits from the #1289 workhorse upgrade."""
    client = create_client(provider, model_key="fast")
    return _stamp_provider(Agent(
        client=client,
        instructions=DIAGNOSIS_AGENT_INSTRUCTIONS,
        tools=[
            tools.get_resource_status,
            tools.read_build_result,
            tools.count_sorries,
            tools.diff_current_vs_original,
            tools.read_build_errors,
            tools.assess_structural_progress,
            tools.adjust_decomposition_budget,
        ],
        name="DiagnosisAgent",
        default_options=_fast_options(),
    ), provider)
