"""Unit tests for P6 per-agent routing map (#7477 P6 fuller fix).

Background (P6, 2026-07-19, #7477): the GLM-5.2 workhorse upgrade
intended by #1289 for fast-class agents (Search, Critic, Diagnosis) was
never wired through to the default ``provider=`` arguments of
``create_search_agent`` (defaults to ``"local"`` Qwen3.6, which is
hang-prone on Search workloads — see 2026-05-11 BG iter 2 trace L849) or
``create_critic_agent`` (defaults to ``"openrouter"`` Claude Haiku 4.5
fast, which is overkill for routing-decision work).

Fix (#7477 P6): extract ``_expected_provider(agent_name) -> str`` in
``prover/p6_routing.py`` (stdlib-only) that pins the *intent* — ``zai``
for the workhorse-class agents. ``MultiAgentSorryProver.__init__`` reads
this map to override the historical defaults; reasoning-class agents
(Tactic/Coordinator/Director) are explicitly NOT touched because their
#1289 routing is owner-locked and out of the P6 mandate.

These tests load ``prover/p6_routing.py`` by file path (bypassing
``prover/__init__.py`` and the LLM stack) and assert:

  1. Workhorse-class agents (Search/Critic/Diagnosis) default to ``zai``.
  2. Reasoning-class agents (Tactic/Coordinator/Director) are explicitly
     NOT in the map — their #1289 routing is owner-locked, P6 does not
     re-route them.
  3. The map is non-empty and identifies exactly the 3 workhorse agents.
  4. ``_validate_provider_override`` honors caller overrides and falls
     back to a sane default for unmapped agents.

Pattern mirrors ``tests/test_p4_l1_false_negative.py`` (#7477 P4, #7533
MERGEABLE) and ``tests/test_bg_tree_lock.py``: file-path load via
``importlib.util.spec_from_file_location`` to bypass ``prover/__init__.py``
which eagerly imports ``agent_framework``.
"""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT))


# Load p6_routing.py DIRECTLY by file path (bypasses prover/__init__.py
# which eagerly imports agent_framework / agent_framework_openai absent
# on a bare CI runner). Mirrors test_p4_l1_false_negative.py pattern.
_spec = importlib.util.spec_from_file_location(
    "prover_p6_routing", ROOT / "prover" / "p6_routing.py"
)
_p6_routing = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_p6_routing)
_expected_provider = _p6_routing._expected_provider
_iter_expected_agents = _p6_routing._iter_expected_agents
_validate_provider_override = _p6_routing._validate_provider_override


# --- workhorse-class agents must route to zai (P6 fuller fix) ---------


def test_search_agent_routes_to_zai():
    """SearchAgent default = ``zai`` (GLM-5.2 workhorse). P6 fuller fix.

    Historical: ``create_search_agent(provider="local")`` defaulted to
    Qwen3.6 which has documented ``finish_reason: length`` empties on
    Search workloads (BG iter 2 trace 2026-05-11, L849). Routing to
    ``zai`` exercises the workhorse upgrade that #1289 intended for
    fast-class agents."""
    assert _expected_provider("SearchAgent") == "zai", (
        "P6: SearchAgent default must route to zai (GLM-5.2 workhorse) "
        "so the #1289 upgrade is actually exercised where search is "
        "needed. Historical default of 'local' caused length-empty "
        "responses on Search workloads."
    )


def test_critic_agent_routes_to_zai():
    """CriticAgent default = ``zai`` (GLM-5.2 workhorse). P6 fuller fix.

    Historical: ``create_critic_agent(provider="openrouter")`` routed
    failure-analysis routing-decision work to Claude Haiku 4.5 fast
    (Anthropic) — overkill for the work, expensive at scale. Routing to
    ``zai`` keeps cost bounded while the model is fast enough for
    routing decisions."""
    assert _expected_provider("CriticAgent") == "zai", (
        "P6: CriticAgent default must route to zai (GLM-5.2 workhorse) "
        "instead of openrouter (Anthropic Haiku 4.5 fast) — overkill "
        "for routing-decision work."
    )


def test_diagnosis_agent_routes_to_zai():
    """DiagnosisAgent default = ``zai`` (GLM-5.2 workhorse). P6 fuller fix.

    Historical: ``create_diagnosis_agent(provider="local")`` defaulted to
    Qwen3.6. Same root cause as SearchAgent — the diagnosis workload is
    fast-class (qualitative verification of build state) and benefits
    from the workhorse upgrade."""
    assert _expected_provider("DiagnosisAgent") == "zai", (
        "P6: DiagnosisAgent default must route to zai (GLM-5.2 "
        "workhorse) — same root cause as SearchAgent. Diagnosis is "
        "fast-class verification work."
    )


# --- reasoning-class agents are EXPLICITLY out of scope (anti-regression)


def test_tactic_agent_not_in_map():
    """TacticAgent must NOT appear in the P6 map — its routing is owner-
    locked by #1289 (GLM-5.1 z.ai times out at 1680s on complex Lean
    tactic generation, so it stays on ``openrouter``/GPT-5.5). P6 is
    workhorse-class only; touching TacticAgent would re-litigate #1289
    out of mandate scope."""
    assert _expected_provider("TacticAgent") is None, (
        "P6 must NOT touch TacticAgent routing — #1289 already routed it "
        "away from zai for valid 1680s timeout reasons. Owner-locked."
    )


def test_coordinator_agent_not_in_map():
    """CoordinatorAgent must NOT appear in the P6 map — its routing is
    owner-locked by #1289 (GLM-5.1 z.ai times out on complex Lean
    contexts). Same rationale as TacticAgent."""
    assert _expected_provider("CoordinatorAgent") is None, (
        "P6 must NOT touch CoordinatorAgent routing — #1289 already "
        "routed it away from zai for valid 12+ min timeout reasons. "
        "Owner-locked."
    )


def test_director_agent_not_in_map():
    """DirectorAgent must NOT appear in the P6 map — Director is a
    reasoning-class external-frontier-LLM agent that intentionally
    routes through OpenRouter for Opus 4.7 / GPT-5.5 high (the whole
    point of the Director is to use the strongest model available,
    see #1081). P6 is workhorse-class only."""
    assert _expected_provider("DirectorAgent") is None, (
        "P6 must NOT touch DirectorAgent routing — Director is "
        "intentionally routed to the strongest frontier model via "
        "OpenRouter (#1081). P6 is workhorse-class only."
    )


# --- map structural invariants ----------------------------------------


def test_map_is_non_empty_and_well_formed():
    """The map must identify at least one workhorse agent, and every
    entry must have a non-empty provider string. Empty map = P6 was not
    actually applied."""
    pairs = _iter_expected_agents()
    assert len(pairs) >= 1, (
        "P6 map must contain at least one workhorse-class agent — "
        "empty map = the fix was not actually applied."
    )
    for agent_name, provider in pairs:
        assert isinstance(agent_name, str) and agent_name, (
            f"P6 map entry has empty agent name: {pairs}"
        )
        assert isinstance(provider, str) and provider, (
            f"P6 map entry for {agent_name!r} has empty provider: {pairs}"
        )


def test_map_covers_exactly_three_workhorse_agents():
    """P6 mandate = the THREE workhorse-class agents (Search, Critic,
    Diagnosis). If a future change adds a fourth, this guard surfaces
    the scope expansion explicitly."""
    pairs = _iter_expected_agents()
    assert len(pairs) == 3, (
        f"P6 map must cover exactly 3 workhorse-class agents "
        f"(Search/Critic/Diagnosis). Got {len(pairs)}: {pairs}. "
        f"If you intentionally expanded scope, update this test AND "
        f"the P6 forensic #7477 spec — reasoning-class agents are "
        f"owner-locked by #1289."
    )


def test_all_map_providers_use_zai():
    """Every P6 map entry routes to ``zai`` — that's the whole point of
    the fix (exercise the workhorse upgrade on workhorse-class agents).
    A future change routing to a different provider is a scope expansion
    that must update the P6 spec."""
    pairs = _iter_expected_agents()
    for agent_name, provider in pairs:
        assert provider == "zai", (
            f"P6 map entry for {agent_name!r} routes to {provider!r}, "
            f"not 'zai'. The P6 mandate is to exercise the #1289 "
            f"workhorse upgrade (GLM-5.2 / zai) on workhorse-class "
            f"agents. A different provider = scope expansion, update "
            f"the spec."
        )


# --- _validate_provider_override behavior -----------------------------


def test_validate_override_honors_caller_override():
    """If a caller explicitly passes a provider (e.g. a test pins
    'local' to reproduce a hang), the override wins. P6's intent is
    only the *default* — explicit overrides are caller authority."""
    assert _validate_provider_override("SearchAgent", "local") == "local"
    assert _validate_provider_override("SearchAgent", "openrouter") == "openrouter"
    assert _validate_provider_override("CriticAgent", "openrouter") == "openrouter"


def test_validate_override_falls_back_to_map_for_known_agents():
    """For a known workhorse agent with no override, fall back to the
    P6 map (= ``zai``). This is the default path."""
    assert _validate_provider_override("SearchAgent", None) == "zai"
    assert _validate_provider_override("CriticAgent", None) == "zai"
    assert _validate_provider_override("DiagnosisAgent", None) == "zai"


def test_validate_override_falls_back_to_openrouter_for_unknown_agent():
    """For an unknown agent (e.g. a future agent type that hasn't been
    mapped), fall back to ``openrouter`` — the historical
    ``MultiAgentSorryProver`` default for reasoning-class work. This
    keeps P6 behavior additive, not destructive."""
    assert _validate_provider_override("FutureAgent", None) == "openrouter"
    assert _validate_provider_override("FutureReasoningAgent", None) == "openrouter"
