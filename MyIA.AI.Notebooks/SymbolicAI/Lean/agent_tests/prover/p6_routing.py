"""P6 per-agent routing map (#7477 P6 forensic fuller fix).

Background (P6, 2026-07-19, #7477): the GLM-5.2 workhorse upgrade was
intended (per #1289) for the *fast* agents (Search, Critic, Diagnosis) that
do the high-volume, low-creative work — Search for lemma mining, Critic
for failure analysis routing. The forensic observed that:

  * ``create_search_agent`` defaults to ``provider="local"`` (Qwen3.6,
    which has documented ``finish_reason: length`` empties on Search
    workloads — 2026-05-11 BG iter 2 trace L849).
  * ``create_critic_agent`` defaults to ``provider="openrouter"`` (Claude
    Haiku 4.5 fast) which is overkill for a routing-decision agent and
    burns Anthropic budget on work that z.ai handles for a tenth of the
    cost.

P6 says the workhorse (``zai`` / GLM-5.2) should be exercised where search
*is* needed. The fix demotes ``local`` and ``openrouter`` as the Search
and Critic defaults and promotes ``zai`` to that role.

This helper centralises the *intent* (which provider is expected for each
agent) so the wiring stays auditable + testable stdlib-only, mirroring the
``p4_final_verify.py`` pattern (#7477 P4, #7533 MERGEABLE).

Anti-regression note: this helper does NOT mutate the live prover state.
``MultiAgentSorryProver.__init__`` reads ``_expected_provider(name)`` to
override the historical defaults, but the live ``create_*_agent``
signatures remain unchanged — callers that explicitly pass a provider
override (e.g. for tests) keep their value.
"""

from __future__ import annotations

# Per-agent expected provider, drawn from the forensic #7477 P6 + #1289.
#
# Naming rationale: ``zai`` = z.ai GLM-5.2 (the intended workhorse per
# #1289 follow-up); ``local`` = Qwen3.6 35B-A3B (faster but hang-prone on
# Search); ``openrouter`` = Anthropic Claude Haiku 4.5 fast (overkill for
# routing-decision work, expensive at scale).
#
# The trio of agents listed below were routed away from ``zai`` in the
# historical defaults despite being workhorse-class (``model_key="fast"``).
# Restoring ``zai`` is the P6 fuller fix.
_EXPECTED_PROVIDERS = {
    # model_key="fast" — high-volume lemma mining workhorse.
    "SearchAgent": "zai",
    # model_key="fast" — failure-analysis routing-decision workhorse.
    "CriticAgent": "zai",
    # model_key="fast" — qualitative verification workhorse (only used
    # when ``--use-diagnosis-agent`` flag is set).
    "DiagnosisAgent": "zai",
}


def _expected_provider(agent_name: str) -> str | None:
    """Return the canonical provider for an agent name, or ``None`` if
    the agent has no P6 routing constraint (e.g. reasoning-class agents
    Tactic/Coordinator/Director where #1289 already routed away from
    ``zai`` for valid latency reasons).

    Stdlib-only — safe to import without the LLM stack.
    """
    return _EXPECTED_PROVIDERS.get(agent_name)


def _iter_expected_agents() -> list[tuple[str, str]]:
    """Return the ``(agent_name, expected_provider)`` pairs covered by P6.

    Used by ``test_p6_routing.py`` to assert the map is non-empty AND
    covers exactly the workhorse-class agents. Reasoning-class agents
    (Tactic/Coordinator/Director) are explicitly NOT in scope: their
    #1289 routing is owner-locked and out of the P6 mandate.
    """
    return list(_EXPECTED_PROVIDERS.items())


def _validate_provider_override(agent_name: str, override: str | None) -> str:
    """Resolve the effective provider for an agent, honoring an explicit
    override when supplied.

    ``override=None`` means "no caller override, use the P6 default".
    Any non-None value is returned as-is (caller knows best — these are
    tests or pre-prod tooling that intentionally pin a different
    provider). Stdlib-only.
    """
    if override is not None:
        return override
    expected = _expected_provider(agent_name)
    if expected is None:
        # Reasoning-class agents — fall back to a sane default that
        # matches the historical MultiAgentSorryProver routing.
        return "openrouter"
    return expected
