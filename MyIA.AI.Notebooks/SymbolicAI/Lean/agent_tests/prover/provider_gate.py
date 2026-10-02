"""Fail-fast provider credential gate, shared by both prover launchers (#18709).

Extracted from ``agent_tests/run_prover_bg.py`` (#1453 forensic, 2026-09-19)
so the inner launcher (``prover/run_prover_bg.py``) gates identically instead
of discovering a keyless P6-pinned agent 45 min into a run. Founder case
(#18709, po-2025, 2026-10-01, measured firsthand x2): ``--provider zai
--local-provider local`` crashed after build + GoalExtract because
SearchAgent/CriticAgent are P6-pinned to ``zai`` (``p6_routing``) with no
``ZAI_API_KEY`` on the lane, and the inner launcher exposed no
``--search-provider``/``--critic-provider``/``--diagnosis-provider`` override
and no credential gate — the crash surfaced only as ``Prover crashed``.

Design: pure functions + the providers mapping passed as a parameter, so the
gate stays importable and testable without the LLM stack (stdlib-only besides
``p6_routing``, mirroring the ``p4_final_verify.py`` pattern). Gate semantics
(keyless-by-design localhost, empty base_url refusal) are unchanged from the
#1453 gate — #18709 only widens their reach to the inner launcher.
"""

from __future__ import annotations

from urllib.parse import urlparse

from prover.p6_routing import _expected_provider

# Provider name -> env var carrying its API key. Unknown providers fall back
# to ``<NAME>_API_KEY`` at validation time (same contract as the #1453 gate).
PROVIDER_ENV_KEYS = {
    "zai": "ZAI_API_KEY",
    "openrouter": "OPENROUTER_API_KEY",
    "mistral": "MISTRAL_API_KEY",
    "local": "LOCAL_LLM_API_KEY",
}


def effective_agent_providers(
    provider,
    local_provider,
    *,
    coordinator_provider=None,
    tactic_provider=None,
    search_provider=None,
    critic_provider=None,
    diagnosis_provider=None,
    director_provider=None,
    use_diagnosis_agent=False,
) -> dict:
    """Resolve the per-role provider map exactly as the prover will.

    Mirrors ``MultiAgentSorryProver.__init__`` (provers.py: openrouter
    defaults for coordinator/tactic) and p6_routing's ``_expected_provider``
    (zai for Search/Critic) so the gate can never drift from what the
    workflow actually dials.

    ``diagnosis`` enters the map when an override is supplied OR the caller
    will enable the DiagnosisAgent (``use_diagnosis_agent``) — the P6 pin
    then applies and its key must exist. Without either, the agent is never
    constructed and gating it would false-refuse the launch.
    """
    eff = {
        "reasoning": provider,
        "fast": local_provider,
        "coordinator": coordinator_provider or "openrouter",
        "tactic": tactic_provider or "openrouter",
        "search": search_provider or _expected_provider("SearchAgent")
        or "local",
        "critic": critic_provider or _expected_provider("CriticAgent")
        or "local",
    }
    _diagnosis = diagnosis_provider or (
        _expected_provider("DiagnosisAgent") if use_diagnosis_agent else None
    )
    if _diagnosis is not None:
        eff["diagnosis"] = _diagnosis
    if director_provider:
        eff["director"] = director_provider
    return eff


def validate_provider_credentials(eff: dict, providers: dict) -> list:
    """#1453 forensic (2026-09-19): fail-fast credential gate.

    Refuses to launch when a routed provider has no credentials, naming each
    offending role. Keyless by design: localhost endpoints (Ollama/vLLM). An
    empty base_url on provider ``local`` (LOCAL_LLM_BASE_URL unset) targets
    the OpenAI default endpoint with an empty key and is equally refused.

    ``providers`` is the ``PROVIDERS`` mapping from ``prover.config`` (name ->
    dict with ``base_url``/``api_key``), passed as a parameter so this module
    imports stdlib-only.
    """
    problems = []
    for role, name in eff.items():
        cfg = providers.get(name)
        if cfg is None:
            problems.append(f"{role}: unknown provider '{name}'")
            continue
        base = (cfg.get("base_url") or "").strip()
        key = (cfg.get("api_key") or "").strip()
        host = urlparse(base).hostname or ""
        if host in ("localhost", "127.0.0.1", "::1"):
            continue
        env = PROVIDER_ENV_KEYS.get(name, f"{name.upper()}_API_KEY")
        if not base:
            problems.append(
                f"{role} -> '{name}': base_url vide ({env} / base non configurés)"
            )
        elif not key:
            problems.append(
                f"{role} -> '{name}': {env} absent/vide pour {base}"
            )
    return problems
