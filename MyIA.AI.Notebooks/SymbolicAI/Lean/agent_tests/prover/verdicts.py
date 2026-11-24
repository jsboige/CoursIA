"""Canonical prover run verdict — single source for both classifiers.

Forensic #1453. The verdict ladder used to live twice:

  * ``prover/run_prover_bg.py`` — the LIVE classifier, scored when a run ends;
  * ``prover/baselines/analyze_traces.py`` — a hand-copied MIRROR, applied
    retroactively to the legacy ``*_result.json`` wrappers that predate the
    ``result_kind`` field (added 2026-07-02).

The mirror was justified because importing ``run_prover_bg`` pulls
``prover.config`` / ``prover.provers`` / ``lean_utils`` / ``tree_lock`` —
heavy and side-effectful outside the harness runtime. But the copy was kept in
sync by a docstring instruction ("keep the 9-branch precedence in sync"), and
it drifted: by 2026-11-05 the mirror still had 9 branches while the live
classifier had 10, so every legacy freeze-loop wrapper was scored
``no_progress`` retroactively — the very verdict the ``freeze_loop`` /
``no_attempt`` split exists to replace.

The verdict logic is pure dict arithmetic with no dependency on the harness
runtime: it belongs in a module of its own, imported by both sides. Drift
stops being a discipline problem and becomes an import.

Ranked by what a coordinator does next; first match wins.
"""

from __future__ import annotations

__all__ = ["derive_result_kind"]


def derive_result_kind(result, final_sorry, original_sorry) -> str:
    """Canonical run verdict, ranked by what a coordinator does next.

    Forensic #1453 (2026-07-02): a run's outcome was scattered across 4 fields
    (result.status, sorry_delta, structural_progress, error) and every consumer
    re-derived its own verdict — the ai-01 harvest step included.
      sorry_decreased  -> harvest: branch + PR (textual sorry count dropped)
      structural_only  -> keep iterating: decomposition landed, count did not drop
      crashed          -> postmortem the harness, not the proof
      provider_outage  -> the LLM provider died mid-run (circuit-breaker,
                          #5869): the prover never got to work — retry when
                          the provider is back, do NOT read as tactical failure
      correctly_refused-> the Coordinator explicitly abandoned the goal via
                          mark_sorry_intractable (after F9 Director + B2
                          SearchAgent gates) and the workflow yielded before
                          iteration_cap (#7477 P2a). The agent did the right
                          thing by refusing — do NOT read as tactical failure.
      heartbeat_budget_exceeded -> a Lean tactic blew the maxHeartbeats budget
                          (latched in TacticTools.compile via
                          tools._is_heartbeat_timeout, #7477 P5a). Distinct from
                          correctly_refused: the agent did NOT refuse, it tried a
                          tactic too expensive for the budget. Needs a cheaper
                          tactic / higher maxHeartbeats / decomposition, NOT more
                          iterations.
      decomposition_regression -> a net-sorry-INCREASE decomposition with ZERO
                          build-verified tactics (runaway sub-sorry spraying,
                          #7477 P3). Distinct from structural_only: a real
                          restructuring has verified_tactic_count > 0. Tells a
                          coordinator the decomposition was an unproven spray,
                          NOT progress — do NOT harvest / branch it.
      reasoning_budget_exceeded -> the run burned its SESSION reasoning wall-
                          clock (max_session_seconds / workflow_timeout_s)
                          without converging on an edit (latched in the
                          multi-agent `except _asyncio.TimeoutError` or the
                          autonomous WALL-CLOCK CAP branch, #7477 P5a-search).
                          Distinct from heartbeat_budget_exceeded (compile-
                          level Lean maxHeartbeats wall): this is session-level
                          — the agent loop spent the whole budget reasoning and
                          emitted 0 attempts. Forensic: kimi-k3 run `bt56gsv78`
                          (DEMO 62 ne, 8->8, 0 attempts, 1800s Search-phase).
                          Tells a coordinator the arm needs a shorter reasoning
                          budget / different search / smaller decomposition, NOT
                          more wall-clock or iterations.
      freeze_loop      -> TacticAgent never got a tool call through: the
                          freeze-loop guard escalated to Coordinator N times
                          (text-without-tool streaks) with ZERO tactic
                          submissions and the workflow yielded at the hardcap
                          instead of burning iteration_cap (#1453 C3,
                          2026-09-19; founder: qwen2.5:7b emits tool-calls as
                          fenced-JSON prose — 6 firings, 8/8 iterations, 0
                          attempts). Tells a coordinator to change
                          model/provider (tool-calling capability), NOT more
                          iterations.
      no_progress      -> diagnostic data only

    Real progress outranks the outage flag: a run that lowered the sorry count
    (or landed a decomposition) before the provider died is still a harvest —
    the outage remains visible via result["provider_failures"].
    """
    if isinstance(result, dict) and result.get("error"):
        return "crashed"
    if (final_sorry is not None and original_sorry is not None
            and final_sorry < original_sorry):
        return "sorry_decreased"
    if isinstance(result, dict) and result.get("structural_progress"):
        return "structural_only"
    if isinstance(result, dict) and result.get("provider_outage"):
        return "provider_outage"
    # P2a (#7477 forensic): the Coordinator explicitly abandoned the goal via
    # mark_sorry_intractable (after F9 Director + B2 SearchAgent gates) and the
    # workflow yielded before iteration_cap. Ranked AFTER sorry_decreased /
    # structural_only: a run that lowered the sorry count or landed a verified
    # decomposition before abandoning is still progress — the abandonment flag
    # only reclassifies what would otherwise be no_progress. Forensic DEMO 62
    # (NW L2970, a DO-NOT-TARGET line): correctly refused 4× but previously
    # scored no_progress + burned iteration_cap. correctly_refused lets a
    # coordinator distinguish "agent did the right thing" from "agent spun".
    if isinstance(result, dict) and result.get("intractable"):
        return "correctly_refused"
    # P5a (#7477 forensic): a Lean tactic blew the maxHeartbeats budget
    # (latched in TacticTools.compile via tools._is_heartbeat_timeout). Ranked
    # AFTER sorry_decreased / structural_only: a run that lowered the sorry
    # count or landed a verified decomposition before blowing the budget is
    # still progress — this flag only reclassifies what would otherwise be
    # no_progress. Distinct from correctly_refused (the agent did NOT refuse;
    # it tried a tactic too expensive for the budget). Tells a coordinator the
    # target needs a cheaper tactic / higher maxHeartbeats / decomposition,
    # NOT more iterations.
    if isinstance(result, dict) and result.get("heartbeat_budget_exceeded"):
        return "heartbeat_budget_exceeded"
    # P3 (#7477 forensic): a net-sorry-INCREASE decomposition with ZERO build-
    # verified tactics — a spray of unproven sub-sorries the multi-agent path
    # previously mis-labelled as structural_progress (founder L2551 grew 4->8
    # with verified_tactic_count==0 across 11 dedup'd runs). provers.py classifies
    # this via is_decomposition_regression(final, original, verified) and, on a
    # regression, forces structural_progress=False + sets the
    # decomposition_regression flag; this branch surfaces the precise pathology
    # for the forensic harvest instead of letting it fall through to no_progress.
    # Ranked AFTER sorry_decreased / structural_only / provider_outage /
    # correctly_refused / heartbeat_budget_exceeded: those outrank it (a run that
    # lowered sorry, landed a verified decomposition, or hit an
    # outage/refusal/budget wall first ranks as that outcome). Mutually exclusive
    # with structural_only in practice — the P3 guard only fires when
    # structural_progress was demoted. Legacy-safe: a result dict without the
    # field (autonomous path / old traces) returns None -> falsy -> no_progress,
    # identical to the classifier's None->False contract.
    if isinstance(result, dict) and result.get("decomposition_regression"):
        return "decomposition_regression"
    # P5a-search (#7477 forensic, jsboige A-B 2026-07-20): the run burned its
    # session reasoning wall-clock without converging on an edit (0 attempts).
    # Ranked AFTER sorry_decreased / structural_only / provider_outage /
    # correctly_refused / heartbeat_budget_exceeded / decomposition_regression:
    # those are all more specific pathologies (real progress, provider death,
    # explicit refusal, compile-level heartbeat wall, unverified spray). This
    # flag only reclassifies what would otherwise be no_progress — the most
    # generic budget-wall diagnosis. Distinct from heartbeat_budget_exceeded
    # (compile-level): here the agents never got a tactic to the compiler, they
    # spent the whole budget in Search-phase reasoning. Forensic kimi-k3 run
    # `bt56gsv78` (DEMO 62 ne, 8->8, 0 attempts, 1800s) previously scored
    # no_progress; reasoning_budget_exceeded lets a coordinator distinguish
    # "agent spun reasoning without editing" from "agent tried and failed".
    if isinstance(result, dict) and result.get("reasoning_budget_exceeded"):
        return "reasoning_budget_exceeded"
    # C3 (#1453 calibration forensic, po-2024 2026-09-19): the freeze-loop
    # escalation hardcap ended the run — the C617 guard forced N Coordinator
    # handoffs (TacticAgent text-without-tool streaks) while tactic_history
    # stayed EMPTY. The model structurally cannot tool-call (founder case:
    # qwen2.5:7b via Ollama emits tool-calls as fenced-JSON prose; the harness
    # echoes its own text back as [receive] — 6 guard firings, 8/8 iterations,
    # 0 attempts). Ranked after every progress/outage/refusal flag (mutually
    # exclusive with them by construction: the yield requires an empty
    # tactic_history, so no sorry/structural outcome can precede it). Tells a
    # coordinator to change model/provider (tool-calling capability), NOT more
    # iterations. Legacy-safe: field absent -> falsy -> no_progress.
    if isinstance(result, dict) and result.get("freeze_loop"):
        # Cycle-29 split (#1453, po-2025 measure 2026-11-04, DEMO 45 spans
        # 13:44Z): a yield with ZERO tactic submissions is not a proof
        # failure — the model never attempted one. The final verdict must
        # distinguish "never tried" from "tried and froze": for no_attempt
        # the lever is model/provider (tool-calling capability), for a
        # freeze AFTER real attempts more iterations can still pay (the
        # agent demonstrably tool-calls). Today the latch guarantees
        # attempts==0 on this path (the yield requires an empty
        # tactic_history), so attempts>0 is the defensive branch kept for
        # future freeze sources. Legacy-safe: attempts absent -> falsy ->
        # no_attempt, which is what the latch produced anyway.
        if not result.get("attempts"):
            return "no_attempt"
        return "freeze_loop"
    return "no_progress"
