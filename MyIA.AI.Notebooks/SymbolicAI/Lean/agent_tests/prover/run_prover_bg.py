#!/usr/bin/env python3
"""Launch the multi-agent prover on a specific sorry target.

Usage:
    python run_prover_bg.py --demo 9 --mode multi --iterations 10
    python run_prover_bg.py --file path/to.lean --line 563 --mode autonomous --iterations 8

Supports both demo-based (from prover/__init__.py DEMOS) and direct file/line targeting.
"""
import argparse
import asyncio
import json
import sys
import time
from pathlib import Path

sys.stdout.reconfigure(line_buffering=True)
sys.stderr.reconfigure(line_buffering=True)

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from prover import DEMOS, PROVED_DEMOS, TraceLogger
from prover.provers import MultiAgentSorryProver, AutonomousProver
from prover.config import create_client
from prover.lean_utils import count_real_sorries
from prover.tree_lock import (
    acquire_tree_lock,
    find_lean_project_root,
    release_tree_lock,
)

TRACES_DIR = Path(__file__).parent / "traces"
TRACES_DIR.mkdir(exist_ok=True)


def _derive_result_kind(result, final_sorry: int, original_sorry: int) -> str:
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
      no_progress      -> diagnostic data only

    Real progress outranks the outage flag: a run that lowered the sorry count
    (or landed a decomposition) before the provider died is still a harvest —
    the outage remains visible via result["provider_failures"].
    """
    if isinstance(result, dict) and result.get("error"):
        return "crashed"
    if final_sorry < original_sorry:
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
    return "no_progress"


def run_prover(demo_num: int = None, filepath: str = None, line: int = None,
               mode: str = "multi", iterations: int = 8,
               provider: str = "zai", local_provider: str = "local",
               goal: str = "", director_provider: str = None,
               coordinator_provider: str = None,
               tactic_provider: str = None,
               use_diagnosis_agent: bool = False,
               concurrent_search_count: int = 0,
               force_lock: bool = False):
    """Run the prover on a target."""
    if demo_num is not None:
        if demo_num not in DEMOS:
            print(f"Demo {demo_num} not found. Available: {sorted(DEMOS.keys())}")
            sys.exit(1)
        if demo_num in PROVED_DEMOS:
            print(f"Demo {demo_num} ({DEMOS[demo_num]['name']}) is PROVED — skipping.")
            sys.exit(0)
        demo = DEMOS[demo_num]
        filepath = demo["file"]
        line = demo.get("line")
        name = demo["name"]
    elif filepath:
        demo = {"file": filepath, "name": f"custom_{Path(filepath).stem}_L{line}",
                "line": line, "goal": goal}
        name = demo["name"]
    else:
        print("Must specify --demo or --file/--line")
        sys.exit(1)

    # One prover per tree (#6790): run-7 was launched through THIS launcher
    # while run-6 held the same tree — run-7's cleanup reverted run-6's
    # build-passing candidate. Refuse the second run instead.
    tree_root = find_lean_project_root(filepath) or Path(filepath).resolve().parent
    lock_path, lock_msg = acquire_tree_lock(
        tree_root, demo_num if demo_num is not None else name, force=force_lock,
    )
    if lock_path is None:
        print(f"[LOCKED] {lock_msg}")
        return {"name": name, "result_kind": "locked", "reason": lock_msg}
    print(f"[TREE_LOCK] {lock_path}")
    try:
        return _run_prover_locked(
            demo, name, filepath, line, mode, iterations, provider,
            local_provider, director_provider, coordinator_provider,
            tactic_provider, use_diagnosis_agent, concurrent_search_count,
        )
    finally:
        release_tree_lock(lock_path)


def _run_prover_locked(demo, name, filepath, line, mode, iterations, provider,
                       local_provider, director_provider, coordinator_provider,
                       tactic_provider, use_diagnosis_agent,
                       concurrent_search_count):
    """The original run body, executed while holding the tree lock."""
    original = Path(filepath).read_text(encoding="utf-8")
    original_sorry = count_real_sorries(original)
    print(f"Target: {name}")
    print(f"  File: {filepath} (line {line})")
    print(f"  Mode: {mode}, Iterations: {iterations}")
    print(f"  Provider: {provider}, Local: {local_provider}, Tactic: {tactic_provider or 'openrouter (default)'}, Coordinator: {coordinator_provider or 'openrouter (default)'}")
    print(f"  Initial sorry count: {original_sorry}")
    print()

    # P3 (#1453): dynamic pre-check — skip the (expensive) prover spawn when the
    # target file already has no sorry. The static PROVED_DEMOS set (above) only
    # covers demos curated by hand and goes stale; a target solved since the last
    # curation — or any direct --file/--line target that is already clean — would
    # otherwise still spawn a full multi-agent run for zero work (the forensic
    # "already-solved schedule" pathology). A count of 0 is a SAFE skip signal:
    # count_real_sorries strips comments/docstrings and word-bounds the token, so
    # == 0 guarantees there is genuinely nothing to prove and can never skip a
    # live target. (count > 0 still spawns the prover, exactly as before.)
    if original_sorry == 0:
        print(f"Already solved: 0 sorry in {filepath} — skipping prover spawn.")
        trace_name = f"{mode}_{name.replace(' ', '_')}_{provider}"
        summary = {
            "name": name,
            "mode": mode,
            "provider": provider,
            "coordinator_provider": coordinator_provider or "openrouter (default)",
            "iterations": iterations,
            "actual_iterations": 0,
            "original_sorry": 0,
            "final_sorry": 0,
            "sorry_delta": 0,
            "result_kind": "already_solved",
            "elapsed_s": 0.0,
            "result": {"status": "already_solved",
                       "reason": "0 sorry in target file (pre-check, no prover spawn)"},
            "trace_file": None,
            "timestamp": time.strftime("%Y-%m-%dT%H:%M:%S"),
        }
        summary_path = TRACES_DIR / f"{trace_name}_result.json"
        summary_path.write_text(
            json.dumps(summary, indent=2, ensure_ascii=False, default=str),
            encoding="utf-8",
        )
        print(f"Summary: {summary_path}")
        return summary

    trace = TraceLogger(output_dir=str(TRACES_DIR))

    if mode == "multi":
        prover = MultiAgentSorryProver(
            trace=trace, provider=provider, local_provider=local_provider,
            director_provider=director_provider,
            coordinator_provider=coordinator_provider,
            tactic_provider=tactic_provider)
        if director_provider:
            print(f"  Director: ENABLED (provider={director_provider})")
    else:
        prover = AutonomousProver(trace=trace, provider=provider)

    start = time.time()
    try:
        if mode == "multi":
            result = asyncio.run(
                prover.prove_sorry(demo=demo, max_iterations=iterations,
                                   use_diagnosis_agent=use_diagnosis_agent,
                                   concurrent_search_count=concurrent_search_count)
            )
        else:
            result = prover.prove_sorry(demo=demo, max_iterations=iterations)
    except Exception as e:
        print(f"\nProver crashed: {e}")
        result = {"error": str(e)}
    elapsed = time.time() - start

    final = Path(filepath).read_text(encoding="utf-8")
    final_sorry = count_real_sorries(final)

    result_kind = _derive_result_kind(result, final_sorry, original_sorry)

    trace_name = f"{mode}_{name.replace(' ', '_')}_{provider}"
    trace_path = trace.save(trace_name)

    print(f"\n{'='*60}")
    # FX-9 (#1453, ai-01 L2536 harvest): the prover result dict carries a
    # boolean ``success`` field, not a string ``status`` field — reading the
    # latter always fell through to the ``unknown`` default. Derive the
    # SUCCESS/FAILED label from the boolean to match the prover's own internal
    # RESULT line (provers.py:880/1580).
    _success = bool(result.get("success")) if isinstance(result, dict) else False
    print(f"RESULT: {'SUCCESS' if _success else 'FAILED'}")
    print(f"  Verdict: {result_kind}")
    print(f"  Sorry: {original_sorry} → {final_sorry}")
    _actual_iters = result.get("iterations") if isinstance(result, dict) else None
    print(f"  Iterations: {_actual_iters if _actual_iters is not None else '?'}/{iterations} (actual/budget)")
    print(f"  Time: {elapsed:.1f}s")
    print(f"  Trace: {trace_path}")
    print(f"{'='*60}")

    # Save result summary
    summary = {
        "name": name,
        "mode": mode,
        "provider": provider,
        "coordinator_provider": coordinator_provider or "openrouter (default)",
        # `iterations` is the REQUESTED budget (the max_iterations CLI arg). Kept
        # under this key for backward compat with existing trace analyzers.
        # `actual_iterations` is how many iterations the prover actually ran
        # (from the prover result; None if the run crashed before reporting).
        # Forensic (#1453 P4): the summary previously exposed only the budget, so
        # a run that hit the cap and one that exited early after 2 iterations were
        # indistinguishable in the top-level field — the actual count was buried
        # in `result["iterations"]`. Both are now legible side by side.
        "iterations": iterations,
        "actual_iterations": result.get("iterations") if isinstance(result, dict) else None,
        "original_sorry": original_sorry,
        "final_sorry": final_sorry,
        # Convention: sorry_delta = final - original. POSITIF = REGRESSION (plus de sorry), NEGATIF = progres. Oppose a tools.py (original - current). Forensic #1453 2026-06-23.
        "sorry_delta": final_sorry - original_sorry,
        "sorry_reduction": original_sorry - final_sorry,  # positif = progres (lecture non ambigue)
        # Canonical verdict (see _derive_result_kind): sorry_decreased |
        # structural_only | provider_outage | no_progress | crashed |
        # already_solved | heartbeat_budget_exceeded | decomposition_regression.
        "result_kind": result_kind,
        "elapsed_s": round(elapsed, 1),
        "result": result,
        "trace_file": trace_path,
        "timestamp": time.strftime("%Y-%m-%dT%H:%M:%S"),
    }
    summary_path = TRACES_DIR / f"{trace_name}_result.json"
    summary_path.write_text(
        json.dumps(summary, indent=2, ensure_ascii=False, default=str),
        encoding="utf-8",
    )
    print(f"Summary: {summary_path}")

    return summary


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Run Lean prover on a target")
    parser.add_argument("--demo", type=int, help="Demo number from DEMOS dict")
    parser.add_argument("--file", help="Target .lean file path")
    parser.add_argument("--line", type=int, help="Sorry line number")
    parser.add_argument("--goal", default="", help="Goal state override for KB matching")
    parser.add_argument("--mode", default="multi", choices=["multi", "autonomous"])
    parser.add_argument("--iterations", type=int, default=8)
    parser.add_argument("--provider", default="openrouter",
                        help="Provider for AutonomousProver auto-mode agent "
                             "(default: openrouter). #1459: GLM-5.1 (zai) causes "
                             "87.8%% rate-limit errors; GPT-5.5 via openrouter "
                             "eliminates the cascade. Use 'zai' for fallback.")
    parser.add_argument("--local-provider", default="local")
    parser.add_argument("--director-provider", default=None,
                        help="Provider for the frontier DirectorAgent "
                             "(e.g. 'openrouter'). Omit to disable the "
                             "Director lane. Only used in --mode multi.")
    parser.add_argument("--coordinator-provider", default=None,
                        help="Provider for CoordinatorAgent (default: openrouter). "
                             "#1289: GLM-5.1 (zai) times out on complex Lean contexts; "
                             "GPT-5.5 via openrouter is 6x faster. "
                             "Only used in --mode multi.")
    parser.add_argument("--tactic-provider", default=None,
                        help="Provider for TacticAgent (default: openrouter). "
                             "#1289: GLM-5.1 (zai) times out at 1680s on complex "
                             "Lean tactic generation; GPT-5.5 via openrouter "
                             "expected ~60-120s. Only used in --mode multi.")
    parser.add_argument("--use-diagnosis-agent", action="store_true",
                        help="Enable DiagnosisAgent (LLM-powered qualitative "
                             "verification replacing mechanical VerifyExecutor). "
                             "Only used in --mode multi.")
    parser.add_argument("--concurrent-search", type=int, default=0,
                        help="Number of ADDITIONAL SearchAgents to run in "
                             "parallel (B.7). 0 = single search (default). "
                             "E.g. --concurrent-search 2 = 3 total search agents. "
                             "Only used in --mode multi.")
    parser.add_argument("--force-lock", action="store_true",
                        help="Break an existing .prover.lock even if its holder "
                             "looks alive or is on a foreign host (WSL<->Windows). "
                             "Operator decision — see #6790.")
    args = parser.parse_args()

    summary = run_prover(
        demo_num=args.demo,
        filepath=args.file,
        line=args.line,
        mode=args.mode,
        iterations=args.iterations,
        provider=args.provider,
        local_provider=args.local_provider,
        goal=args.goal,
        director_provider=args.director_provider,
        coordinator_provider=args.coordinator_provider,
        tactic_provider=args.tactic_provider,
        use_diagnosis_agent=args.use_diagnosis_agent,
        concurrent_search_count=args.concurrent_search,
        force_lock=args.force_lock,
    )
    if isinstance(summary, dict) and summary.get("result_kind") == "locked":
        sys.exit(3)  # same contract as the outer launcher (#6790)
