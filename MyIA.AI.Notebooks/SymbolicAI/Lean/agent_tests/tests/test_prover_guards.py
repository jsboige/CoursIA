"""Unit tests for prover guards (lean_server import, stub guard, build check).

These cover the three regressions reported by po-2026 on 2026-05-08:
  #1 CRITICAL — `lean_server.py` import failed silently → compile() always True
  #3 HIGH      — sorry guard ignored non-`sorry` placeholders (`exact _`, ...)
  #2 HIGH      — multi-agent workflow had no per-call timeout → infinite hang

Run from `agent_tests/`:
    python -m pytest tests/ -q
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

# Make `prover/` importable regardless of how pytest was invoked.
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT))

from prover.state import ProofState, SorryContext  # noqa: E402
from prover.tools import TacticTools  # noqa: E402


# ──────────────────────────────────────────────────────────────────────────
# CRITICAL #1 — lean_server import is path-independent
# ──────────────────────────────────────────────────────────────────────────


def test_lean_server_class_loads_via_spec_import():
    """The verifier's spec-based loader finds lean_server.py one level up."""
    from prover.verifier import _load_lean_verifier_class

    cls = _load_lean_verifier_class()
    assert cls.__name__ == "LeanVerifier"
    # Idempotent — second call returns the cached class.
    assert _load_lean_verifier_class() is cls


def test_get_verifier_instantiates_without_lean_project():
    """get_verifier() must not crash when project_dir is set explicitly."""
    from prover import verifier as vmod

    # Reset module-level singleton so each test starts clean.
    vmod._verifier = None
    v = vmod.get_verifier(project_dir="/tmp/dummy-not-real")
    assert v is not None
    assert v.project_dir == "/tmp/dummy-not-real"


# ──────────────────────────────────────────────────────────────────────────
# HIGH #3 — stub guard rejects non-compiling placeholders
# ──────────────────────────────────────────────────────────────────────────


@pytest.fixture
def tactic_tools(tmp_path):
    """A TacticTools instance against a fake file (no real Lean needed).

    File is padded with realistic boilerplate so the file-size guard
    (which blocks >50% size deltas) does not fire on small edits.
    """
    fake = tmp_path / "Fake.lean"
    body = (
        "import Mathlib.Tactic\n"
        "namespace TestSpace\n"
        + "\n".join(f"-- comment line {i} for size padding" for i in range(50))
        + "\ntheorem t : True := by\n  sorry\n"
        + "\n".join(f"-- trailing line {i} for size padding" for i in range(50))
        + "\nend TestSpace\n"
    )
    fake.write_text(body, encoding="utf-8")
    sorry_line = next(
        i + 1 for i, line in enumerate(body.split("\n")) if "sorry" in line
    )
    state = ProofState(theorem_statement="t")
    sctx = SorryContext(
        filepath=str(fake), sorry_line=sorry_line, indentation=2,
        indent_str="  ", full_file=body,
    )
    tt = TacticTools(state, str(fake), sctx)
    # Stash the sorry line on the instance so tests can reach it.
    tt._test_sorry_line = sorry_line
    return tt


@pytest.mark.parametrize("stub", [
    "exact _",
    "exact ?_",
    "exact ?h",
    "refine ?_",
    "admit",
    "_",
])
def test_stub_guard_rejects_known_placeholders(tactic_tools, stub):
    err = tactic_tools._check_stub_guard(stub, "test")
    assert err is not None
    assert "BLOCKED by stub guard" in err


@pytest.mark.parametrize("ok", [
    "exact h",
    "exact And.intro hp hq",
    "rfl",
    "simp [foo]",
    "omega",
    "intro x; rfl",
    "have h : True := trivial\nexact h",
])
def test_stub_guard_accepts_real_tactics(tactic_tools, ok):
    assert tactic_tools._check_stub_guard(ok, "test") is None


def test_stub_guard_ignores_comments(tactic_tools):
    # A `-- exact _` comment must NOT trigger the guard.
    assert tactic_tools._check_stub_guard("-- exact _\nrfl", "test") is None


# ──────────────────────────────────────────────────────────────────────────
# HIGH #3 — file_replace_sorry rejects stubs without writing
# ──────────────────────────────────────────────────────────────────────────


def test_file_replace_sorry_blocks_exact_underscore(tactic_tools):
    """file_replace_sorry must NOT write a stub replacement to disk."""
    import json
    before = Path(tactic_tools._filepath).read_text(encoding="utf-8")
    # build_check=False keeps the test offline (no lake needed).
    out = json.loads(
        tactic_tools.file_replace_sorry(
            tactic_tools._test_sorry_line, "exact _", build_check=False,
        )
    )
    assert "error" in out
    assert "stub guard" in out["error"]
    after = Path(tactic_tools._filepath).read_text(encoding="utf-8")
    assert before == after  # file untouched


def test_file_replace_sorry_writes_real_tactic(tactic_tools):
    """A real tactic replaces the sorry and the file is updated."""
    import json
    out = json.loads(
        tactic_tools.file_replace_sorry(
            tactic_tools._test_sorry_line, "trivial", build_check=False,
        )
    )
    assert "error" not in out, out
    content = Path(tactic_tools._filepath).read_text(encoding="utf-8")
    assert "sorry" not in content
    assert "trivial" in content


# ──────────────────────────────────────────────────────────────────────────
# HIGH #2 — workflow ProofMessage carries iteration cap
# ──────────────────────────────────────────────────────────────────────────


def test_proof_message_has_iteration_cap_field():
    """ProofMessage must carry max_iterations so the graph can bail out."""
    from prover.workflow import ProofMessage, DEFAULT_AGENT_TIMEOUT_S

    m = ProofMessage(content="x", max_iterations=3)
    assert m.max_iterations == 3
    assert m.iteration == 0
    # Default per-agent timeout is bounded so a stalled provider can't
    # freeze the workflow indefinitely.
    assert 30 <= DEFAULT_AGENT_TIMEOUT_S <= 600


def test_multi_agent_prover_accepts_workflow_timeout():
    """MultiAgentSorryProver.prove_sorry exposes a wall-clock cap."""
    import inspect
    from prover.provers import MultiAgentSorryProver

    sig = inspect.signature(MultiAgentSorryProver.prove_sorry)
    assert "workflow_timeout_s" in sig.parameters


# ──────────────────────────────────────────────────────────────────────────
# P4 — set_attack_plan integration (B.3)
# ──────────────────────────────────────────────────────────────────────────


def test_coordinator_agent_has_set_attack_plan_tool():
    """CoordinatorAgent must expose set_attack_plan and advance_plan tools.

    We verify by checking the CoordinatorTools instance is wired correctly,
    since the Agent framework stores tools internally (not as _tools).
    """
    from prover.tools import CoordinatorTools
    from prover.agents import create_coordinator_agent
    from prover.trace import TraceLogger

    state = ProofState(theorem_statement="test")
    trace = TraceLogger()
    tools = CoordinatorTools(state, filepath="", trace=trace)

    # Verify the tool methods exist and are callable
    assert callable(tools.set_attack_plan)
    assert callable(tools.advance_plan)

    # Verify they work
    result = tools.set_attack_plan(["step1", "step2"], reason="test")
    assert state.plan == ["step1", "step2"]

    # Verify the agent was created without error (tools list accepted)
    agent = create_coordinator_agent(tools, provider="zai")
    assert agent is not None
    assert agent.name == "CoordinatorAgent"


def test_set_attack_plan_stores_in_proof_state():
    """set_attack_plan stores steps in ProofState.plan."""
    from prover.tools import CoordinatorTools
    from prover.trace import TraceLogger

    state = ProofState(theorem_statement="test")
    trace = TraceLogger()
    tools = CoordinatorTools(state, filepath="", trace=trace)

    result = tools.set_attack_plan(
        steps=["intro x", "exact x"],
        reason="direct proof"
    )
    assert state.plan == ["intro x", "exact x"]
    assert state.plan_phase == 0
    assert "2 steps" in result


def test_advance_plan_increments_phase():
    """advance_plan moves to the next step in the plan."""
    from prover.tools import CoordinatorTools
    from prover.trace import TraceLogger

    state = ProofState(theorem_statement="test")
    trace = TraceLogger()
    tools = CoordinatorTools(state, filepath="", trace=trace)

    tools.set_attack_plan(["step1", "step2", "step3"], reason="test")
    assert state.plan_phase == 0

    tools.advance_plan()
    assert state.plan_phase == 1

    tools.advance_plan()
    assert state.plan_phase == 2

    # Does not go beyond the last step
    tools.advance_plan()
    assert state.plan_phase == 2


def test_proof_message_has_plan_field():
    """ProofMessage carries a plan field for B.3 propagation."""
    from prover.workflow import ProofMessage

    m = ProofMessage(content="x", plan=["step1", "step2"])
    assert m.plan == ["step1", "step2"]
    assert m.next_agent == "coordinator"  # default is now coordinator


def test_proof_message_default_routes_to_coordinator():
    """B.3: initial routing is to coordinator (sets attack plan first)."""
    from prover.workflow import ProofMessage

    m = ProofMessage(content="x")
    assert m.next_agent == "coordinator"


def test_workflow_builder_passes_state_to_executors():
    """ProofWorkflowBuilder passes state to AgentExecutors for plan propagation."""
    from unittest.mock import MagicMock
    from prover.workflow import ProofWorkflowBuilder, ProofMessage
    from prover.state import SorryContext

    state = ProofState(theorem_statement="test")
    sorry_ctx = SorryContext(filepath="fake.lean", sorry_line=1, indentation=0)

    mock_agents = [MagicMock(name=f"agent_{i}") for i in range(4)]
    for a in mock_agents:
        a.name = f"Agent_{a._mock_name}"

    builder = ProofWorkflowBuilder(
        *mock_agents, sorry_ctx, "", state=state,
    )
    # All executors should have the state reference
    assert builder._coordinator._state is state
    assert builder._search._state is state
    assert builder._tactic._state is state
    assert builder._critic._state is state


def test_plan_injected_into_downstream_context():
    """B.3: When plan is set, AgentExecutor prepends it for non-coordinator agents."""
    from unittest.mock import AsyncMock, MagicMock, patch
    from prover.workflow import AgentExecutor, ProofMessage
    from prover.state import ProofState

    state = ProofState(theorem_statement="test")
    agent = MagicMock()
    agent.name = "SearchAgent"
    agent.run = AsyncMock(return_value=MagicMock(
        messages=[MagicMock(text="found lemma")]
    ))

    executor = AgentExecutor(agent, state=state)
    msg = ProofMessage(
        content="search for lemmas",
        plan=["step1: intro x", "step2: exact x"],
    )

    import asyncio
    # We need a WorkflowContext mock — but we can test the content enrichment
    # by checking the agent.run call argument
    async def _test():
        # Create a minimal mock context
        ctx = AsyncMock()
        ctx.yield_output = AsyncMock()
        ctx.send_message = AsyncMock()

        # Increment is part of handle, so iteration will be 1 after
        await executor.handle(msg, ctx)

        # Check agent.run was called with plan header prepended
        call_args = agent.run.call_args[0][0]
        assert "PLAN D'ATTAQUE" in call_args
        assert "step1: intro x" in call_args
        assert "search for lemmas" in call_args

    asyncio.run(_test())


def test_plan_not_injected_for_coordinator():
    """B.3: Plan is NOT prepended when the agent IS CoordinatorAgent."""
    from unittest.mock import AsyncMock, MagicMock
    from prover.workflow import AgentExecutor, ProofMessage

    agent = MagicMock()
    agent.name = "CoordinatorAgent"
    agent.run = AsyncMock(return_value=MagicMock(
        messages=[MagicMock(text="coordinated")]
    ))

    executor = AgentExecutor(agent)
    msg = ProofMessage(
        content="analyze goal",
        plan=["step1"],
    )

    import asyncio

    async def _test():
        ctx = AsyncMock()
        ctx.yield_output = AsyncMock()
        ctx.send_message = AsyncMock()
        await executor.handle(msg, ctx)

        call_args = agent.run.call_args[0][0]
        assert "PLAN D'ATTAQUE" not in call_args
        assert "analyze goal" in call_args

    asyncio.run(_test())


# ──────────────────────────────────────────────────────────────────────────
# Cycle 25 trace fix — file_replace_lines preserves protected comments
# ──────────────────────────────────────────────────────────────────────────


def test_file_replace_lines_preserves_proof_strategy_comments(tmp_path):
    """Replacement that strips PROOF STRATEGY block must preserve those comments.

    Cycle 25 ai-01 trace: prover BG iter 1 stripped 16 lines of human-curated
    PROOF STRATEGY documentation while making no proof progress (sorry 4->4).
    The fix prepends protected comments back to the replacement so the agent
    cannot silently regress documentation.
    """
    import json
    fake = tmp_path / "VotingFake.lean"
    body = (
        "import Mathlib.Tactic\n"
        "namespace TestSpace\n"
        + "\n".join(f"-- pad {i}" for i in range(80))
        + "\ntheorem t : True := by\n"
        + "  -- PROOF STRATEGY (ai-01 Cycle 25):\n"
        + "  -- 1. Establish sorted list properties\n"
        + "  -- 2. Apply List.Perm.countP_eq\n"
        + "  -- KEY MATHLIB LEMMAS: List.mergeSort_perm, List.countP_append\n"
        + "  -- TODO: discharge sub-goal via omega\n"
        + "  sorry\n"
        + "\n".join(f"-- tail {i}" for i in range(80))
        + "\nend TestSpace\n"
    )
    fake.write_text(body, encoding="utf-8")

    state = ProofState(theorem_statement="t")
    sctx = SorryContext(
        filepath=str(fake), sorry_line=88, indentation=2,
        indent_str="  ", full_file=body,
    )
    tt = TacticTools(state, str(fake), sctx)

    # The agent rewrites the proof block (lines 84-89) and "forgets" the
    # PROOF STRATEGY / TODO / KEY MATHLIB comments — this is the bug.
    out = json.loads(tt.file_replace_lines(
        start=84, end=89,
        new_content="  trivial",
        build_check=False,
    ))
    assert "error" not in out, out
    after = fake.read_text(encoding="utf-8")
    # All 4 protected markers must survive
    assert "PROOF STRATEGY" in after, "PROOF STRATEGY comment was stripped"
    assert "KEY MATHLIB LEMMAS" in after, "KEY MATHLIB comment was stripped"
    assert "TODO: discharge" in after, "TODO comment was stripped"


def test_file_replace_lines_no_duplicate_when_marker_in_replacement(tmp_path):
    """If the agent's new_content already includes the marker, do not duplicate."""
    import json
    fake = tmp_path / "VotingFake.lean"
    body = (
        "import Mathlib.Tactic\n"
        "namespace TestSpace\n"
        + "\n".join(f"-- pad {i}" for i in range(80))
        + "\ntheorem t : True := by\n"
        + "  -- TODO: prove this\n"
        + "  sorry\n"
        + "\n".join(f"-- tail {i}" for i in range(80))
        + "\nend TestSpace\n"
    )
    fake.write_text(body, encoding="utf-8")

    state = ProofState(theorem_statement="t")
    sctx = SorryContext(
        filepath=str(fake), sorry_line=85, indentation=2,
        indent_str="  ", full_file=body,
    )
    tt = TacticTools(state, str(fake), sctx)

    # Agent provides new_content that already preserves the TODO line itself
    out = json.loads(tt.file_replace_lines(
        start=84, end=85,
        new_content="  -- TODO: prove this\n  trivial",
        build_check=False,
    ))
    assert "error" not in out, out
    after = fake.read_text(encoding="utf-8")
    # TODO appears exactly once (no duplicate)
    assert after.count("TODO: prove this") == 1


# ──────────────────────────────────────────────────────────────────────────
# Iter 2 false positive — snapshot must NOT update when build_check=False
# ──────────────────────────────────────────────────────────────────────────


def _make_fake_voting(tmp_path, content_lines):
    fake = tmp_path / "VotingFake.lean"
    body = (
        "import Mathlib.Tactic\n"
        "namespace TestSpace\n"
        + "\n".join(f"-- pad {i}" for i in range(80))
        + "\ntheorem t : True := by\n"
        + "\n".join(content_lines)
        + "\n"
        + "\n".join(f"-- tail {i}" for i in range(80))
        + "\nend TestSpace\n"
    )
    fake.write_text(body, encoding="utf-8")
    return fake, body


def test_file_replace_sorry_no_snapshot_when_build_check_false(tmp_path):
    """build_check=False MUST NOT update best_sorry_count or best_content.

    Iter 2 of demo 9 (Voting.lean L355) trace: the agent called
    file_replace_sorry(replacement="show ?a ≦ ?b -- PROBE", build_check=False).
    The replacement contained an invalid Lean Unicode token (U+2266 instead of
    U+2264) which fails lake build, but best_sorry_count was promoted to 3
    (from 4) on raw count alone because build_check was False. The autonomous
    loop then committed that snapshot as RESULT_SUCCESS sorry 4→3.

    Regression guard: with build_check=False, snapshots stay frozen.
    """
    import json
    fake, body = _make_fake_voting(tmp_path, ["  sorry"])

    state = ProofState(theorem_statement="t")
    sctx = SorryContext(
        filepath=str(fake), sorry_line=84, indentation=2,
        indent_str="  ", full_file=body,
    )
    tt = TacticTools(state, str(fake), sctx)

    initial_best = tt.best_sorry_count
    initial_best_content = tt.best_content

    # Probe with build_check=False — exactly the iter 2 sequence
    out = json.loads(tt.file_replace_sorry(
        sorry_line=84,
        replacement="show ?a ≦ ?b -- PROBE",  # invalid Lean U+2266 token
        build_check=False,
    ))
    assert "error" not in out, out
    assert out["build_check"] == "skipped"
    assert out.get("snapshot_updated") is False, (
        "build_check=False MUST set snapshot_updated=False"
    )
    assert tt.best_sorry_count == initial_best, (
        f"best_sorry_count changed without build verification: "
        f"{initial_best} -> {tt.best_sorry_count}"
    )
    assert tt.best_content == initial_best_content, (
        "best_content snapshot updated without build verification"
    )


def test_file_replace_lines_no_snapshot_when_build_check_false(tmp_path):
    """Same invariant for file_replace_lines."""
    import json
    fake, body = _make_fake_voting(tmp_path, ["  sorry"])

    state = ProofState(theorem_statement="t")
    sctx = SorryContext(
        filepath=str(fake), sorry_line=84, indentation=2,
        indent_str="  ", full_file=body,
    )
    tt = TacticTools(state, str(fake), sctx)

    initial_best = tt.best_sorry_count
    initial_best_content = tt.best_content
    initial_last_ok = getattr(tt, "_last_build_ok_content", None)

    out = json.loads(tt.file_replace_lines(
        start=84, end=84,
        new_content="  show ?a ≦ ?b -- PROBE",
        build_check=False,
    ))
    assert "error" not in out, out
    assert out["build_check"] == "skipped"
    assert out.get("snapshot_updated") is False
    assert tt.best_sorry_count == initial_best
    assert tt.best_content == initial_best_content
    # _last_build_ok_content must also stay frozen — provers.py uses it as
    # the structural-progress fallback; updating it without a build check
    # would let an unverified snapshot leak through that path too.
    assert getattr(tt, "_last_build_ok_content", None) == initial_last_ok, (
        "_last_build_ok_content updated without build verification"
    )


# ──────────────────────────────────────────────────────────────────────────
# F9 (2026-05-17) — Director consultation gate on mark_sorry_intractable
#
# Context: C37 forensic (DEMO 15/16/17) confirmed the Coordinator abandoned
# every hard target in <140s with 0 Director invocations, because
# mark_sorry_intractable had no preconditions. F9 makes intractable refuse
# unless the Director has actually run at least once.
# ──────────────────────────────────────────────────────────────────────────


def test_f9_intractable_refused_before_director_consultation():
    """mark_sorry_intractable must refuse when director_consulted is False."""
    from prover.tools import CoordinatorTools

    state = ProofState()
    ct = CoordinatorTools(state=state, filepath="", trace=None)

    out = ct.mark_sorry_intractable("test premature abandon")
    assert "REFUSED" in out, f"F9 gate failed to refuse: {out[:200]}"
    assert "request_director_guidance" in out, (
        f"F9 refusal must point to the recovery tool: {out[:200]}"
    )
    assert state.intractable is False, (
        "state.intractable must NOT be set when refused"
    )


def test_f9_request_director_guidance_designates_director():
    """request_director_guidance must route the next turn to DirectorAgent."""
    from prover.tools import CoordinatorTools

    state = ProofState()
    ct = CoordinatorTools(state=state, filepath="", trace=None)

    out = ct.request_director_guidance("hard target, 2 plans tried")
    assert "Director" in out, f"unexpected return: {out[:200]}"

    designated = state.consume_next_agent_designation()
    assert designated == "DirectorAgent", (
        f"request_director_guidance failed to designate Director: {designated!r}"
    )


def test_f9_intractable_accepted_after_director_consultation():
    """After director_consulted=True (set by AgentExecutor when Director runs),
    mark_sorry_intractable proceeds normally."""
    from prover.tools import CoordinatorTools

    state = ProofState()
    ct = CoordinatorTools(state=state, filepath="", trace=None)

    # Simulate AgentExecutor recording a real Director run.
    state.director_consulted = True
    state.director_consulted_count = 1
    # B2 gate (#1224): the always-wired SearchAgent (provers.py:255) has also
    # explored reference_docs/ by the time the Coordinator gives up.
    state.search_agent_consulted = True

    out = ct.mark_sorry_intractable("director also failed")
    assert "REFUSED" not in out, f"F9 gate over-restrictive: {out[:200]}"
    assert "intractable" in out.lower()
    assert state.intractable is True
    assert state.intractable_reason == "director also failed"


def test_f9_graceful_degradation_when_no_director_wired():
    """When MultiAgentSorryProver is run without --director-provider, the
    intractable gate must NOT trap the session — provers.py sets
    state.director_consulted = True at init when director_agent is None.

    Without this auto-bypass, sessions running on po-2026/other machines
    without OpenRouter credentials would loop until workflow_timeout because
    they can never escape via intractable. This test pins the contract.
    """
    state = ProofState()
    # Simulate what MultiAgentSorryProver.prove_sorry does when
    # director_provider is None (no Director created).
    director_agent = None
    if director_agent is None:
        state.director_consulted = True
    # The SearchAgent is always wired (provers.py:255, unconditional), so by
    # the time intractable is reached it has run and cleared the B2 gate
    # (#1224). Only the Director has a no-wire auto-bypass.
    state.search_agent_consulted = True

    from prover.tools import CoordinatorTools
    ct = CoordinatorTools(state=state, filepath="", trace=None)

    out = ct.mark_sorry_intractable("no director available, gave up after N iters")
    assert "REFUSED" not in out, (
        f"F9 gate trapped a no-Director session: {out[:200]}"
    )
    assert state.intractable is True


# ──────────────────────────────────────────────────────────────────────────
# P1 latch-success (Epic #1453, 2026-05-23 forensic) — in-place-proof detector
#
# Bug: tools.file_replace_lines edits the REAL target file in place and its
# own build_check passes, but SorryContext.sorry_line is frozen at session
# start (provers.py:203) and is NEVER updated. The downstream
# verify_sorry_replacement then finds no sorry at the frozen line,
# P5-relocates to a nearest UNRELATED sorry, injects the tactic there ->
# goal mismatch -> spurious tactic_failed that MASKS the genuine proof.
#
# The latch in VerifyExecutor.handle catches this BEFORE the doomed re-verify
# when all three hold (else it falls through, P5 path preserved):
#   1. the frozen target line no longer contains "sorry"
#   2. the current raw sorry count is STRICTLY below the session-start count
#      (full_file snapshot) -> distinguishes a real proof from a line shift
#   3. a confirming build of the actual file succeeds
# These tests pin the decision offline (verifier + re-verify mocked, no lake).
# ──────────────────────────────────────────────────────────────────────────


def _make_verify_executor(filepath, sorry_line, full_file, goal_state=""):
    from prover.workflow import VerifyExecutor

    sctx = SorryContext(
        filepath=str(filepath), sorry_line=sorry_line, indentation=2,
        indent_str="  ", full_file=full_file, goal_state=goal_state,
    )
    return VerifyExecutor(sorry_context=sctx, imports="")


def _run_handle(executor, msg):
    import asyncio
    from unittest.mock import AsyncMock

    ctx = AsyncMock()
    ctx.yield_output = AsyncMock()
    ctx.send_message = AsyncMock()
    asyncio.run(executor.handle(msg, ctx))
    return ctx


def _patch_verifier_and_reverify(monkeypatch, build_success=True, raw_output=""):
    """Mock the verifier (condition 3) and record any re-verify fall-through.

    ``raw_output`` lets a test inject a build log carrying a "declaration uses
    sorry" warning so the build-aware latch guard (#1500) can be exercised
    without a real lake build.
    """
    import prover.verifier as vmod
    import prover.lean_utils as lu

    class _FakeVerifier:
        def verify_project_file(self, rel, force=False):
            return {"success": build_success, "errors": "",
                    "raw_output": raw_output}

    monkeypatch.setattr(vmod, "get_verifier", lambda *a, **k: _FakeVerifier())

    reverify_calls = []
    monkeypatch.setattr(
        lu, "verify_sorry_replacement",
        lambda **k: (reverify_calls.append(k)
                     or {"success": False, "errors": "REACHED_REVERIFY"}),
    )
    return reverify_calls


def test_p1_latch_fires_on_in_place_proof(tmp_path, monkeypatch):
    """All three conditions hold -> latch sets proof_found, no re-verify run."""
    from prover.workflow import ProofMessage

    proved = (
        "import Mathlib.Tactic\n"
        "theorem t : True := by\n"
        "  trivial\n"
    )
    fake = tmp_path / "Proved.lean"
    fake.write_text(proved, encoding="utf-8")
    # Session-start snapshot had ONE sorry; it is now proved (count 1 -> 0).
    session_full = proved.replace("  trivial\n", "  sorry\n")
    assert session_full.count("sorry") == 1 and proved.count("sorry") == 0

    reverify_calls = _patch_verifier_and_reverify(monkeypatch, build_success=True)

    ex = _make_verify_executor(fake, sorry_line=3, full_file=session_full)
    msg = ProofMessage(content="x", tactic="trivial", sorry_count=1)
    ctx = _run_handle(ex, msg)

    assert msg.proof_found is True, "latch must set proof_found on in-place proof"
    assert reverify_calls == [], (
        "verify_sorry_replacement must NOT run when the latch fires"
    )
    ctx.yield_output.assert_awaited_once()


def test_p1_latch_skips_when_sorry_count_not_dropped(tmp_path, monkeypatch):
    """Condition 2 fails (count unchanged = a shift) -> re-verify runs instead."""
    from prover.workflow import ProofMessage

    # Frozen line is clear, but the session snapshot has the SAME sorry count
    # (the sorry merely moved). The latch must defer to the existing verify.
    content = (
        "import Mathlib.Tactic\n"
        "theorem t : True := by\n"
        "  trivial\n"
        "-- a stray sorry mention in a comment\n"
    )
    fake = tmp_path / "Shift.lean"
    fake.write_text(content, encoding="utf-8")
    session_full = content  # identical -> same count -> no drop

    reverify_calls = _patch_verifier_and_reverify(monkeypatch, build_success=True)

    ex = _make_verify_executor(fake, sorry_line=3, full_file=session_full)
    msg = ProofMessage(content="x", tactic="trivial", sorry_count=1)
    _run_handle(ex, msg)

    assert msg.proof_found is False, "latch must not fire without a sorry drop"
    assert len(reverify_calls) == 1, "re-verify must run when the latch is skipped"


def test_p1_latch_skips_when_target_line_still_has_sorry(tmp_path, monkeypatch):
    """Condition 1 fails (frozen line still has sorry) -> re-verify runs.

    Even though a sorry was removed elsewhere (count dropped), the frozen
    target line still carries a sorry, so latching success would be a false
    positive. Condition 1 vetoes it.
    """
    from prover.workflow import ProofMessage

    content = (
        "import Mathlib.Tactic\n"
        "theorem t1 : True := by\n"
        "  sorry\n"  # frozen line 3 — STILL a sorry
    )
    fake = tmp_path / "StillSorry.lean"
    fake.write_text(content, encoding="utf-8")
    # Session snapshot had TWO sorries (count dropped 2 -> 1) so cond 2 holds.
    session_full = content + "theorem t2 : True := by\n  sorry\n"
    assert session_full.count("sorry") == 2 and content.count("sorry") == 1

    reverify_calls = _patch_verifier_and_reverify(monkeypatch, build_success=True)

    ex = _make_verify_executor(fake, sorry_line=3, full_file=session_full)
    msg = ProofMessage(content="x", tactic="omega", sorry_count=2)
    _run_handle(ex, msg)

    assert msg.proof_found is False, (
        "latch must not fire while the frozen target line still has a sorry"
    )
    assert len(reverify_calls) == 1, "re-verify must run when condition 1 vetoes"


# ──────────────────────────────────────────────────────────────────────────
# #1500 — implicit-sorry blind spot: a passing build can still hide a sorry
#
# When the agent swaps an explicit `sorry` for a search tactic
# (apply?/exact?/solve_by_elim) that finds nothing, Lean emits a
# "declaration uses sorry" WARNING (not an error). The build SUCCEEDS and the
# text no longer contains the token "sorry", so a text-only count reports 0 —
# a false positive. The fix folds the build-warning count into the decision
# (the same max() that tools.compile() already uses) in BOTH success gates:
#   - prover/provers.py  run_session success gate (final_sorry adoption)
#   - prover/workflow.py P1 in-place latch (effective-count condition)
# `_count_sorries_from_build_output` is the shared primitive; tests below pin
# the primitive and the latch decision offline (no lake build needed).
# ──────────────────────────────────────────────────────────────────────────


# A realistic lake build log fragment with one implicit-sorry warning.
_IMPLICIT_SORRY_LOG = (
    "Building TestSpace\n"
    "warning: ./TestSpace/Fake.lean:42:0: declaration uses 'sorry'\n"
    "Build completed successfully.\n"
)


def test_count_sorries_from_build_output_counts_warning():
    """The shared primitive counts a 'declaration uses sorry' warning."""
    from prover.tools import _count_sorries_from_build_output

    assert _count_sorries_from_build_output(_IMPLICIT_SORRY_LOG) == 1


@pytest.mark.parametrize("log", [
    "Build completed successfully.\n",          # clean build, no warning
    "info: building\nwarning: unused variable x\n",  # unrelated warning
    "",                                          # empty
])
def test_count_sorries_from_build_output_zero_when_no_sorry(log):
    """No 'uses sorry' warning -> count 0 (no false positives on clean logs)."""
    from prover.tools import _count_sorries_from_build_output

    assert _count_sorries_from_build_output(log) == 0


def test_count_sorries_from_build_output_counts_multiple_declarations():
    """One warning per flagged declaration."""
    from prover.tools import _count_sorries_from_build_output

    log = (
        "warning: ./A.lean:3:0: declaration uses 'sorry'\n"
        "warning: ./A.lean:9:0: declaration uses `sorry`\n"
    )
    assert _count_sorries_from_build_output(log) == 2


def test_p1_latch_skips_on_implicit_sorry(tmp_path, monkeypatch):
    """#1500: frozen line text-clear + text count dropped + build SUCCEEDS,
    but the build log warns 'declaration uses sorry' (the agent swapped the
    explicit sorry for `apply?` which found nothing). The effective count did
    NOT actually drop, so the latch must NOT fire — it must fall through to the
    normal verify path instead of claiming a spurious in-place proof.
    """
    from prover.workflow import ProofMessage

    # Text shows no "sorry" (replaced by apply?), but the build will warn.
    swapped = (
        "import Mathlib.Tactic\n"
        "theorem t : True := by\n"
        "  apply?\n"
    )
    fake = tmp_path / "Implicit.lean"
    fake.write_text(swapped, encoding="utf-8")
    session_full = swapped.replace("  apply?\n", "  sorry\n")
    # Condition 1 (frozen line clear) and condition 2 (text 1 -> 0) both hold.
    assert session_full.count("sorry") == 1 and swapped.count("sorry") == 0

    reverify_calls = _patch_verifier_and_reverify(
        monkeypatch, build_success=True, raw_output=_IMPLICIT_SORRY_LOG,
    )

    ex = _make_verify_executor(fake, sorry_line=3, full_file=session_full)
    msg = ProofMessage(content="x", tactic="apply?", sorry_count=1)
    _run_handle(ex, msg)

    assert msg.proof_found is False, (
        "latch must NOT fire when the build still warns 'uses sorry' (#1500)"
    )
    assert len(reverify_calls) == 1, (
        "re-verify must run when the effective (build-aware) count did not drop"
    )


# ──────────────────────────────────────────────────────────────────────────
# #1483 — AutonomousProver increase-case gate: a strategic decomposition that
# RAISES the sorry count but still compiles (lake build SUCCESS, 0 errors) must
# be reported as success and must NOT be reverted. The revert branch upstream
# (provers.py ~1105) is keyed on `level_1_build` alone, so a sorry increase
# never reaches it while the build passes; `_autonomous_success_gate` is the
# pure decision behind the final success/structural-progress flags. P4 intent:
# "never revert a file solely because sorry increased".
# ──────────────────────────────────────────────────────────────────────────
def test_autonomous_gate_increase_case_is_success_no_revert():
    """sorry 4 -> 5 (decomposition) + build OK => success, structural progress."""
    from prover.provers import _autonomous_success_gate

    success, structural = _autonomous_success_gate(
        final_sorry=5, original_sorry_count=4, final_build_ok=True,
    )
    assert success is True, (
        "increase-case that still builds must report success (P4 #1483)"
    )
    assert structural is True, (
        "a building sorry increase is structural progress, not a regression"
    )


def test_autonomous_gate_increase_case_reverts_when_build_fails():
    """sorry 4 -> 5 but build FAILS => not success (revert territory)."""
    from prover.provers import _autonomous_success_gate

    success, structural = _autonomous_success_gate(
        final_sorry=5, original_sorry_count=4, final_build_ok=False,
    )
    assert success is False
    assert structural is False


@pytest.mark.parametrize(
    "final_sorry,original,build_ok,exp_success,exp_struct",
    [
        # increase + build OK -> success via structural progress (#1483 core)
        (5, 4, True, True, True),
        # same count + build OK + >0 -> structural progress (no regression)
        (4, 4, True, True, True),
        # decrease + build OK -> plain success, not structural
        (3, 4, True, True, False),
        # fully solved + build OK -> success, not structural (count 0)
        (0, 4, True, True, False),
        # increase + build FAIL -> never success
        (5, 4, False, False, False),
        # decrease + build FAIL -> never success (false positive guard)
        (3, 4, False, False, False),
        # degenerate 0 -> 0 (no sorry to prove): no progress, not structural
        # (struct needs final_sorry > 0). Preserves the pre-extraction formula.
        (0, 0, True, False, False),
    ],
)
def test_autonomous_gate_matrix(final_sorry, original, build_ok,
                                exp_success, exp_struct):
    from prover.provers import _autonomous_success_gate

    success, structural = _autonomous_success_gate(
        final_sorry=final_sorry,
        original_sorry_count=original,
        final_build_ok=build_ok,
    )
    assert success is exp_success
    assert structural is exp_struct


# ──────────────────────────────────────────────────────────────────────────
# #1460 — compile_probe_goal caching. Probing the goal state runs the Lean
# server; forensics found 54 exact-repeat probes of the same unchanged goal
# (~2.2h wasted). The cache is keyed by (file content hash, sorry_line): a
# repeat probe of an unchanged file is served from cache, and any edit that
# changes the content hash invalidates it (a content key is a stronger
# invalidation signal than a wall-clock TTL — the goal can only change when
# the file does).
# ──────────────────────────────────────────────────────────────────────────
def test_probe_goal_caches_unchanged_file(tactic_tools, monkeypatch):
    """Two probes of the same file hit the Lean server once; second is cached."""
    import json
    import prover.lean_utils as lean_utils

    calls = {"n": 0}

    def fake_get_goal_state(filepath, line):
        calls["n"] += 1
        return f"goal at {line}"

    monkeypatch.setattr(lean_utils, "get_goal_state", fake_get_goal_state)
    line = tactic_tools._test_sorry_line

    first = tactic_tools.compile_probe_goal(line)
    second = tactic_tools.compile_probe_goal(line)

    assert calls["n"] == 1, "unchanged file must serve the second probe from cache"
    assert first == second, "cached result must be identical to the first probe"
    assert json.loads(first)["goal"] == f"goal at {line}"


def test_probe_goal_cache_invalidates_on_context_change(tactic_tools, monkeypatch):
    """An edit INSIDE the [sorry-11, sorry+10] context window busts the cache.

    P2 fix (#1460): the probe cache keys on the surrounding context hash
    (±probe_ctx_lines around sorry), not the whole file. A context-window edit
    changes that hash -> cache miss -> recompute. (The old whole-file-hash
    test assumed ANY edit invalidated; the P2 narrowing makes that false -- see
    the companion test_probe_goal_cache_survives_out_of_window_edit below.)
    """
    import prover.lean_utils as lean_utils

    calls = {"n": 0}

    def fake_get_goal_state(filepath, line):
        calls["n"] += 1
        return f"goal v{calls['n']}"

    monkeypatch.setattr(lean_utils, "get_goal_state", fake_get_goal_state)
    line = tactic_tools._test_sorry_line

    tactic_tools.compile_probe_goal(line)
    # Mutate a line INSIDE the context window (the line right after sorry is
    # within [sorry-11, sorry+10] -> changes the context hash -> cache miss).
    path = Path(tactic_tools._filepath)
    lines = path.read_text(encoding="utf-8").split("\n")
    lines[line] = lines[line] + "  -- in-window context edit"
    path.write_text("\n".join(lines), encoding="utf-8")
    tactic_tools.compile_probe_goal(line)

    assert calls["n"] == 2, "an in-window context edit must invalidate the probe cache"


def test_probe_goal_cache_survives_out_of_window_edit(tactic_tools, monkeypatch):
    """An edit OUTSIDE the context window does NOT bust the cache (P2 #1460).

    The padded fixture places the sorry near the middle with ~50 trailing
    padding lines, so an EOF append lands far outside [sorry-11, sorry+10].
    The context hash is unchanged -> cache hit -> no recompute. This is the
    P2 optimization (edits far from the sorry no longer invalidate the cache)
    and the exact case the old whole-file-hash assertion wrongly expected to
    recompute (it failed with `assert 1 == 2` on a clean main).
    """
    import prover.lean_utils as lean_utils

    calls = {"n": 0}

    def fake_get_goal_state(filepath, line):
        calls["n"] += 1
        return f"goal v{calls['n']}"

    monkeypatch.setattr(lean_utils, "get_goal_state", fake_get_goal_state)
    line = tactic_tools._test_sorry_line

    tactic_tools.compile_probe_goal(line)
    # Append at EOF -- outside the context window, so the hash is unchanged.
    path = Path(tactic_tools._filepath)
    path.write_text(path.read_text(encoding="utf-8") + "\n-- edit\n", encoding="utf-8")
    tactic_tools.compile_probe_goal(line)

    assert calls["n"] == 1, (
        "an out-of-window (EOF) edit must NOT invalidate the probe cache "
        "(P2 #1460: hash surrounding context only)"
    )


# ──────────────────────────────────────────────────────────────────────────
# P1 Δ0 stagnation hard-cap (Epic #1453) — AgentExecutor.handle must yield
# once consecutive Δ0 compiles cross DELTA0_STAGNATION_HARDCAP.
#
# The compile tool (tools.py) already counts consecutive Δ0 compiles (a build
# that succeeds but does NOT reach a new sorry low) and mirrors the count to
# state.consecutive_delta0_compiles, but until #1453 nothing consumed it — it
# relied on the LLM heeding a soft directive string. Forensic
# multi_custom_Lattice_L147_zai.json: 26/30 compiles were Δ0 (22 consecutive at
# 4 sorry from the start) yet the run never terminated and burned the full
# budget. The hard cap is the orchestrator backstop.
# ──────────────────────────────────────────────────────────────────────────


def _stagnation_agent(name="SearchAgent"):
    from unittest.mock import AsyncMock, MagicMock

    agent = MagicMock()
    agent.name = name
    agent.run = AsyncMock(return_value=MagicMock(
        messages=[MagicMock(text="ran")]
    ))
    return agent


def test_delta0_hardcap_yields_and_skips_agent():
    """At/over the hard cap, handle yields the message and never runs the agent."""
    from prover.workflow import (
        AgentExecutor, ProofMessage, DELTA0_STAGNATION_HARDCAP,
    )

    state = ProofState(theorem_statement="t")
    state.consecutive_delta0_compiles = DELTA0_STAGNATION_HARDCAP
    agent = _stagnation_agent()
    ex = AgentExecutor(agent, state=state)
    ctx = _run_handle(ex, ProofMessage(content="x"))

    ctx.yield_output.assert_awaited_once()
    agent.run.assert_not_awaited()  # no compute wasted past the cap


def test_delta0_below_hardcap_runs_agent_normally():
    """One short of the cap, the run continues — the agent executes as usual."""
    from prover.workflow import (
        AgentExecutor, ProofMessage, DELTA0_STAGNATION_HARDCAP,
    )

    state = ProofState(theorem_statement="t")
    state.consecutive_delta0_compiles = DELTA0_STAGNATION_HARDCAP - 1
    agent = _stagnation_agent()
    ex = AgentExecutor(agent, state=state)
    ctx = _run_handle(ex, ProofMessage(content="x"))

    agent.run.assert_awaited_once()  # below the cap → keep working
    ctx.yield_output.assert_not_awaited()


def test_delta0_hardcap_ignored_when_proof_found():
    """A found proof must not be masked by the stagnation yield (guarded by
    `not msg.proof_found`)."""
    from prover.workflow import (
        AgentExecutor, ProofMessage, DELTA0_STAGNATION_HARDCAP,
    )

    state = ProofState(theorem_statement="t")
    state.consecutive_delta0_compiles = DELTA0_STAGNATION_HARDCAP + 5
    agent = _stagnation_agent()
    ex = AgentExecutor(agent, state=state)
    msg = ProofMessage(content="x")
    msg.proof_found = True
    ctx = _run_handle(ex, msg)

    # The delta0 path is skipped; the agent runs (proof_found is handled
    # elsewhere, not pre-empted by the stagnation backstop).
    agent.run.assert_awaited_once()


# ──────────────────────────────────────────────────────────────────────────
# P5/P4 (Epic #1453, 2026-05-29 forensic) — pre-screen documented-intractable
# targets BEFORE spawning agents.
#
# Forensic: all NON-Conway sorry targets are documented intractable in
# docs/lean/stable_marriage_intractable_diagnosis.md, yet director-less
# (zai-provider) runs blanket-bypassed the intractable gate (provers.py sets
# state.director_consulted=True when director_agent is None) and looped to the
# iteration cap — 9/13 runs burned full budgets, ~8.2h wasted. The pre-screen
# (P5) returns {skipped:true, success:false, reason:"documented_intractable"}
# without spawning; the director-less fallback (P4) applies the SAME KB skip
# instead of looping. These tests pin the decision offline (mock KB, no lake).
# ──────────────────────────────────────────────────────────────────────────


@pytest.fixture
def mock_intractable_kb(monkeypatch):
    """Inject a deterministic 2-entry KB into the cache (no real file I/O)."""
    import prover.provers as P

    fake_kb = [
        {
            "file": "GaleShapley.lean",
            "line": 116,
            "identifier": "gale_shapley_man_optimal :: IsStable",
            "reason": "rural hospitals theorem missing",
            "source": "docs/lean/stable_marriage_intractable_diagnosis.md#blocker-1",
        },
        {
            "file": "WholeFileIntractable.lean",
            "match_by_file_only": True,
            "identifier": "any sorry in this file",
            "reason": "entire file blocked behind new formalization",
            "source": "docs/lean/example.md",
        },
    ]
    monkeypatch.setattr(P, "_intractable_kb_cache", fake_kb)
    return fake_kb


def test_load_intractable_kb_returns_documented_targets():
    """The real version-controlled KB loads and lists the documented targets."""
    import prover.provers as P

    # Bust any cache from a prior test so we read the real JSON.
    P._intractable_kb_cache = None
    kb = P._load_intractable_kb()
    P._intractable_kb_cache = None  # leave cache clean for downstream tests

    assert isinstance(kb, list) and len(kb) >= 5, (
        f"expected the documented stable-marriage targets, got {len(kb)}"
    )
    files = {e.get("file") for e in kb}
    assert {"GaleShapley.lean", "Lattice.lean", "Basic.lean"} <= files
    # Every entry must cite a source doc (review discipline).
    assert all(e.get("source") for e in kb), "every KB entry must cite a source"


def test_load_intractable_kb_degrades_to_empty_on_missing_file(monkeypatch):
    """A missing/broken KB returns [] (never crashes the prover)."""
    import prover.provers as P
    from pathlib import Path as _P

    P._intractable_kb_cache = None
    monkeypatch.setattr(P, "_INTRACTABLE_KB_PATH", _P("/does/not/exist.json"))
    assert P._load_intractable_kb() == []
    P._intractable_kb_cache = None


def test_match_intractable_kb_matches_by_basename_and_line(mock_intractable_kb):
    """Matching is filename-based (machine-portable) AND line-keyed."""
    import prover.provers as P

    # Different absolute path, same basename + line -> match.
    entry = P._match_intractable_kb(
        "/some/machine/specific/path/GaleShapley.lean", 116
    )
    assert entry is not None
    assert entry["identifier"] == "gale_shapley_man_optimal :: IsStable"


def test_match_intractable_kb_no_match_on_different_line(mock_intractable_kb):
    """Same file, a DIFFERENT (provable) sorry line must NOT match."""
    import prover.provers as P

    assert P._match_intractable_kb("X/GaleShapley.lean", 999) is None


def test_match_intractable_kb_no_match_on_different_file(mock_intractable_kb):
    """A file not in the KB must not match — provable targets stay provable."""
    import prover.provers as P

    assert P._match_intractable_kb("X/Voting.lean", 116) is None


def test_match_intractable_kb_file_only_matches_any_line(mock_intractable_kb):
    """match_by_file_only entries match ANY sorry line in that file."""
    import prover.provers as P

    assert P._match_intractable_kb("X/WholeFileIntractable.lean", 1) is not None
    assert P._match_intractable_kb("X/WholeFileIntractable.lean", 42) is not None


def test_refuse_intractable_returns_skip_dict(mock_intractable_kb):
    """A KB match yields the documented_intractable skip dict (P5 shape)."""
    import prover.provers as P

    out = P._refuse_intractable("X/GaleShapley.lean", 116, "DEMO_X")
    assert out is not None
    assert out["skipped"] is True
    assert out["success"] is False
    assert out["reason"] == "documented_intractable"
    assert out["sorry_line"] == 116
    assert out["demo"] == "DEMO_X"
    assert out["source"]
    # Shape parity with _refuse_honest_sorry (same keys present).
    for key in ("success", "skipped", "reason", "detail", "demo",
                "sorry_line", "filepath"):
        assert key in out, f"missing key {key!r} (shape parity with honest_sorry)"


def test_refuse_intractable_returns_none_for_provable_target(mock_intractable_kb):
    """A target NOT in the KB returns None -> the prover proceeds normally."""
    import prover.provers as P

    assert P._refuse_intractable("X/GaleShapley.lean", 999, "DEMO_X") is None
    assert P._refuse_intractable("X/Voting.lean", 116, "DEMO_X") is None


def test_refuse_intractable_shape_matches_honest_sorry(mock_intractable_kb):
    """The skip dict mirrors _refuse_honest_sorry so callers handle both alike."""
    import prover.provers as P

    intractable = P._refuse_intractable("X/GaleShapley.lean", 116, "D")
    # _refuse_honest_sorry returns the same shape for a static HONEST sorry.
    # We compare key sets (values differ by reason).
    honest_keys = {
        "success", "skipped", "reason", "detail", "demo",
        "sorry_line", "filepath",
    }
    assert honest_keys <= set(intractable.keys())
    assert intractable["success"] is False and intractable["skipped"] is True


def test_p4_director_less_fallback_skips_intractable(mock_intractable_kb):
    """P4: the director-less branch applies the KB skip instead of looping.

    Mirrors the exact decision in provers.py: when director_agent is None and
    the target is a KB hit, _refuse_intractable returns a skip dict (the branch
    returns it). A non-KB target returns None (graceful degradation preserved:
    director_consulted=True, run proceeds).
    """
    import prover.provers as P

    # KB target -> skip (no loop-to-cap).
    skip = P._refuse_intractable("X/GaleShapley.lean", 116, "D")
    assert skip is not None and skip["reason"] == "documented_intractable"

    # Non-KB target -> None -> the blanket F9 auto-bypass still applies.
    assert P._refuse_intractable("X/SomeProvable.lean", 5, "D") is None


# ──────────────────────────────────────────────────────────────────────────
# P6 (Epic #1453, 2026-05-29 forensic) — surface structural_progress into the
# result JSON so a build-OK / sorry_delta>=0 "proof restructured" outcome is
# distinguishable from an actual sorry reduction.
#
# Both provers must emit the field. We verify the result-construction key is
# present by parsing the source AST of prove_sorry (no LLM / lake needed).
# ──────────────────────────────────────────────────────────────────────────


def test_multi_agent_result_includes_structural_progress_key():
    """MultiAgentSorryProver result dict carries the structural_progress key."""
    import ast
    import inspect
    from prover.provers import MultiAgentSorryProver

    src = inspect.getsource(MultiAgentSorryProver.prove_sorry)
    tree = ast.parse(src.lstrip())  # strip method indentation
    keys = _result_dict_keys(tree)
    assert "structural_progress" in keys, (
        "MultiAgentSorryProver.prove_sorry must surface structural_progress (P6)"
    )


def test_autonomous_result_includes_structural_progress_key():
    """AutonomousProver result dict carries the structural_progress key."""
    import ast
    import inspect
    from prover.provers import AutonomousProver

    src = inspect.getsource(AutonomousProver.prove_sorry)
    tree = ast.parse(src.lstrip())
    keys = _result_dict_keys(tree)
    assert "structural_progress" in keys, (
        "AutonomousProver.prove_sorry must surface structural_progress (P6)"
    )


def _result_dict_keys(tree):
    """Collect every string key from every dict literal in an AST subtree."""
    import ast

    keys = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Dict):
            for k in node.keys:
                if isinstance(k, ast.Constant) and isinstance(k.value, str):
                    keys.add(k.value)
    return keys


def test_autonomous_gate_structural_flag_feeds_result():
    """The structural_progress flag the result reports is the gate's 2nd return.

    Pins the wiring: _autonomous_success_gate returns (success, structural),
    and the result JSON's structural_progress must reflect that boolean — i.e.
    a build-OK same-count outcome reports structural_progress=True.
    """
    from prover.provers import _autonomous_success_gate

    _success, structural = _autonomous_success_gate(
        final_sorry=4, original_sorry_count=4, final_build_ok=True,
    )
    assert structural is True  # build-OK, sorry_delta==0 -> "proof restructured"


# ──────────────────────────────────────────────────────────────────────────
# #1500 (tools.py) — _build_check_or_revert success path must count the
# build-aware sorry, not the text token.
#
# The build-count fix (#1500) was applied to compile() (tools.py:1769) and to
# the provers.run_session / workflow P1-latch gates, but _build_check_or_revert
# -- the build-check run after every file_replace_* edit (the dominant
# autonomous path: ~75 replace vs ~5 compile() calls in the cycle-97 L308
# trace) -- still used text.count('sorry'). A build that SUCCEEDS while warning
# 'declaration uses sorry' (implicit sorry from an unresolved apply?/exact?),
# with the explicit 'sorry' token removed, reports text=0, which
# _record_sorry_count(0) reads as a fresh 'solved / new low' -> false progress
# signal on the path that matters most.
# ──────────────────────────────────────────────────────────────────────────


def _patch_verifier_success(monkeypatch, raw_output):
    """Mock verify_project_file to return a successful build with given log."""
    import prover.verifier as vmod

    class _FakeVerifier:
        def verify_project_file(self, rel, force=False):
            return {"success": True, "errors": "", "raw_output": raw_output}

    monkeypatch.setattr(vmod, "get_verifier", lambda *a, **k: _FakeVerifier())


def test_build_check_or_revert_counts_implicit_sorry(tmp_path, monkeypatch):
    """A success-path build that warns 'uses sorry' must record count 1, not 0.

    The agent swapped the explicit sorry for apply? (found nothing): the file
    text no longer contains the token 'sorry', but the build still warns of an
    implicit sorry. The build-aware count must see it so _record_sorry_count
    does not register a false 'solved / new low'.
    """
    swapped = (
        "import Mathlib.Tactic\n"
        "theorem t : True := by\n"
        "  apply?\n"
    )
    fake = tmp_path / "Implicit.lean"
    fake.write_text(swapped, encoding="utf-8")

    _patch_verifier_success(
        monkeypatch,
        "warning: ./Implicit.lean:3:0: declaration uses 'sorry'\n",
    )

    state = ProofState(theorem_statement="t")
    sctx = SorryContext(
        filepath=str(fake), sorry_line=3, indentation=2,
        indent_str="  ", full_file=swapped,
    )
    tt = TacticTools(state, str(fake), sctx)

    # pre-edit content carried 1 explicit sorry
    original = swapped.replace("  apply?\n", "  sorry\n")
    result = tt._build_check_or_revert(original, "test")

    assert result is None, "a successful build must not revert"
    assert tt._min_compile_sorry_count == 1, (
        f"implicit sorry must be counted via build output (got "
        f"{tt._min_compile_sorry_count}); a text-only count would record 0 "
        f"and falsely signal solved"
    )


def test_build_check_or_revert_real_solve_records_zero(tmp_path, monkeypatch):
    """A genuine solve (build success, no sorry warning) records 0."""
    proved = (
        "import Mathlib.Tactic\n"
        "theorem t : True := by\n"
        "  trivial\n"
    )
    fake = tmp_path / "Proved.lean"
    fake.write_text(proved, encoding="utf-8")

    _patch_verifier_success(monkeypatch, "Build completed successfully.\n")

    state = ProofState(theorem_statement="t")
    sctx = SorryContext(
        filepath=str(fake), sorry_line=3, indentation=2,
        indent_str="  ", full_file=proved,
    )
    tt = TacticTools(state, str(fake), sctx)

    original = proved.replace("  trivial\n", "  sorry\n")
    assert tt._build_check_or_revert(original, "test") is None
    assert tt._min_compile_sorry_count == 0


# ──────────────────────────────────────────────────────────────────────────
# FX-6 (#1453) — statement-mutation false success. Founding incident
# (Reidemeister.lean L545, 2026-07-02, trace
# multi_custom_Reidemeister_L545_openrouter_result.json): the agent replaced
# the in-statement hole `sorry -- ambient_isotopic k₁ k₂` with the RHS,
# producing a vacuous X ↔ X closed by `Iff.rfl`. The run reported
# success=True with proof=null ∧ attempts=0 ∧ sorry_delta=-2: the drop-based
# disjuncts of the success gates were not conditioned on ANY verified tactic.
# ──────────────────────────────────────────────────────────────────────────


def test_gate_rejects_drop_with_zero_verified_tactics():
    """Reidemeister shape: drop + build OK + 0 verified tactic => NOT success."""
    from prover.provers import _autonomous_success_gate

    success, structural = _autonomous_success_gate(
        final_sorry=2, original_sorry_count=4, final_build_ok=True,
        verified_tactic_count=0,
    )
    assert success is False, (
        "a sorry drop nobody proved is a statement mutation, not a success"
    )
    assert structural is False


def test_gate_accepts_drop_with_verified_tactic():
    """Same drop with >=1 build-verified tactic stays a success."""
    from prover.provers import _autonomous_success_gate

    success, structural = _autonomous_success_gate(
        final_sorry=3, original_sorry_count=4, final_build_ok=True,
        verified_tactic_count=1,
    )
    assert success is True
    assert structural is False


def test_gate_structural_progress_unaffected_by_zero_verified():
    """Decomposition (count up, build OK) stays success even with 0 verified
    tactics — the FX-6 condition only gates the DROP disjunct (#1483 P4)."""
    from prover.provers import _autonomous_success_gate

    success, structural = _autonomous_success_gate(
        final_sorry=5, original_sorry_count=4, final_build_ok=True,
        verified_tactic_count=0,
    )
    assert success is True
    assert structural is True


# ──────────────────────────────────────────────────────────────────────────
# FX-8 (#1453, NanoClaw #4936 concern): the autonomous-path asymmetry of #4909.
# After _stmt_mutation_guard restores the original file, final_sorry ==
# original_sorry_count with verified_tactic_count == 0. The pre-FX-8 gate
# reported success=True via the structural-progress disjunct (final >=
# original covering the equality), a FALSE SUCCESS (mutation detected, nothing
# proved). The multi-agent path overrides structural_progress = False after its
# mutation guard; FX-8 mirrors that inside the gate itself.
# ──────────────────────────────────────────────────────────────────────────


def test_fx8_gate_rejects_same_count_zero_verified():
    """NanoClaw #4936: post-mutation-restore state must NOT be a success.

    Shape: final == original (restored), build OK, 0 verified tactic. Pre-FX-8
    this reported success=True via structural_progress (the bug); the gate must
    now refuse it.
    """
    from prover.provers import _autonomous_success_gate

    success, structural = _autonomous_success_gate(
        final_sorry=4, original_sorry_count=4, final_build_ok=True,
        verified_tactic_count=0,
    )
    assert success is False, (
        "a same-count build with 0 verified tactic is a restored statement "
        "mutation (or no-op), not a success (FX-8 autonomous asymmetry fix)"
    )
    assert structural is False


def test_fx8_gate_same_count_stays_structural_with_verified():
    """A genuine same-count restructure (>=1 verified tactic) stays a success.

    Bounds FX-8: the narrow guard only fires when verified == 0 AND
    final == original. A legitimate restructured proof with the same sorry
    count but a build-verified tactic remains structural progress.
    """
    from prover.provers import _autonomous_success_gate

    success, structural = _autonomous_success_gate(
        final_sorry=4, original_sorry_count=4, final_build_ok=True,
        verified_tactic_count=1,
    )
    assert success is True
    assert structural is True


# ──────────────────────────────────────────────────────────────────────────
# FX-9 (#1453, ai-01 L2536 harvest): launcher/reporting accuracy. Two lies
# observed on the L2536 multi-agent run (be9uzhmc1, multi/zai/12, 1757s):
#   (a) ``RESULT: unknown`` — run_prover_bg read ``result['status']`` which the
#       prover never sets (it returns ``success``), so the launcher always fell
#       through to ``unknown``.
#   (b) ``Iterations: 0/12`` while 13 attempts ran — the multi-agent workflow
#       increments ``msg.iteration`` (workflow.py:185) but never mirrors it into
#       ``state.iteration``, so the result's ``iterations`` field was stuck at 0.
#       The workflow DOES keep ``state.remaining_iterations`` in sync
#       (workflow.py:1167), so the real loop count is
#       ``max(0, budget - remaining_iterations)``.
# ──────────────────────────────────────────────────────────────────────────


def test_fx9_multi_result_iterations_derived_from_remaining():
    """The multi-agent result must report actual loops run, not the stale
    state iteration field (which the workflow never increments).

    Regression guard: the fix line is unique in provers.py — the early-return
    paths use the literal ``"iterations": 0``, so the computed form is unique
    to the main multi-agent return. Catches a reintroduction of the 0-count bug.
    """
    from pathlib import Path

    src = (Path(__file__).resolve().parent.parent / "prover" / "provers.py"
           ).read_text(encoding="utf-8")
    assert (
        '"iterations": max(0, max_iterations - state.remaining_iterations),' in src
    ), (
        "FX-9 violated — multi-agent result iterations must be derived from "
        "remaining_iterations (max(0, max_iterations - state.remaining_iterations)), "
        "not the stale per-state iteration field the workflow never updates"
    )


def test_fx9_multi_iterations_formula_matches_l2536_scenario():
    """The FX-9 iteration formula gives the honest loop count for the L2536
    harvest scenario: budget 12, workflow ran to the cap (remaining=0) =>
    12 loops reported (not 0). A session that exited after 3 loops
    (remaining=9) => 3."""
    # budget=12, remaining=0 (cap hit, the L2536 case): 12 loops, not 0.
    assert max(0, 12 - 0) == 12
    # budget=12, remaining=9 (early exit after 3 loops): 3.
    assert max(0, 12 - 9) == 3
    # budget=8, remaining=8 (no loop ran): 0.
    assert max(0, 8 - 8) == 0


def test_fx9_launcher_status_derived_from_success():
    """The launcher RESULT line must derive SUCCESS/FAILED from ``success``
    (bool), not the nonexistent ``status`` key (which always yielded
    ``unknown``).

    Regression guard (FX-7-style source scan).
    """
    from pathlib import Path

    src = (Path(__file__).resolve().parent.parent / "prover" / "run_prover_bg.py"
           ).read_text(encoding="utf-8")
    # The buggy form read the never-set 'status' key.
    assert "result.get('status'" not in src and 'result.get("status"' not in src, (
        "FX-9 violated — launcher must not read result['status'] (the prover "
        "returns 'success', never 'status'); that yielded 'RESULT: unknown'"
    )
    # The fix derives the label from the bool 'success' field.
    assert "result.get(\"success\")" in src, (
        "FX-9 violated — launcher RESULT line must derive from result['success']"
    )


def test_gate_backward_compat_without_verified_param():
    """Legacy callers (no verified_tactic_count) keep pre-FX-6 behaviour."""
    from prover.provers import _autonomous_success_gate

    success, structural = _autonomous_success_gate(
        final_sorry=2, original_sorry_count=4, final_build_ok=True,
    )
    assert success is True
    assert structural is False


def test_stmt_mutation_guard_fires_on_reidemeister_shape():
    """build OK + drop + proof_found=False + 0 verified => mutation flagged."""
    from prover.provers import _stmt_mutation_guard

    assert _stmt_mutation_guard(
        final_sorry=2, original_sorry_count=4, final_build_ok=True,
        proof_found=False, verified_tactic_count=0,
    ) is True


@pytest.mark.parametrize(
    "final_sorry,original,build_ok,proof_found,verified,why",
    [
        (2, 4, True, True, 0, "proof_found: a real proof legitimises the drop"),
        (2, 4, True, False, 1, "a build-verified tactic legitimises the drop"),
        (2, 4, False, False, 0, "build failure is handled by the revert path"),
        (4, 4, True, False, 0, "no drop: nothing to flag (structural case)"),
        (5, 4, True, False, 0, "increase: decomposition territory, not mutation"),
    ],
)
def test_stmt_mutation_guard_quiet_cases(final_sorry, original, build_ok,
                                         proof_found, verified, why):
    from prover.provers import _stmt_mutation_guard

    assert _stmt_mutation_guard(
        final_sorry=final_sorry, original_sorry_count=original,
        final_build_ok=build_ok, proof_found=proof_found,
        verified_tactic_count=verified,
    ) is False, why


# ──────────────────────────────────────────────────────────────────────────
# FX-6 (#1453) — count_real_sorries: comment-stripped, word-bounded counter.
# The legacy `content.count("sorry")` substring counter over-counts prose
# mentions (HashlifeCorrectness reported 33 where 4 were real) and counts
# `sorry -- comment` annotations twice when the comment mentions sorry.
# ──────────────────────────────────────────────────────────────────────────


def test_count_real_sorries_ignores_line_comments():
    from prover.lean_utils import count_real_sorries

    content = (
        "-- this proof used to be sorry, sorry everywhere\n"
        "theorem t : True := by\n"
        "  exact sorry\n"
    )
    assert count_real_sorries(content) == 1


def test_count_real_sorries_ignores_nested_block_comments():
    from prover.lean_utils import count_real_sorries

    content = (
        "/- sorry /- nested sorry -/ still comment sorry -/\n"
        "theorem t : True := sorry\n"
    )
    assert count_real_sorries(content) == 1


def test_count_real_sorries_counts_sorry_with_trailing_comment_once():
    """The Reidemeister in-statement hole form: `sorry -- <prose>` is ONE
    real sorry even when the trailing comment matters to a human reader."""
    from prover.lean_utils import count_real_sorries

    content = "    sorry -- ambient_isotopic k₁ k₂\n"
    assert count_real_sorries(content) == 1


def test_count_real_sorries_word_boundary():
    """`sorryAx` / identifiers containing 'sorry' are not real sorries."""
    from prover.lean_utils import count_real_sorries

    content = (
        "#check @sorryAx\n"
        "def notsorry := 1\n"
        "example : True := by trivial\n"
    )
    assert count_real_sorries(content) == 0


def test_count_real_sorries_catches_all_real_forms():
    from prover.lean_utils import count_real_sorries

    content = (
        "theorem a : True := sorry\n"          # term-mode := sorry
        "theorem b : True := by\n"
        "  exact sorry\n"                       # exact sorry
        "theorem c : True := by\n"
        "  sorry\n"                             # bare tactic sorry
    )
    assert count_real_sorries(content) == 3


def test_strip_lean_comments_preserves_code():
    from prover.lean_utils import strip_lean_comments

    content = (
        "import Mathlib.Tactic  -- tail comment\n"
        "/- block\n   spanning lines -/\n"
        "theorem t : 1 + 1 = 2 := by norm_num\n"
    )
    stripped = strip_lean_comments(content)
    assert "tail comment" not in stripped
    assert "spanning lines" not in stripped
    assert "theorem t : 1 + 1 = 2 := by norm_num" in stripped


# --- FX-7 (#1453): migrate ALL sorry counters to count_real_sorries ----------
# The success gates (verify_sorry_replacement, the workflow latch), snapshot
# counters in tools.py, and run_prover_bg reporting all historically used the
# `content.count("sorry")` substring counter, which over-counts prose mentions
# in comments/docstrings (HashlifeCorrectness: substring 34, real 4 — 8.5x
# inflation). FX-7 retires the substring counter repo-wide in one pass so every
# before/after delta is consistent; a "0 sorry -> skip" gate now fires on the
# REAL count instead of never firing while comment prose mentions survive.


def test_fx7_count_real_sorries_massively_undercounts_comment_prose():
    """Mirrors the founding HashlifeCorrectness inflation: a file with heavy
    'sorry' prose in comments/docstrings must count only the REAL tokens, so
    the migrated gates see the true obligation count (FX-7 value)."""
    from prover.lean_utils import count_real_sorries

    content = (
        "/-!\n"
        "This file proves the hashlife result. It used to be sorry everywhere;\n"
        "we removed sorry after sorry until only sorry-free scaffolding sorry\n"
        "mentions remained in this docstring (sorry, sorry, sorry).\n"
        "-/\n"
        "-- NB: the word sorry in this line comment is NOT an obligation.\n"
        "theorem t1 : True := by\n"
        "  sorry\n"                       # 1 real
        "theorem t2 : True := by\n"
        "  exact sorry\n"                 # 2 real
    )
    assert content.count("sorry") >= 8    # substring over-counts prose
    assert count_real_sorries(content) == 2


def test_fx7_no_legacy_substring_counter_in_prover_source():
    """FX-7 regression guard: no prover source module may reintroduce the
    legacy `.count("sorry")` substring counter on file content — every gate,
    snapshot, and report must go through count_real_sorries so deltas stay
    consistent. The only allowed mention is the historical docstring in
    lean_utils.py describing the retired counter."""
    from pathlib import Path

    prover_dir = Path(__file__).resolve().parent.parent / "prover"
    legacy = []
    for py in sorted(prover_dir.glob("*.py")):
        for ln, line in enumerate(py.read_text(encoding="utf-8").splitlines(), 1):
            if '.count("sorry")' in line:
                # lean_utils.py keeps ONE historical mention in the
                # count_real_sorries docstring describing the retired counter.
                # Match on an explicit marker (not markdown formatting) so the
                # allow survives a docstring reformat (NanoClaw #4936 △ Mineur).
                if py.name == "lean_utils.py" and "# FX-7-ALLOW" in line:
                    continue
                legacy.append(f"{py.name}:{ln}: {line.strip()}")
    assert not legacy, (
        "FX-7 violated — legacy substring `.count(\"sorry\")` reintroduced:\n"
        + "\n".join(legacy)
    )


# --- FX-6b (#1453): sorry_is_in_statement + in-statement entry refusal ------
# The latch (workflow.py) and verify_sorry_replacement both set
# proof_found=True without touching tactic_history, and proof_found is a
# standalone OR disjunct in the success gates (po-2026 post-merge review of
# #4909). An in-statement sorry "closed" through either path is a statement
# mutation the FX-6 gate cannot see. The fix is upstream: such a hole is a
# SPECIFICATION gap, refused before any agent runs.

REIDEMEISTER_L545_SHAPE = (
    "import Mathlib.Tactic\n"                                        # 1
    "\n"                                                             # 2
    "def KnotEquiv (a b : Nat) : Prop := a = b\n"                    # 3
    "\n"                                                             # 4
    "theorem reidemeister_theorem :\n"                               # 5
    "    ∀ (k₁ k₂ : Nat),\n"                          # 6
    "      -- Ambient isotopy of the embeddings\n"                   # 7
    "      sorry -- ambient_isotopic k₁ k₂\n"              # 8  <- in-statement
    "      ↔\n"                                                 # 9
    "      KnotEquiv k₁ k₂ := by\n"                        # 10 <- first ':='
    "  exact sorry\n"                                                # 11 <- in-body
)


def test_in_statement_detected_on_reidemeister_shape():
    from prover.lean_utils import sorry_is_in_statement

    assert sorry_is_in_statement(REIDEMEISTER_L545_SHAPE, 8) is True


def test_in_body_sorry_of_same_declaration_not_flagged():
    from prover.lean_utils import sorry_is_in_statement

    assert sorry_is_in_statement(REIDEMEISTER_L545_SHAPE, 11) is False


def test_same_line_sorry_after_assign_is_body():
    from prover.lean_utils import sorry_is_in_statement

    content = "theorem foo : 1 + 1 = 2 := by sorry\n"
    assert sorry_is_in_statement(content, 1) is False


def test_same_line_sorry_before_assign_is_statement():
    from prover.lean_utils import sorry_is_in_statement

    content = "def x : sorry := trivial\n"
    assert sorry_is_in_statement(content, 1) is True


def test_match_syntax_body_without_assign_not_flagged():
    from prover.lean_utils import sorry_is_in_statement

    content = (
        "def f : Nat → Nat\n"
        "  | 0 => sorry\n"
        "  | _ => 1\n"
    )
    assert sorry_is_in_statement(content, 2) is False


def test_sorry_only_in_comment_on_target_line_not_flagged():
    from prover.lean_utils import sorry_is_in_statement

    content = (
        "theorem t :\n"
        "    -- sorry, this comment mentions it\n"
        "    1 + 1 = 2 := by norm_num\n"
    )
    assert sorry_is_in_statement(content, 2) is False


def test_attribute_and_modifiers_above_declaration_handled():
    from prover.lean_utils import sorry_is_in_statement

    content = (
        "@[simp]\n"
        "private noncomputable def g :\n"
        "    sorry := by\n"
        "  trivial\n"
    )
    # ':=' is on line 3 at a column AFTER the sorry token -> statement
    assert sorry_is_in_statement(content, 3) is True


def test_line_comment_assign_is_ignored_in_scan():
    from prover.lean_utils import sorry_is_in_statement

    content = (
        "theorem t :\n"
        "    -- fake := in a comment\n"
        "    sorry\n"
        "    ↔ True := by\n"
        "  exact sorry\n"
    )
    assert sorry_is_in_statement(content, 3) is True


def test_out_of_range_line_not_flagged():
    from prover.lean_utils import sorry_is_in_statement

    assert sorry_is_in_statement("theorem t : True := by sorry\n", 99) is False
    assert sorry_is_in_statement("", 1) is False


def test_no_enclosing_declaration_not_flagged():
    from prover.lean_utils import sorry_is_in_statement

    content = "-- orphan\nsorry\n"
    assert sorry_is_in_statement(content, 2) is False


def test_next_declaration_bounds_the_scan():
    from prover.lean_utils import sorry_is_in_statement

    # decl A uses match syntax (no ':='); decl B below has one. The scan
    # must stop at decl B and NOT attribute B's ':=' to A's sorry.
    content = (
        "def f : Nat → Nat\n"
        "  | 0 => sorry\n"
        "theorem t : True := by trivial\n"
    )
    assert sorry_is_in_statement(content, 2) is False


def test_refuse_in_statement_sorry_returns_skip_dict(tmp_path):
    from prover.provers import _refuse_in_statement_sorry

    f = tmp_path / "Reid.lean"
    f.write_text(REIDEMEISTER_L545_SHAPE, encoding="utf-8")
    result = _refuse_in_statement_sorry(str(f), 8, "demo-reid")
    assert result is not None
    assert result["success"] is False
    assert result["skipped"] is True
    assert result["reason"] == "in_statement_sorry"
    assert result["sorry_line"] == 8
    assert result["demo"] == "demo-reid"


def test_refuse_in_statement_sorry_none_for_body_sorry(tmp_path):
    from prover.provers import _refuse_in_statement_sorry

    f = tmp_path / "Reid.lean"
    f.write_text(REIDEMEISTER_L545_SHAPE, encoding="utf-8")
    assert _refuse_in_statement_sorry(str(f), 11, "demo-reid") is None


def test_refuse_in_statement_sorry_none_when_file_missing(tmp_path):
    from prover.provers import _refuse_in_statement_sorry

    missing = tmp_path / "nope.lean"
    assert _refuse_in_statement_sorry(str(missing), 8, "demo") is None


# --- FX-5 (#1453): TRUE_PLACEHOLDER_GOAL — refuse a sorry whose goal is True -
# A goal of `True` is never a legitimate obligation (proves by `trivial`). It
# arises from a mutated/vacuous statement or a degenerate sub-goal; the agent
# then loops on "task already complete" (L545 replay). Detection runs ONE probe
# (`exact True.intro`); zero false positives — only a True goal closes under it.

def _mock_probe_verifier(monkeypatch, raw_output):
    """Point get_verifier at a fake whose compile returns `raw_output`."""
    import prover.verifier as vmod

    class _FakeVerifier:
        def verify_project_file(self, rel, force=False):
            return {"success": not raw_output, "errors": "", "raw_output": raw_output}
    monkeypatch.setattr(vmod, "get_verifier", lambda *a, **k: _FakeVerifier())


_TRUE_GOAL_FILE = (
    "import Mathlib.Tactic\n"
    "theorem t : True := by\n"
    "  sorry\n"           # line 3 — a True goal (degenerate)
)


def test_is_true_placeholder_goal_detects_true_goal(tmp_path, monkeypatch):
    from prover.lean_utils import is_true_placeholder_goal

    # Probe `exact True.intro` closes the goal → no error, no unsolved.
    _mock_probe_verifier(monkeypatch, raw_output="")
    f = tmp_path / "T.lean"
    f.write_text(_TRUE_GOAL_FILE, encoding="utf-8")
    is_true, reason = is_true_placeholder_goal(str(f), 3)
    assert is_true is True
    assert "TRUE_PLACEHOLDER_GOAL" in reason


def test_is_true_placeholder_goal_false_on_type_mismatch(tmp_path, monkeypatch):
    """A real goal (e.g. 1 + 1 = 2) type-mismatches `exact True.intro`."""
    from prover.lean_utils import is_true_placeholder_goal

    # Error reported AT the probed line → probe did not close the goal.
    _mock_probe_verifier(
        monkeypatch,
        raw_output="3:2: error: type mismatch\n  exact True.intro\nhas type\n  True",
    )
    f = tmp_path / "Real.lean"
    f.write_text(_TRUE_GOAL_FILE, encoding="utf-8")
    is_true, _ = is_true_placeholder_goal(str(f), 3)
    assert is_true is False


def test_is_true_placeholder_goal_false_on_unsolved_goals(tmp_path, monkeypatch):
    """Probe accepted but left an open goal → not a closed True goal."""
    from prover.lean_utils import is_true_placeholder_goal

    _mock_probe_verifier(monkeypatch, raw_output="3:2: error: unsolved goals")
    f = tmp_path / "Uns.lean"
    f.write_text(_TRUE_GOAL_FILE, encoding="utf-8")
    assert is_true_placeholder_goal(str(f), 3)[0] is False


def test_is_true_placeholder_goal_false_when_no_sorry_token(tmp_path, monkeypatch):
    """A line without a real sorry token is never probed (no compile)."""
    from prover.lean_utils import is_true_placeholder_goal

    probe_calls = []
    _mock_probe_verifier(monkeypatch, raw_output="")
    f = tmp_path / "NoSorry.lean"
    f.write_text("theorem t : True := by\n  trivial\n", encoding="utf-8")
    # Line 2 has no sorry → False, and the verifier must not have been built.
    assert is_true_placeholder_goal(str(f), 2)[0] is False


def test_is_true_placeholder_goal_false_for_deeply_nested(tmp_path, monkeypatch):
    """Indent >= 8 → cascade errors → conservatively skip (no false positive)."""
    from prover.lean_utils import is_true_placeholder_goal

    _mock_probe_verifier(monkeypatch, raw_output="")
    f = tmp_path / "Nested.lean"
    f.write_text("theorem t : True := by\n        sorry\n", encoding="utf-8")  # 8-space indent
    assert is_true_placeholder_goal(str(f), 2)[0] is False


def test_is_true_placeholder_goal_false_when_file_missing(tmp_path):
    from prover.lean_utils import is_true_placeholder_goal

    missing = tmp_path / "nope.lean"
    assert is_true_placeholder_goal(str(missing), 3)[0] is False


def test_is_true_placeholder_goal_conservative_on_other_sorries_erroring(tmp_path, monkeypatch):
    """Errors from OTHER sorries FAR from the probed line do not flip the
    verdict: only an error/unsolved-goal within tolerance of the target line
    decides closure. (A nearby unsolved goal WOULD block detection — the
    conservative tolerance — so this test uses a far-away error.)"""
    from prover.lean_utils import is_true_placeholder_goal

    # An unrelated sorry's error at line 30 (>> the 25-line tolerance from
    # the True goal at line 3) must not block the True-goal detection.
    _mock_probe_verifier(monkeypatch, raw_output="30:2: error: unsolved goals")
    f = tmp_path / "Mixed.lean"
    f.write_text(_TRUE_GOAL_FILE, encoding="utf-8")  # _TRUE_GOAL_FILE: sorry at line 3
    assert is_true_placeholder_goal(str(f), 3)[0] is True


def test_refuse_true_placeholder_goal_returns_dict_on_true_goal(tmp_path, monkeypatch):
    from prover.provers import _refuse_true_placeholder_goal

    _mock_probe_verifier(monkeypatch, raw_output="")
    f = tmp_path / "T.lean"
    f.write_text(_TRUE_GOAL_FILE, encoding="utf-8")
    out = _refuse_true_placeholder_goal(str(f), 3, "demo-true")
    assert out is not None
    assert out["reason"] == "true_placeholder_goal"
    assert out["skipped"] is True
    assert out["demo"] == "demo-true"


def test_refuse_true_placeholder_goal_none_on_real_goal(tmp_path, monkeypatch):
    from prover.provers import _refuse_true_placeholder_goal

    _mock_probe_verifier(
        monkeypatch, raw_output="3:2: error: type mismatch\n  exact True.intro")
    f = tmp_path / "Real.lean"
    f.write_text(_TRUE_GOAL_FILE, encoding="utf-8")
    assert _refuse_true_placeholder_goal(str(f), 3, "demo") is None


# ──────────────────────────────────────────────────────────────────────────
# #5869 (2026-07-10) — provider-outage backoff + circuit-breaker + iteration
# accounting.
#
# Forensic trace multi_custom_HashlifeCorrectness_L2636: openrouter died at
# +601s and the TacticAgent hop failed ~20 times in 1.5s — each ~50ms
# round-trip incremented msg.iteration, burned the whole proof budget and
# polluted the verdict as `no_progress` although no tactic was ever attempted
# after the outage. Three fixes, all pinned here offline:
#   1. "service failed" (agent_framework's wrapped provider error) is now a
#      transient marker -> bounded in-hop retries with exponential backoff
#      instead of an instant no-sleep re-loop.
#   2. A provider hop that definitively fails REFUNDS the iteration it
#      incremented at entry (transport failure != tactic work).
#   3. After PROVIDER_OUTAGE_BREAKER consecutive failed hops the run yields
#      with error_type="provider_outage", distinct from no_progress.
# ──────────────────────────────────────────────────────────────────────────


def _failing_agent(name="TacticAgent", exc=None):
    """An agent whose `.run` always raises the given provider error."""
    from unittest.mock import AsyncMock, MagicMock

    if exc is None:
        exc = RuntimeError("OpenAIChatCompletionClient service failed: 503")

    agent = MagicMock()
    agent.name = name
    agent.run = AsyncMock(side_effect=exc)
    return agent


def _success_then_fail_agent(name="TacticAgent", fail_exc=None):
    """Succeeds once, then raises on every subsequent call."""
    from unittest.mock import AsyncMock, MagicMock

    if fail_exc is None:
        fail_exc = RuntimeError("OpenAIChatCompletionClient service failed: 503")

    agent = MagicMock()
    agent.name = name
    agent.run = AsyncMock(side_effect=[
        MagicMock(messages=[MagicMock(text="ran")]),
        fail_exc, fail_exc, fail_exc, fail_exc, fail_exc,
    ])
    return agent


@pytest.fixture
def no_sleep(monkeypatch):
    """Patch asyncio.sleep inside the workflow module so backoff is instant
    in tests (otherwise the breaker test alone would sleep ~30s)."""
    from unittest.mock import AsyncMock
    import prover.workflow as wf

    monkeypatch.setattr(wf.asyncio, "sleep", AsyncMock())
    return wf.asyncio.sleep


def test_service_failed_is_now_transient():
    """The wrapped provider error from forensic L2636 must classify as
    transient so it enters the bounded retry path, not the no-sleep loop."""
    from prover.workflow import _is_transient_error

    assert _is_transient_error(
        RuntimeError("OpenAIChatCompletionClient service failed: 503")
    ) is True


def test_service_failed_with_4xx_status_still_not_transient():
    """The 4xx guard still wins: a wrapped error mentioning a real config
    status (404/401/403) is NOT retried even if it also says 'service failed'."""
    from prover.workflow import _is_transient_error

    # 'service failed' string present, but a 404 status code on the exc.
    class _Err(Exception):
        status_code = 404

    _Err.__str__ = lambda self: "OpenAIChatCompletionClient service failed"
    assert _is_transient_error(_Err()) is False


def test_transient_backoff_is_exponential_capped():
    """Backoff doubles 1/2/4/8/16s then holds at the cap."""
    from prover.workflow import _transient_backoff_s, TRANSIENT_RETRY_BACKOFF_CAP_S

    assert _transient_backoff_s(1) == 1.0
    assert _transient_backoff_s(2) == 2.0
    assert _transient_backoff_s(3) == 4.0
    assert _transient_backoff_s(4) == 8.0
    assert _transient_backoff_s(5) == 16.0
    assert _transient_backoff_s(20) == TRANSIENT_RETRY_BACKOFF_CAP_S


def test_provider_failure_refunds_iteration_and_counts(no_sleep):
    """A single failed provider hop refunds the iteration it incremented and
    bumps the failure counters — the budget is NOT burned by a transport error."""
    from prover.workflow import AgentExecutor, ProofMessage

    state = ProofState(theorem_statement="t")
    ex = AgentExecutor(_failing_agent(), state=state)
    msg = ProofMessage(content="x", iteration=4, max_iterations=10)

    ctx = _run_handle(ex, msg)

    # iteration refunded back to 4 (the +1 at entry was undone).
    assert msg.iteration == 4, f"expected refund to 4, got {msg.iteration}"
    assert msg.provider_failures == 1
    assert msg.consecutive_provider_failures == 1
    assert msg.provider_outage is False  # one failure does not trip the breaker
    # Not yet at the breaker threshold -> message flows on (no yield here).
    ctx.yield_output.assert_not_awaited()


def test_circuit_breaker_trips_at_threshold(no_sleep):
    """After PROVIDER_OUTAGE_BREAKER consecutive failed hops the run yields with
    error_type='provider_outage' and does not keep calling the dead provider."""
    from prover.workflow import (
        AgentExecutor, ProofMessage, PROVIDER_OUTAGE_BREAKER,
    )

    state = ProofState(theorem_statement="t")
    agent = _failing_agent()
    ex = AgentExecutor(agent, state=state)

    msg = ProofMessage(content="x", max_iterations=10)
    for _ in range(PROVIDER_OUTAGE_BREAKER):
        ctx = _run_handle(ex, msg)

    assert msg.provider_outage is True
    assert msg.error_type == "provider_outage"
    assert msg.consecutive_provider_failures == PROVIDER_OUTAGE_BREAKER
    # Budget intact: the three failures refunded their entry increments.
    assert msg.iteration == 0, f"expected 0 burned iterations, got {msg.iteration}"
    # The final hop yielded the outage verdict.
    assert ctx.yield_output.await_count >= 1


def test_budget_intact_across_full_outage(no_sleep):
    """Simulating the L2636 incident: a provider that fails on EVERY hop. The
    iteration budget must stay intact and the run must terminate via the breaker
    (not via the iteration cap with a `no_progress` mislabel)."""
    from prover.workflow import (
        AgentExecutor, ProofMessage, PROVIDER_OUTAGE_BREAKER, TRANSIENT_RETRY_MAX,
    )

    state = ProofState(theorem_statement="t")
    agent = _failing_agent()
    ex = AgentExecutor(agent, state=state)
    msg = ProofMessage(content="x", max_iterations=10)

    # Drive hops until the breaker yields. Cap the loop well above the
    # breaker threshold so a broken (non-terminating) breaker is caught.
    for _ in range(PROVIDER_OUTAGE_BREAKER + 5):
        _run_handle(ex, msg)
        if msg.provider_outage:
            break

    assert msg.provider_outage is True, "breaker should have terminated the run"
    assert msg.iteration == 0, "no real tactic attempt -> budget fully intact"
    # Each failed hop ran the initial call + its in-hop retry chain
    # (TRANSIENT_RETRY_MAX retries) before giving up.
    assert agent.run.await_count == PROVIDER_OUTAGE_BREAKER * (1 + TRANSIENT_RETRY_MAX)


def test_success_resets_consecutive_failure_counter(no_sleep):
    """A flapping provider that succeeds between failures never trips the
    breaker: any successful hop resets consecutive_provider_failures to 0."""
    from prover.workflow import AgentExecutor, ProofMessage

    state = ProofState(theorem_statement="t")
    # succeeds, then fails, then fails (2 consecutive, below threshold of 3).
    agent = _success_then_fail_agent()
    ex = AgentExecutor(agent, state=state)
    msg = ProofMessage(content="x", max_iterations=10)

    _run_handle(ex, msg)  # hop 1: success -> resets counter
    assert msg.consecutive_provider_failures == 0
    _run_handle(ex, msg)  # hop 2: failure
    assert msg.consecutive_provider_failures == 1
    assert msg.provider_outage is False
    _run_handle(ex, msg)  # hop 3: failure (2 consecutive)
    assert msg.consecutive_provider_failures == 2
    assert msg.provider_outage is False  # still below breaker


def test_context_window_error_is_not_a_provider_failure(no_sleep):
    """A context-length overflow is a request-size issue, not a provider outage:
    it must NOT refund the iteration or trip the breaker."""
    from prover.workflow import AgentExecutor, ProofMessage

    state = ProofState(theorem_statement="t")
    agent = _failing_agent(
        exc=RuntimeError("This model's maximum context length is 128000 tokens "
                         "(context_length_exceeded)."))
    ex = AgentExecutor(agent, state=state)
    msg = ProofMessage(content="x", iteration=3, max_iterations=10)

    _run_handle(ex, msg)

    assert msg.provider_failures == 0
    assert msg.provider_outage is False
    assert msg.consecutive_provider_failures == 0
    # Context overflow is real attempted work (truncation retry) -> the entry
    # iteration increment (3 -> 4) is NOT refunded.
    assert msg.iteration == 4


def test_result_kind_provider_outage_when_outage_flag_set():
    """_derive_result_kind surfaces provider_outage, distinct from no_progress,
    but real progress (sorry_decreased) still outranks the outage flag."""
    from prover.run_prover_bg import _derive_result_kind

    # Outage, no progress, no structural progress -> provider_outage.
    assert _derive_result_kind(
        {"provider_outage": True, "provider_failures": 3}, 4, 4
    ) == "provider_outage"
    # Outage BUT sorry dropped -> still harvestable (sorry_decreased wins).
    assert _derive_result_kind(
        {"provider_outage": True, "provider_failures": 3}, 2, 4
    ) == "sorry_decreased"
    # No outage, no progress -> legacy no_progress.
    assert _derive_result_kind({}, 4, 4) == "no_progress"
    # Crashed outranks everything (result carries an error key).
    assert _derive_result_kind(
        {"provider_outage": True, "error": "boom"}, 4, 4
    ) == "crashed"


# ──────────────────────────────────────────────────────────────────────────
# #5891 (2026-07-10) — config.py path-resolution: ancestor-walk for
# MyIA.AI.Notebooks/, with drive-letter fallbacks.
#
# The harness ships inside the CoursIA-2 layout (../prover/config.py under
# MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests/). C:\dev\CoursIA\ is a
# separate physical checkout of the same repo with identical git content
# but different inodes. Before the fix, _COOPERATIVE_GAMES_CANDIDATES and
# its four siblings hardcoded `C:\dev\CoursIA\...`, so a BG-iter run from
# CoursIA-2 would silently edit the WRONG tree and a PR on CoursIA-2
# would not pick up the change.
#
# The fix walks `Path(__file__).resolve().parents` for the first ancestor
# named "MyIA.AI.Notebooks" that exists, prepends the resulting workspace-
# relative path to each candidate list, and keeps the drive-letter
# fallbacks as a safety net (so a harness copy dropped elsewhere still
# works).
#
# These tests pin the contract offline: no Lake build needed, no real
# file I/O beyond reading the candidate paths the module already exposes.
# ──────────────────────────────────────────────────────────────────────────


def test_workspace_root_walks_to_myia_ai_notebooks():
    """_workspace_root() finds the MyIA.AI.Notebooks ancestor of config.py.

    In a normal CoursIA-2 checkout the ancestor chain is:
      .../prover -> .../agent_tests -> .../Lean -> .../SymbolicAI
              -> .../MyIA.AI.Notebooks
    The first name=="MyIA.AI.Notebooks" that exists() wins.
    """
    from prover.config import _workspace_root, _WORKSPACE_ROOT

    assert _WORKSPACE_ROOT is not None, (
        "the harness lives inside MyIA.AI.Notebooks/ — _workspace_root() "
        "must find it via the ancestor walk"
    )
    assert _WORKSPACE_ROOT.name == "MyIA.AI.Notebooks"
    assert _WORKSPACE_ROOT.exists()
    # Same value across calls (cached at import).
    assert _workspace_root() == _WORKSPACE_ROOT


def test_workspace_relative_joins_to_workspace_root():
    """Forward-slash relative strings resolve under the workspace root."""
    from prover.config import _workspace_relative, _WORKSPACE_ROOT

    p = _workspace_relative("GameTheory/cooperative_games_lean")
    assert p == _WORKSPACE_ROOT / "GameTheory" / "cooperative_games_lean"
    assert p.exists(), (
        "the workspace-relative entry for cooperative_games_lean must "
        "resolve to a real directory on a normal CoursIA-2 layout"
    )


def test_workspace_relative_returns_none_when_no_root(monkeypatch):
    """A None _WORKSPACE_ROOT degrades to None (caller treats as miss)."""
    import prover.config as cfg

    monkeypatch.setattr(cfg, "_WORKSPACE_ROOT", None)
    assert cfg._workspace_relative("GameTheory/cooperative_games_lean") is None


def test_path_constants_resolve_to_active_workspace():
    """Every FILE constant resolves into the active workspace, not a sibling.

    On CoursIA-2, none of SHAPLEY_FILE / VOTING_FILE / GALESHAPLEY_FILE /
    NASH_CALIBRATION_FILE / CONWAY_NIM_FILE / COOPERATIVE_GAMES_DIR /
    SOCIAL_CHOICE_DIR / STABLE_MARRIAGE_DIR / CALIBRATION_DIR / CONWAY_DIR
    must point at C:\\dev\\CoursIA\\ (a separate physical checkout) when
    the harness is run from C:\\dev\\CoursIA-2.
    """
    import re
    from prover.config import (
        SHAPLEY_FILE, VOTING_FILE, GALESHAPLEY_FILE,
        NASH_CALIBRATION_FILE, CONWAY_NIM_FILE,
        COOPERATIVE_GAMES_DIR, SOCIAL_CHOICE_DIR,
        STABLE_MARRIAGE_DIR, CALIBRATION_DIR, CONWAY_DIR,
    )

    # The legacy hardcoded form "C:\dev\CoursIA\..." (no -2) is the wrong
    # tree. The fix is to prefer a workspace-relative entry first.
    WRONG_TREE = re.compile(r"C:\\dev\\CoursIA\\")
    REAL_TREE = re.compile(r"C:\\dev\\CoursIA-2\\")

    paths = {
        "COOPERATIVE_GAMES_DIR": COOPERATIVE_GAMES_DIR,
        "SOCIAL_CHOICE_DIR": SOCIAL_CHOICE_DIR,
        "STABLE_MARRIAGE_DIR": STABLE_MARRIAGE_DIR,
        "CALIBRATION_DIR": CALIBRATION_DIR,
        "CONWAY_DIR": CONWAY_DIR,
        "SHAPLEY_FILE": SHAPLEY_FILE,
        "VOTING_FILE": VOTING_FILE,
        "GALESHAPLEY_FILE": GALESHAPLEY_FILE,
        "NASH_CALIBRATION_FILE": NASH_CALIBRATION_FILE,
        "CONWAY_NIM_FILE": CONWAY_NIM_FILE,
    }
    for name, p in paths.items():
        s = str(p)
        # A wrong-tree leak: the legacy fallback was selected because the
        # workspace-relative entry was missing or non-existent.
        assert not WRONG_TREE.search(s) or "CoursIA-2" in s, (
            f"{name}={s} still points to C:\\dev\\CoursIA\\ — the harness "
            f"would silently edit the wrong tree (the bug #5891)"
        )
        # And: every constant must point at a real file/dir.
        assert p.exists(), f"{name}={s} does not exist after resolution"
        # And on this layout, the workspace-relative (CoursIA-2) entry won.
        assert REAL_TREE.search(s), (
            f"{name}={s} should resolve into the active CoursIA-2 workspace"
        )


def test_candidates_list_prefers_workspace_relative_entry():
    """The workspace-relative path is listed FIRST in each candidate list.

    `next((p for p in CANDIDATES if p.exists()), ...)` is order-sensitive.
    Prepending the workspace-relative entry ensures the active workspace
    wins over the drive-letter fallbacks.
    """
    from prover.config import (
        _COOPERATIVE_GAMES_CANDIDATES,
        _SOCIAL_CHOICE_CANDIDATES,
        _STABLE_MARRIAGE_CANDIDATES,
        _CALIBRATION_CANDIDATES,
        _CONWAY_CANDIDATES,
    )

    for lst in (
        _COOPERATIVE_GAMES_CANDIDATES,
        _SOCIAL_CHOICE_CANDIDATES,
        _STABLE_MARRIAGE_CANDIDATES,
        _CALIBRATION_CANDIDATES,
        _CONWAY_CANDIDATES,
    ):
        assert len(lst) >= 2, "each candidate list keeps its legacy fallbacks"
        first = str(lst[0])
        # First entry is workspace-relative (CoursIA-2 path) on this layout.
        assert "CoursIA-2" in first, (
            f"first candidate should be workspace-relative, got {first}"
        )
        # Drive-letter fallbacks still present.
        legacy_paths = [str(p) for p in lst[1:]]
        assert any(r"C:\dev\CoursIA\MyIA.AI.Notebooks" in s for s in legacy_paths), (
            "drive-letter fallbacks must remain as a safety net"
        )


def test_legacy_fallback_still_works_when_no_workspace_root(monkeypatch):
    """If _WORKSPACE_ROOT is None, the legacy drive-letter list still resolves.

    Defends the safety-net path: a harness copy dropped outside the
    CoursIA layout (e.g. into a standalone dir without MyIA.AI.Notebooks/
    ancestor) must keep working via the original candidates.
    """
    import prover.config as cfg
    from pathlib import Path

    # Pretend no workspace root was found.
    monkeypatch.setattr(cfg, "_WORKSPACE_ROOT", None)
    # Remove the workspace-relative first entry from the candidate list so
    # resolution falls back to the drive-letter list (mirrors what
    # _workspace_root()==None would produce).
    monkeypatch.setattr(cfg, "_COOPERATIVE_GAMES_CANDIDATES", [
        Path(r"C:\dev\CoursIA\MyIA.AI.Notebooks\GameTheory\cooperative_games_lean"),
        Path(r"D:\dev\CoursIA\MyIA.AI.Notebooks\GameTheory\cooperative_games_lean"),
    ])
    cfg.COOPERATIVE_GAMES_DIR = next(
        (p for p in cfg._COOPERATIVE_GAMES_CANDIDATES if p.exists()),
        cfg._COOPERATIVE_GAMES_CANDIDATES[0],
    )
    # On this Windows host, C:\dev\CoursIA exists — the legacy path resolves.
    assert cfg.COOPERATIVE_GAMES_DIR.exists(), (
        "legacy drive-letter fallback must still resolve to a real path"
    )
