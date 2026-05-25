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


def test_probe_goal_cache_invalidates_on_file_change(tactic_tools, monkeypatch):
    """Editing the file changes its content hash, so the next probe recomputes."""
    import prover.lean_utils as lean_utils

    calls = {"n": 0}

    def fake_get_goal_state(filepath, line):
        calls["n"] += 1
        return f"goal v{calls['n']}"

    monkeypatch.setattr(lean_utils, "get_goal_state", fake_get_goal_state)
    line = tactic_tools._test_sorry_line

    tactic_tools.compile_probe_goal(line)
    # Mutate the underlying file: the content hash changes -> cache miss.
    path = Path(tactic_tools._filepath)
    path.write_text(path.read_text(encoding="utf-8") + "\n-- edit\n", encoding="utf-8")
    tactic_tools.compile_probe_goal(line)

    assert calls["n"] == 2, "a content change must invalidate the probe cache"


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
