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

