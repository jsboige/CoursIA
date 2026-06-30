"""Pytest suite for argumentation_lib._runner (See #2137).

Locks the contract of the 3-phase argumentation analysis runner (Informal -> Formal
-> Synthesis) that orchestrates the Semantic Kernel agents. This COMPLETES the
argumentation_lib test arc: _shared_state (#4664) + _state_manager_plugin (#4665) +
_runner (here) = the three vendored layers all under contract.

Durable finding (documented): `_runner` is hard-coupled to `semantic_kernel`
(Kernel, ChatCompletionAgent, AgentGroupChat, ChatHistory, ChatMessageContent,
AuthorRole) at import time, BUT semantic_kernel is NOT a hard dependency of the shim
(__init__.py lazy-imports _runner via get_analysis_runner()). So we install a
comprehensive sys.modules mock of the SK surface BEFORE importing _runner. The mock
is structural (covers every symbol _runner touches) so the runner's real wiring is
exercised end-to-end against fakes, not stubbed at the seams.

The mock AgentGroupChat.invoke() is a controllable async generator (class-level
YIELD_NAMES / RAISE) so we can drive happy-path turn counts, the max_turns cap, and
phase-level error propagation deterministically.
"""
from __future__ import annotations

import asyncio
import inspect
import os
import sys
from types import ModuleType, SimpleNamespace

# Make `argumentation_lib` (at ../argumentation_lib relative to this tests/ dir)
# importable regardless of pytest's rootdir / cwd.
_TESTS_DIR = os.path.dirname(os.path.abspath(__file__))
_ARG_ANALYSIS_DIR = os.path.dirname(_TESTS_DIR)
if _ARG_ANALYSIS_DIR not in sys.path:
    sys.path.insert(0, _ARG_ANALYSIS_DIR)


# ---------------------------------------------------------------------------
# Comprehensive semantic_kernel mock (must cover _runner + _state_manager_plugin)
# ---------------------------------------------------------------------------
def _install_sk_mock():
    if "semantic_kernel" in sys.modules and getattr(
        sys.modules["semantic_kernel"], "_coursia_mock", False
    ):
        return  # already installed by a prior test in this process

    sk = ModuleType("semantic_kernel")
    sk._coursia_mock = True

    # semantic_kernel.Kernel
    class Kernel:
        def __init__(self):
            self.plugins = {}

        def add_plugin(self, instance, plugin_name):
            instance.name = plugin_name
            self.plugins[plugin_name] = instance
            return instance

    sk.Kernel = Kernel

    # semantic_kernel.functions.kernel_function (no-op decorator, needed by
    # _state_manager_plugin which _runner imports transitively)
    functions = ModuleType("semantic_kernel.functions")

    def kernel_function(*args, **kwargs):
        def decorator(func):
            return func

        if args and callable(args[0]) and not kwargs:
            return args[0]
        return decorator

    functions.kernel_function = kernel_function
    sk.functions = functions
    sk.kernel_function = kernel_function

    # semantic_kernel.agents.chat_completion.chat_completion_agent.ChatCompletionAgent
    agents = ModuleType("semantic_kernel.agents")
    cc_parent = ModuleType("semantic_kernel.agents.chat_completion")
    gc_parent = ModuleType("semantic_kernel.agents.group_chat")

    mod_agent = ModuleType(
        "semantic_kernel.agents.chat_completion.chat_completion_agent"
    )

    class ChatCompletionAgent:
        def __init__(self, kernel=None, name=None, instructions=None, service_id=None):
            self.kernel = kernel
            self.name = name
            self.instructions = instructions
            self.service_id = service_id

    mod_agent.ChatCompletionAgent = ChatCompletionAgent

    # semantic_kernel.agents.group_chat.agent_group_chat.AgentGroupChat
    mod_gc = ModuleType("semantic_kernel.agents.group_chat.agent_group_chat")

    class AgentGroupChat:
        # class-level knobs so tests can drive the async generator deterministically
        YIELD_NAMES = ["ProjectManagerAgent", "Worker"]
        RAISE = None

        def __init__(self, agents=None):
            self.agents = agents or []

        async def invoke(self):
            if AgentGroupChat.RAISE is not None:
                raise AgentGroupChat.RAISE
            for name in AgentGroupChat.YIELD_NAMES:
                yield SimpleNamespace(name=name)

    mod_gc.AgentGroupChat = AgentGroupChat

    # contents
    contents = ModuleType("semantic_kernel.contents")
    utils = ModuleType("semantic_kernel.contents.utils")

    mod_cmc = ModuleType("semantic_kernel.contents.chat_message_content")

    class ChatMessageContent:
        def __init__(self, role=None, content=None):
            self.role = role
            self.content = content

    mod_cmc.ChatMessageContent = ChatMessageContent

    mod_role = ModuleType("semantic_kernel.contents.utils.author_role")

    class AuthorRole:
        USER = "user"
        ASSISTANT = "assistant"
        SYSTEM = "system"

    mod_role.AuthorRole = AuthorRole

    mod_hist = ModuleType("semantic_kernel.contents.chat_history")

    class ChatHistory:
        def __init__(self):
            self.messages = []

        def add_message(self, message):
            self.messages.append(message)

    mod_hist.ChatHistory = ChatHistory

    # wire attributes + register every module path Python may resolve
    sk.agents = agents
    sk.contents = contents
    agents.chat_completion = cc_parent
    agents.group_chat = gc_parent
    cc_parent.chat_completion_agent = mod_agent
    gc_parent.agent_group_chat = mod_gc
    contents.chat_message_content = mod_cmc
    contents.utils = utils
    contents.chat_history = mod_hist
    utils.author_role = mod_role

    for name, mod in {
        "semantic_kernel": sk,
        "semantic_kernel.functions": functions,
        "semantic_kernel.agents": agents,
        "semantic_kernel.agents.chat_completion": cc_parent,
        "semantic_kernel.agents.chat_completion.chat_completion_agent": mod_agent,
        "semantic_kernel.agents.group_chat": gc_parent,
        "semantic_kernel.agents.group_chat.agent_group_chat": mod_gc,
        "semantic_kernel.contents": contents,
        "semantic_kernel.contents.chat_message_content": mod_cmc,
        "semantic_kernel.contents.utils": utils,
        "semantic_kernel.contents.utils.author_role": mod_role,
        "semantic_kernel.contents.chat_history": mod_hist,
    }.items():
        sys.modules[name] = mod


_install_sk_mock()

# import target AFTER the mock is in place
from argumentation_lib._runner import (  # noqa: E402
    PROMPT_DEFINE_TASKS,
    PROMPT_INFORMAL_ANALYSIS,
    PROMPT_LOGIC_ANALYSIS,
    PROMPT_SYNTHESIS,
    AnalysisRunner,
    create_informal_agent,
    create_logic_agent,
    create_pm_agent,
)
from argumentation_lib._shared_state import RhetoricalAnalysisState  # noqa: E402


# ---------------------------------------------------------------------------
# Fixtures / helpers
# ---------------------------------------------------------------------------
def _kernel():
    return sys.modules["semantic_kernel"].Kernel()


def _state(text="Le chat est sur le paillasson. Donc le chat est a l'interieur."):
    return RhetoricalAnalysisState(text)


def _run(runner):
    """Drive the async runner from a sync test without requiring pytest-asyncio."""
    return asyncio.run(runner.run())


import pytest  # noqa: E402


@pytest.fixture(autouse=True)
def _reset_chat_knobs():
    """Reset the AgentGroupChat class-level knobs between tests."""
    # AgentGroupChat lives in the mock module; reach it via sys.modules
    AGC = sys.modules[
        "semantic_kernel.agents.group_chat.agent_group_chat"
    ].AgentGroupChat
    saved_names, saved_raise = AGC.YIELD_NAMES, AGC.RAISE
    AGC.YIELD_NAMES = ["ProjectManagerAgent", "Worker"]
    AGC.RAISE = None
    yield
    AGC.YIELD_NAMES, AGC.RAISE = saved_names, saved_raise


# ---------------------------------------------------------------------------
# Import + structure
# ---------------------------------------------------------------------------
def test_runner_imports_cleanly_with_mock():
    """_runner imports without real semantic_kernel / JVM (mock satisfies SK surface)."""
    import argumentation_lib._runner as r

    assert hasattr(r, "AnalysisRunner")
    assert hasattr(r, "create_pm_agent")


def test_public_surface_present():
    assert callable(create_pm_agent)
    assert callable(create_informal_agent)
    assert callable(create_logic_agent)
    assert inspect.isclass(AnalysisRunner)


# ---------------------------------------------------------------------------
# Prompts (vendored from EPITA pm/prompts.py) — content contracts
# ---------------------------------------------------------------------------
def test_four_prompts_exist_and_nonempty():
    for p in (PROMPT_DEFINE_TASKS, PROMPT_INFORMAL_ANALYSIS, PROMPT_LOGIC_ANALYSIS, PROMPT_SYNTHESIS):
        assert isinstance(p, str) and len(p) > 20


def test_all_prompts_carry_state_placeholder():
    for p in (PROMPT_DEFINE_TASKS, PROMPT_INFORMAL_ANALYSIS, PROMPT_LOGIC_ANALYSIS, PROMPT_SYNTHESIS):
        assert "{{$analysis_state}}" in p


def test_prompt_define_tasks_structures_the_sequence():
    low = PROMPT_DEFINE_TASKS.lower()
    # the 5-step ideal sequence + agent roster + JSON answer format
    assert "informalagent" in low or "informal" in low
    assert "logicagent" in low or "logique" in low
    assert "task_description" in PROMPT_DEFINE_TASKS
    assert "assigned_agent" in PROMPT_DEFINE_TASKS


def test_prompt_informal_targets_fallacies():
    low = PROMPT_INFORMAL_ANALYSIS.lower()
    assert "sophism" in low or "ad hominem" in low
    assert "argument" in low


def test_prompt_logic_targets_belief_sets_and_queries():
    low = PROMPT_LOGIC_ANALYSIS.lower()
    assert "belief" in low or "croyance" in low
    assert "requ" in low  # requete / query / require


# ---------------------------------------------------------------------------
# Zero secrets (HARD — the module docstring claims it)
# ---------------------------------------------------------------------------
def _runner_source():
    import argumentation_lib._runner as r

    with open(r.__file__, encoding="utf-8") as fh:
        return fh.read()


def test_no_model_name_literals_in_source():
    src = _runner_source().lower()
    for needle in ("gpt-", "claude", "gemini", "llama", "qwen", "mistral", "deepseek"):
        assert needle not in src, f"model name literal found: {needle}"


def test_no_environment_reads_in_source():
    src = _runner_source()
    # the runner receives the LLM service_id + kernel from the notebook; it must NOT
    # read env / files for credentials itself.
    for needle in ("os.getenv", "os.environ", "getenv(", "load_dotenv", ".env"):
        assert needle not in src, f"env read found: {needle}"


def test_no_secret_literals_in_source():
    import re

    src = _runner_source()
    for pat in (r"sk-[a-zA-Z0-9]{16}", r"Bearer\s", r'key\s*=\s*["\']', r'token\s*=\s*["\']'):
        assert not re.search(pat, src), f"secret-like literal matched {pat}"


# ---------------------------------------------------------------------------
# Agent builders
# ---------------------------------------------------------------------------
def test_create_pm_agent_registers_state_manager_and_returns_agent():
    k, s = _kernel(), _state()
    agent = create_pm_agent(k, "svc", s)
    assert agent.name == "ProjectManagerAgent"
    assert agent.service_id == "svc"
    assert agent.instructions is PROMPT_DEFINE_TASKS
    assert "StateManager" in k.plugins


def test_create_informal_agent_name_and_instructions():
    k, s = _kernel(), _state()
    create_pm_agent(k, "svc", s)  # pre-register plugin
    agent = create_informal_agent(k, "svc", s)
    assert agent.name == "InformalAgent"
    assert agent.instructions is PROMPT_INFORMAL_ANALYSIS


def test_create_logic_agent_name_and_instructions():
    k, s = _kernel(), _state()
    create_pm_agent(k, "svc", s)
    agent = create_logic_agent(k, "svc", s)
    assert agent.name == "LogicAgent"
    assert agent.instructions is PROMPT_LOGIC_ANALYSIS


def test_agent_builders_are_idempotent_on_plugin_registration():
    """If StateManager is already on the kernel, builders must NOT re-add it."""
    k, s = _kernel(), _state()
    create_pm_agent(k, "svc", s)
    assert len(k.plugins) == 1
    create_informal_agent(k, "svc", s)
    create_logic_agent(k, "svc", s)
    assert len(k.plugins) == 1  # still exactly one StateManager plugin
    assert "StateManager" in k.plugins


def test_informal_builder_registers_plugin_when_absent():
    """Informal/Logic builders also register the plugin if PM wasn't called first."""
    k, s = _kernel(), _state()
    assert "StateManager" not in k.plugins
    create_informal_agent(k, "svc", s)
    assert "StateManager" in k.plugins


# ---------------------------------------------------------------------------
# AnalysisRunner.__init__
# ---------------------------------------------------------------------------
def test_runner_init_stores_attributes():
    k, s = _kernel(), _state()
    runner = AnalysisRunner(k, "my-svc", s, max_turns=8)
    assert runner.kernel is k
    assert runner.llm_service_id == "my-svc"
    assert runner.state is s
    assert runner.max_turns == 8


def test_runner_init_default_max_turns():
    runner = AnalysisRunner(_kernel(), "svc", _state())
    assert runner.max_turns == 20


def test_runner_init_registers_plugin_when_absent():
    k = _kernel()
    assert "StateManager" not in k.plugins
    runner = AnalysisRunner(k, "svc", _state())
    assert "StateManager" in k.plugins
    assert runner._smp is not None


def test_runner_init_does_not_re_register_when_present():
    k, s = _kernel(), _state()
    k.add_plugin(SimpleNamespace(name="StateManager"), "StateManager")
    runner = AnalysisRunner(k, "svc", s)
    # plugin already there -> runner leaves it and holds no new smp
    assert runner._smp is None
    assert len(k.plugins) == 1


# ---------------------------------------------------------------------------
# run() — happy path
# ---------------------------------------------------------------------------
def test_run_returns_expected_top_level_shape():
    runner = AnalysisRunner(_kernel(), "svc", _state())
    out = _run(runner)
    assert set(out.keys()) >= {"phases", "state_snapshot", "conclusion"}


def test_run_executes_three_phases_in_order():
    out = _run(AnalysisRunner(_kernel(), "svc", _state()))
    names = [p["name"] for p in out["phases"]]
    assert names == ["informal", "formal", "synthesis"]


def test_run_phases_completed_with_turn_counts():
    out = _run(AnalysisRunner(_kernel(), "svc", _state()))
    for phase in out["phases"]:
        assert phase["status"] == "completed"
        assert isinstance(phase["turns"], int) and phase["turns"] >= 1


def test_run_populates_state_snapshot():
    out = _run(AnalysisRunner(_kernel(), "svc", _state()))
    snap = out["state_snapshot"]
    assert isinstance(snap, dict) and snap  # summarize=True -> non-empty dict


def test_run_conclusion_none_when_state_has_no_final_conclusion():
    out = _run(AnalysisRunner(_kernel(), "svc", _state()))
    # nothing wrote a final conclusion (no real LLM) -> conclusion stays None
    assert out["conclusion"] is None


def test_run_conclusion_surfaced_when_state_carries_one():
    s = _state()
    s.final_conclusion = "Synthese finale de test xyz."
    out = _run(AnalysisRunner(_kernel(), "svc", s))
    assert out["conclusion"] == "Synthese finale de test xyz."


# ---------------------------------------------------------------------------
# run() — max_turns cap
# ---------------------------------------------------------------------------
def test_run_phase_caps_at_max_turns_half():
    """Phases 1 & 2 must break at max_turns // 2, not exhaust the whole generator."""
    AGC = sys.modules[
        "semantic_kernel.agents.group_chat.agent_group_chat"
    ].AgentGroupChat
    AGC.YIELD_NAMES = [f"turn{i}" for i in range(50)]  # generator yields plenty
    runner = AnalysisRunner(_kernel(), "svc", _state(), max_turns=4)  # //2 == 2
    out = _run(runner)
    informal = next(p for p in out["phases"] if p["name"] == "informal")
    formal = next(p for p in out["phases"] if p["name"] == "formal")
    assert informal["turns"] == 2
    assert formal["turns"] == 2


def test_run_phase3_caps_at_three_regardless_of_max_turns():
    AGC = sys.modules[
        "semantic_kernel.agents.group_chat.agent_group_chat"
    ].AgentGroupChat
    AGC.YIELD_NAMES = [f"turn{i}" for i in range(50)]
    runner = AnalysisRunner(_kernel(), "svc", _state(), max_turns=100)
    out = _run(runner)
    synthesis = next(p for p in out["phases"] if p["name"] == "synthesis")
    assert synthesis["turns"] == 3  # hardcoded cap in phase 3


# ---------------------------------------------------------------------------
# run() — error propagation (each phase isolates failures)
# ---------------------------------------------------------------------------
def test_run_records_phase_error_when_invoke_raises():
    AGC = sys.modules[
        "semantic_kernel.agents.group_chat.agent_group_chat"
    ].AgentGroupChat
    AGC.RAISE = RuntimeError("simulated LLM blow-up")
    out = _run(AnalysisRunner(_kernel(), "svc", _state()))
    assert out["phases"], "phases should still be recorded even on error"
    for phase in out["phases"]:
        assert phase["status"] == "error"
        assert "simulated LLM blow-up" in phase["error"]


def test_run_error_does_not_crash_overall_run():
    AGC = sys.modules[
        "semantic_kernel.agents.group_chat.agent_group_chat"
    ].AgentGroupChat
    AGC.RAISE = ValueError("boom")
    out = _run(AnalysisRunner(_kernel(), "svc", _state()))
    # run() swallows per-phase exceptions and still returns a structured dict
    assert isinstance(out, dict) and "phases" in out
    assert out["state_snapshot"] is not None  # snapshot still taken at the end


# ---------------------------------------------------------------------------
# run_sync()
# ---------------------------------------------------------------------------
def test_run_sync_returns_same_shape_as_run():
    runner = AnalysisRunner(_kernel(), "svc", _state())
    out = runner.run_sync()
    assert [p["name"] for p in out["phases"]] == ["informal", "formal", "synthesis"]


# ---------------------------------------------------------------------------
# Determinism
# ---------------------------------------------------------------------------
def test_run_is_deterministic_under_same_mock_config():
    r1 = _run(AnalysisRunner(_kernel(), "svc", _state()))
    r2 = _run(AnalysisRunner(_kernel(), "svc", _state()))
    assert [p["turns"] for p in r1["phases"]] == [p["turns"] for p in r2["phases"]]
    assert [p["name"] for p in r1["phases"]] == [p["name"] for p in r2["phases"]]
