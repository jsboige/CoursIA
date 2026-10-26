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
            self._services = {}

        def add_plugin(self, instance, plugin_name):
            instance.name = plugin_name
            self.plugins[plugin_name] = instance
            return instance

        def add_service(self, service, **kwargs):
            self._services[getattr(service, "service_id", None)] = service
            return service

        def get_service(self, service_id):
            return self._services.get(service_id)

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

    # semantic_kernel.functions.kernel_arguments.KernelArguments (needed by
    # _runner since the SK-1.44 repair: agents carry a default
    # KernelArguments(analysis_state=...) for the prompts' variable token)
    mod_ka = ModuleType("semantic_kernel.functions.kernel_arguments")

    class KernelArguments(dict):
        def __init__(self, *args, **kwargs):
            super().__init__(*args, **kwargs)

    mod_ka.KernelArguments = KernelArguments
    functions.kernel_arguments = mod_ka

    # semantic_kernel.agents.chat_completion.chat_completion_agent.ChatCompletionAgent
    agents = ModuleType("semantic_kernel.agents")
    cc_parent = ModuleType("semantic_kernel.agents.chat_completion")
    gc_parent = ModuleType("semantic_kernel.agents.group_chat")

    mod_agent = ModuleType(
        "semantic_kernel.agents.chat_completion.chat_completion_agent"
    )

    class ChatCompletionAgent:
        def __init__(
            self,
            kernel=None,
            name=None,
            instructions=None,
            service=None,
            arguments=None,
        ):
            self.kernel = kernel
            self.name = name
            self.instructions = instructions
            self.service = service
            self.arguments = arguments

    mod_agent.ChatCompletionAgent = ChatCompletionAgent

    # semantic_kernel.agents.group_chat.agent_group_chat.AgentGroupChat
    mod_gc = ModuleType("semantic_kernel.agents.group_chat.agent_group_chat")

    class AgentGroupChat:
        # class-level knobs so tests can drive the async generator deterministically
        YIELD_NAMES = ["ProjectManagerAgent", "Worker"]
        RAISE = None
        # #18776 reprise ciblée : side-effect appelé avant chaque tour rendu
        # (permet à un test de simuler un agent qui comble le déficit).
        ON_TURN = None
        # instances created since the last reset (order-preserving)
        instances = []

        def __init__(self, agents=None, chat_history=None, termination_strategy=None):
            self.agents = agents or []
            self.chat_history = chat_history
            self.termination_strategy = termination_strategy
            AgentGroupChat.instances.append(self)

        async def invoke(self):
            if AgentGroupChat.RAISE is not None:
                raise AgentGroupChat.RAISE
            for name in AgentGroupChat.YIELD_NAMES:
                if AgentGroupChat.ON_TURN is not None:
                    AgentGroupChat.ON_TURN(name, self)
                yield SimpleNamespace(name=name)

    mod_gc.AgentGroupChat = AgentGroupChat

    # semantic_kernel.agents.strategies.termination.default_termination_strategy
    # (#18776) : le runner passe une stratégie explicite pour que les budgets
    # de phase mordent — le fake enregistre ses instances pour l'assertion.
    strategies = ModuleType("semantic_kernel.agents.strategies")
    term_parent = ModuleType("semantic_kernel.agents.strategies.termination")
    mod_dts = ModuleType(
        "semantic_kernel.agents.strategies.termination.default_termination_strategy"
    )

    class DefaultTerminationStrategy:
        instances = []

        def __init__(self, maximum_iterations=5):
            self.maximum_iterations = maximum_iterations
            DefaultTerminationStrategy.instances.append(self)

    mod_dts.DefaultTerminationStrategy = DefaultTerminationStrategy
    agents.strategies = strategies
    strategies.termination = term_parent
    term_parent.default_termination_strategy = mod_dts

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
        "semantic_kernel.functions.kernel_arguments": mod_ka,
        "semantic_kernel.agents": agents,
        "semantic_kernel.agents.chat_completion": cc_parent,
        "semantic_kernel.agents.chat_completion.chat_completion_agent": mod_agent,
        "semantic_kernel.agents.group_chat": gc_parent,
        "semantic_kernel.agents.group_chat.agent_group_chat": mod_gc,
        "semantic_kernel.agents.strategies": strategies,
        "semantic_kernel.agents.strategies.termination": term_parent,
        "semantic_kernel.agents.strategies.termination.default_termination_strategy": mod_dts,
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
    saved_on_turn, saved_instances = AGC.ON_TURN, AGC.instances
    AGC.ON_TURN = None
    AGC.instances = []
    yield
    AGC.YIELD_NAMES, AGC.RAISE = saved_names, saved_raise
    AGC.ON_TURN, AGC.instances = saved_on_turn, saved_instances


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
    service = k.add_service(SimpleNamespace(service_id="svc"))
    agent = create_pm_agent(k, "svc", s)
    assert agent.name == "ProjectManagerAgent"
    # SK >= 1.30 : ChatCompletionAgent prend l'instance (service=), pas
    # l'identifiant — _resolve_service resout celle enregistree sous "svc".
    assert agent.service is service
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


def test_logic_agent_fallback_taken_only_for_declared_test_stub():
    """Stub declare (`_coursia_mock`) : agent construit sans settings, pas d'erreur.

    C'est la branche legitime du repli : le stub plat de ce fichier n'expose
    pas `semantic_kernel.connectors` (revue ai-01 du 21/10, #18395).
    """
    sk = sys.modules["semantic_kernel"]
    assert getattr(sk, "_coursia_mock", False) is True, "precondition du stub"
    k, s = _kernel(), _state()
    agent = create_logic_agent(k, "svc", s)
    assert agent.name == "LogicAgent"


def test_logic_agent_propagates_import_error_outside_declared_stub():
    """Hors stub declare, une installation SK cassee LEVE au lieu de degrader en silence.

    Sans cette borne, `except ImportError: fcb = None` avalait toute
    installation cassée ou incompatible et le carnet produisait un run
    degrade d'apparence normale (#18395).
    """
    sk = sys.modules["semantic_kernel"]
    had_flag = getattr(sk, "_coursia_mock", False)
    k, s = _kernel(), _state()
    sk._coursia_mock = False
    try:
        with pytest.raises(ImportError):
            create_logic_agent(k, "svc", s)
    finally:
        sk._coursia_mock = had_flag
    assert getattr(sk, "_coursia_mock", False) is had_flag, "drapeau restaure"


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


# ---------------------------------------------------------------------------
# Per-phase turn budget (#18776) — max_informal_turns / max_formal_turns
# ---------------------------------------------------------------------------
def test_per_phase_budget_defaults_to_max_turns_half_when_unset():
    """When max_informal_turns / max_formal_turns are None, fall back to
    max_turns // 2 (legacy behaviour). Locks backwards compatibility with
    callers that do not opt into per-phase budgets.
    """
    runner = AnalysisRunner(_kernel(), "svc", _state(), max_turns=20)
    assert runner.max_informal_turns == 10
    assert runner.max_formal_turns == 10


def test_per_phase_budget_independent_values_override_legacy_default():
    """max_informal_turns and max_formal_turns, when provided, override
    the max_turns // 2 fallback independently.
    """
    runner = AnalysisRunner(
        _kernel(), "svc", _state(),
        max_turns=20, max_informal_turns=15, max_formal_turns=8,
    )
    assert runner.max_informal_turns == 15
    assert runner.max_formal_turns == 8
    assert runner.max_turns == 20  # legacy field untouched


def test_phase1_respects_max_informal_turns_above_max_turns_half():
    """Phase 1 must break at max_informal_turns (15 here), not at the legacy
    max_turns // 2 (10). Guards the regression of #18776.
    """
    AGC = sys.modules[
        "semantic_kernel.agents.group_chat.agent_group_chat"
    ].AgentGroupChat
    AGC.YIELD_NAMES = [f"turn{i}" for i in range(50)]
    runner = AnalysisRunner(
        _kernel(), "svc", _state(),
        max_turns=20, max_informal_turns=15, max_formal_turns=10,
    )
    out = _run(runner)
    informal = next(p for p in out["phases"] if p["name"] == "informal")
    formal = next(p for p in out["phases"] if p["name"] == "formal")
    assert informal["turns"] == 15
    assert formal["turns"] == 10


def test_phase2_respects_max_formal_turns_below_max_turns_half():
    """Phase 2 must break at max_formal_turns (3 here), independently of
    the legacy max_turns // 2 (5). Mirror image of the phase-1 case.
    """
    AGC = sys.modules[
        "semantic_kernel.agents.group_chat.agent_group_chat"
    ].AgentGroupChat
    AGC.YIELD_NAMES = [f"turn{i}" for i in range(50)]
    runner = AnalysisRunner(
        _kernel(), "svc", _state(),
        max_turns=10, max_informal_turns=5, max_formal_turns=3,
    )
    out = _run(runner)
    informal = next(p for p in out["phases"] if p["name"] == "informal")
    formal = next(p for p in out["phases"] if p["name"] == "formal")
    assert informal["turns"] == 5
    assert formal["turns"] == 3


# ---------------------------------------------------------------------------
# budget_variance_study (#18776) — verdict-metric extraction on synthetic states
# ---------------------------------------------------------------------------
class _StudyState:
    """Minimal state object exposing the surface compute_verdict_metrics reads."""

    RAW = (
        "les energies renouvelables sont essentielles pour lutter contre le "
        "changement climatique et reduire les emissions de co2"
    )

    def __init__(self, arguments=None, fallacies=None, conclusion=None,
                 belief_sets=None, query_log=None):
        self.raw_text = self.RAW
        self.identified_arguments = arguments or {}
        self.identified_fallacies = fallacies or {}
        self.final_conclusion = conclusion
        self.belief_sets = belief_sets or {}
        self.query_log = query_log or []
        self.answers = {}


def _substantive_argument():
    return {
        "arg1": ("les energies renouvelables sont essentielles pour lutter "
                 "contre le changement climatique")
    }


def _substantive_fallacy():
    return {
        "fal1": {
            "type": "Appel a l'autorite",
            "justification": "L'orateur invoque un expert hors de son domaine.",
            "target_argument_id": "arg1",
        }
    }


def test_study_metrics_empty_state_is_not_validated():
    from argumentation_lib import budget_variance_study as bvs

    m = bvs.compute_verdict_metrics(_StudyState())
    # port strict : l'état vide porte QUERIES_NONE, donc FAILED_FORMAL (le
    # statut de confiance ne s'applique qu'après les échecs de forme et de
    # couche formelle — un état vide n'est jamais « validé »)
    assert m["validation_status"] == "FAILED_FORMAL"
    assert m["failed_reason"] == "ARGUMENTS_NONE"
    assert m["substantive_arguments"] == 0
    assert m["substantive_fallacies"] == 0


def test_study_metrics_substantive_content_passes_content_checks():
    from argumentation_lib import budget_variance_study as bvs

    m = bvs.compute_verdict_metrics(_StudyState(
        arguments=_substantive_argument(),
        fallacies=_substantive_fallacy(),
        conclusion="Synthese finale de l'analyse.",
        belief_sets={"bs1": "p"},
        query_log=[{"raw_result": "ACCEPTED"}],
    ))
    assert m["substantive_arguments"] == 1
    assert m["substantive_fallacies"] == 1
    assert m["failed_reason"] is None
    # 6 checks passed out of 7 slots (the notebook's max_checks counts an
    # extra split it never awards) -> 0.86, above the 0.8 bar.
    assert m["confidence_score"] == 0.86
    assert m["validation_status"] == "COMPLETE_VALIDATED"


def test_study_metrics_state_key_argument_degrades_to_form_only():
    from argumentation_lib import budget_variance_study as bvs

    m = bvs.compute_verdict_metrics(_StudyState(
        arguments={"arg1": "analysis_state"},
        fallacies=_substantive_fallacy(),
        conclusion="c",
    ))
    assert m["substantive_arguments"] == 0
    assert m["failed_reason"] == "ARGUMENTS_FORM_ONLY"
    assert m["validation_status"] == "INVALIDATED_FORM"


def test_study_metrics_unknown_fallacy_type_degrades_to_form_only():
    from argumentation_lib import budget_variance_study as bvs

    m = bvs.compute_verdict_metrics(_StudyState(
        arguments=_substantive_argument(),
        fallacies={"fal1": {"type": "Type Inconnu",
                            "justification": "pas assez d'elements ici",
                            "target_argument_id": "arg1"}},
        conclusion="c",
    ))
    assert m["substantive_fallacies"] == 0
    assert m["failed_reason"] == "FALLACIES_FORM_ONLY"
    assert m["validation_status"] == "INVALIDATED_FORM"


def test_study_summarize_counts_verdict_forms():
    from argumentation_lib import budget_variance_study as bvs

    runs = [
        {"validation_status": "PARTIAL_VALIDATED", "failed_reason": None,
         "substantive_arguments": 3, "substantive_fallacies": 1,
         "total_turns": 23, "duration_s": 90.0},
        {"validation_status": "PARTIAL_VALIDATED", "failed_reason": None,
         "substantive_arguments": 4, "substantive_fallacies": 0,
         "total_turns": 25, "duration_s": 100.0},
        {"error": "APIConnectionError: boom"},
    ]
    s = bvs.summarize(runs)
    assert s["runs_ok"] == 2
    assert s["runs_error"] == 1
    assert s["verdict_forms_unique"] == ["PARTIAL_VALIDATED"]
    assert s["verdict_forms_distribution"] == {"PARTIAL_VALIDATED": 2}
    assert s["substantive_arguments"]["min"] == 3
    assert s["substantive_arguments"]["max"] == 4


def test_study_load_batch_text_reads_notebook_example():
    from argumentation_lib import budget_variance_study as bvs

    text = bvs._load_batch_text()
    assert len(text) > 1000
    assert "transition energetique" in text


# ---------------------------------------------------------------------------
# Budgets qui mordent (#18776 tranche reprise) — la stratégie de terminaison
# explicite remplace le DefaultTerminationStrategy SK (maximum_iterations=5)
# qui plafonnait silencieusement toute phase sous son budget déclaré.
# ---------------------------------------------------------------------------
def _agc():
    return sys.modules[
        "semantic_kernel.agents.group_chat.agent_group_chat"
    ].AgentGroupChat


def _dts():
    return sys.modules[
        "semantic_kernel.agents.strategies.termination."
        "default_termination_strategy"
    ].DefaultTerminationStrategy


def test_group_chats_receive_explicit_termination_strategy():
    """Chaque phase doit porter SON budget dans la stratégie de terminaison.

    Sans stratégie explicite, SK plafonne tout group chat à 5 itérations :
    les budgets #18785 (10/15) étaient des boutons morts — 20/20 runs réels
    arrêtés à 5 tours par phase (#18776, campagnes 1-2). Le mock enregistre
    les stratégies reçues : informal=15, formal=10, synthesis=3.
    """
    AGC = _agc()
    AGC.YIELD_NAMES = [f"turn{i}" for i in range(50)]
    runner = AnalysisRunner(
        _kernel(), "svc", _state(),
        max_turns=20, max_informal_turns=15, max_formal_turns=10,
    )
    _run(runner)
    strategies = [c.termination_strategy for c in AGC.instances]
    assert len(strategies) == 3  # informal, formal, synthesis (pas de reprise)
    assert [s.maximum_iterations for s in strategies] == [15, 10, 3]


def test_termination_strategy_cap_matches_legacy_default_when_unset():
    """Sans budgets explicites, la stratégie porte le repli max_turns // 2."""
    AGC = _agc()
    AGC.YIELD_NAMES = [f"turn{i}" for i in range(50)]
    _run(AnalysisRunner(_kernel(), "svc", _state(), max_turns=20))
    strategies = [c.termination_strategy for c in AGC.instances]
    assert [s.maximum_iterations for s in strategies] == [10, 10, 3]


# ---------------------------------------------------------------------------
# Reprise ciblée de la phase déficitaire (#18776, branche « ou »)
# ---------------------------------------------------------------------------
def _substantive_arg_desc():
    # phrase du texte par défaut de _state() — recouvrement >= 12 chars
    return "Le chat est sur le paillasson depuis le debut de l'apres-midi"


def _substantive_fallacy_add(state, target="arg_1"):
    state.add_fallacy(
        "Appel a l'autorite",
        "L'orateur invoque son voisin ingenieur comme expert absolu.",
        target,
    )


def _anchor_argument(state):
    """Argument court (non substantif, non clé d'état) : fournit un id
    ciblable aux sophismes des tests — le validateur strict exige une
    cible réellement présente dans l'état."""
    return state.add_argument("argument court")


def test_resumption_defaults_off():
    """La reprise est opt-in : attributs par défaut verrouillés."""
    runner = AnalysisRunner(_kernel(), "svc", _state())
    assert runner.targeted_resumption is False
    assert runner.max_resumption_argument_turns == 4
    assert runner.max_resumption_fallacy_turns == 4
    assert runner.resumption_max_rounds == 2
    assert runner.min_substantive_arguments == 2
    assert runner.min_substantive_fallacies == 2


def test_resumption_off_keeps_exactly_three_phases():
    """targeted_resumption=False (défaut) : rien entre informal et formal."""
    out = _run(AnalysisRunner(_kernel(), "svc", _state()))
    assert [p["name"] for p in out["phases"]] == ["informal", "formal", "synthesis"]


def test_resumption_noop_when_both_targets_met():
    """État déjà substantif des deux côtés -> aucune entrée de reprise."""
    s = _state()
    s.add_argument(_substantive_arg_desc())
    s.add_argument("Donc le chat est a l'interieur selon le raisonnement du texte")
    _substantive_fallacy_add(s, target="arg_1")
    _substantive_fallacy_add(s, target="arg_2")
    runner = AnalysisRunner(_kernel(), "svc", s, targeted_resumption=True)
    out = _run(runner)
    assert [p["name"] for p in out["phases"]] == ["informal", "formal", "synthesis"]


def test_resumption_triggers_on_argument_deficit_only():
    """Sophismes substantifs présents, zéro argument -> seule la reprise
    arguments tourne (c'est la séparation arguments/sophismes demandée)."""
    s = _state()
    # ancres : ids ciblables — sinon les sophismes sont des cibles fantômes
    # que le nettoyage retirerait, ouvrant un second déficit
    _anchor_argument(s)
    _anchor_argument(s)
    _substantive_fallacy_add(s)
    _substantive_fallacy_add(s)
    runner = AnalysisRunner(_kernel(), "svc", s, targeted_resumption=True)
    out = _run(runner)
    names = [p["name"] for p in out["phases"]]
    assert names[0] == "informal"
    assert "resumption_arguments" in names
    assert "resumption_fallacies" not in names
    # la reprise s'insère AVANT la phase formelle : celle-ci encode des
    # arguments, elle doit trouver les arguments comblés
    assert names.index("resumption_arguments") < names.index("formal")


def test_resumption_triggers_on_fallacy_deficit_only():
    """Arguments substantifs présents, zéro sophisme -> seule la reprise
    sophismes tourne."""
    s = _state()
    s.add_argument(_substantive_arg_desc())
    s.add_argument("Donc le chat est a l'interieur selon le raisonnement du texte")
    runner = AnalysisRunner(_kernel(), "svc", s, targeted_resumption=True)
    out = _run(runner)
    names = [p["name"] for p in out["phases"]]
    assert "resumption_fallacies" in names
    assert "resumption_arguments" not in names


def test_resumption_rounds_bounded_when_deficit_persists():
    """Le mock ne comble jamais le déficit -> exactement resumption_max_rounds
    rounds de reprise, pas plus."""
    s = _state()  # 0 argument, 0 sophisme -> les deux déficits persistent
    runner = AnalysisRunner(
        _kernel(), "svc", s, targeted_resumption=True, resumption_max_rounds=2
    )
    out = _run(runner)
    args_rounds = [
        p["round"] for p in out["phases"] if p["name"] == "resumption_arguments"
    ]
    fall_rounds = [
        p["round"] for p in out["phases"] if p["name"] == "resumption_fallacies"
    ]
    assert args_rounds == [1, 2]
    assert fall_rounds == [1, 2]


def test_resumption_stops_when_chat_resolves_deficit():
    """Un chat de reprise qui comble le déficit -> pas de second round."""
    AGC = _agc()
    s = _state()
    _anchor_argument(s)
    _anchor_argument(s)
    _substantive_fallacy_add(s)
    _substantive_fallacy_add(s)

    fill_calls = {"n": 0}
    fill_arguments_descs = [
        _substantive_arg_desc(),
        "Donc le chat est a l'interieur selon le raisonnement du texte",
    ]

    def _fill_arguments(name, chat):
        # seule la reprise comble : le chat informel (agents PM+Informal)
        # ne doit pas produire les arguments ici. Un argument par tour.
        agent_names = [getattr(a, "name", "") for a in chat.agents]
        if "ResumptionArgumentsAgent" in agent_names and fill_calls["n"] < 2:
            s.add_argument(fill_arguments_descs[fill_calls["n"]])
            fill_calls["n"] += 1

    AGC.YIELD_NAMES = ["ResumptionArgumentsAgent", "ResumptionArgumentsAgent"]
    AGC.ON_TURN = _fill_arguments
    runner = AnalysisRunner(_kernel(), "svc", s, targeted_resumption=True)
    out = _run(runner)
    args_entries = [
        p for p in out["phases"] if p["name"] == "resumption_arguments"
    ]
    assert len(args_entries) == 1  # round 1 a comblé -> pas de round 2
    entry = args_entries[0]
    assert entry["status"] == "completed"
    assert entry["substantive_before"] == 0
    assert entry["substantive_after"] == 2


def test_resumption_budgets_carried_by_termination_strategy():
    """Les budgets de reprise arguments/sophismes sont séparés et portés
    chacun par SA stratégie de terminaison (budget par phase au sens de
    l'issue : arguments vs sophismes)."""
    AGC = _agc()
    s = _state()  # les deux déficits
    runner = AnalysisRunner(
        _kernel(), "svc", s, targeted_resumption=True,
        max_informal_turns=10, max_formal_turns=10,
        max_resumption_argument_turns=3, max_resumption_fallacy_turns=2,
        resumption_max_rounds=1,
    )
    _run(runner)
    caps = [c.termination_strategy.maximum_iterations for c in AGC.instances]
    # informal(10), res_args(3), res_fall(2), formal(10), synthesis(3)
    assert caps == [10, 3, 2, 10, 3]


def test_resumption_entry_records_turns_and_budget():
    """L'entrée de reprise rapporte tours consommés, budget et comptes."""
    AGC = _agc()
    AGC.YIELD_NAMES = [f"t{i}" for i in range(10)]
    s = _state()  # deux déficits
    runner = AnalysisRunner(
        _kernel(), "svc", s, targeted_resumption=True,
        max_resumption_argument_turns=4, resumption_max_rounds=1,
    )
    out = _run(runner)
    entry = next(p for p in out["phases"] if p["name"] == "resumption_arguments")
    assert entry["turns"] == 4  # borné par le budget, pas par le générateur
    assert entry["budget_turns"] == 4


def test_resumption_phase_error_isolated():
    """Une reprise qui échoue est isolée : le pipeline continue."""
    AGC = _agc()
    s = _state()
    _anchor_argument(s)
    _anchor_argument(s)
    _substantive_fallacy_add(s)
    _substantive_fallacy_add(s)
    # Le knob RAISE est lu au DÉMARRAGE de chaque générateur invoke : on
    # l'arme pendant le premier tour de la phase informelle (qui se termine
    # normalement — son contrôle a déjà eu lieu), si bien que le PREMIER
    # chat démarré ensuite est la reprise arguments, qui explose.
    state = {"armed": False}

    def _boom_after_informal(name, chat):
        if not state["armed"]:
            state["armed"] = True
            AGC.RAISE = RuntimeError("resumption blow-up")

    AGC.ON_TURN = _boom_after_informal
    runner = AnalysisRunner(_kernel(), "svc", s, targeted_resumption=True)
    out = _run(runner)
    entry = next(p for p in out["phases"] if p["name"] == "resumption_arguments")
    assert entry["status"] == "error"
    assert "resumption blow-up" in entry["error"]
    # le pipeline continue malgré l'échec de la reprise : les trois phases
    # principales restent présentes dans le rapport
    assert [p["name"] for p in out["phases"]][-1] == "synthesis"


# ---------------------------------------------------------------------------
# _verdict — source unique des seuils de substance (#18776)
# ---------------------------------------------------------------------------
def test_verdict_module_is_single_source_for_study():
    """budget_variance_study ré-exporte bien depuis _verdict (source unique)."""
    from argumentation_lib import _verdict
    from argumentation_lib import budget_variance_study as bvs

    assert bvs.compute_verdict_metrics is _verdict.compute_verdict_metrics
    assert bvs.argument_has_substance is _verdict.argument_has_substance
    assert bvs.fallacy_has_substance is _verdict.fallacy_has_substance


def test_verdict_count_substantive_on_real_state():
    from argumentation_lib._verdict import (
        count_substantive_arguments,
        count_substantive_fallacies,
    )

    s = _state()
    s.add_argument(_substantive_arg_desc())
    s.add_argument("analysis_state")  # clé d'état -> non substantif
    _substantive_fallacy_add(s)
    s.add_fallacy("Type Inconnu", "Justification manquante", "arg_1")
    assert count_substantive_arguments(s) == 1
    assert count_substantive_fallacies(s) == 1


def test_verdict_module_reads_no_env():
    """_verdict ne lit ni env ni réseau (contrat runner zéro-env)."""
    import argumentation_lib._verdict as v

    with open(v.__file__, encoding="utf-8") as fh:
        src = fh.read()
    for needle in ("os.getenv", "os.environ", "getenv(", "load_dotenv"):
        assert needle not in src, f"env read found: {needle}"


def test_verdict_constants_match_notebook_validation_cell():
    """Les constantes de _verdict sont celles de la cellule de validation du
    carnet 08b (port verbatim) — ce test rougit si l'une des deux dérive."""
    import ast
    import json as _json
    import pathlib

    import argumentation_lib._verdict as v

    nb_path = (
        pathlib.Path(__file__).resolve().parents[1]
        / "Argumentation-08b-Executor-Python.ipynb"
    )
    nb = _json.loads(nb_path.read_text(encoding="utf-8"))
    cell_src = next(
        "".join(c["source"])
        for c in nb["cells"]
        if c["cell_type"] == "code"
        and "CELLULE DE VALIDATION FINALE" in "".join(c["source"])
    )

    # constantes scalaires : assignations litterales en tête de cellule
    scalars = {}
    for node in ast.parse(cell_src).body:
        if (
            isinstance(node, ast.AnnAssign)
            and isinstance(node.target, ast.Name)
            and isinstance(node.value, ast.Constant)
        ):
            scalars[node.target.id] = node.value.value
    assert scalars.get("MIN_ARGUMENT_WORDS") == v.MIN_ARGUMENT_WORDS
    assert scalars.get("MIN_ARGUMENT_TEXT_OVERLAP") == v.MIN_ARGUMENT_TEXT_OVERLAP

    # liste noire des clés d'état : comparer le set littéral, assignation
    # par expression (set display), nom pour nom
    for node in ast.parse(cell_src).body:
        if (
            isinstance(node, ast.AnnAssign)
            and isinstance(node.target, ast.Name)
            and node.target.id == "STATE_KEYS_BLACKLIST"
        ):
            cell_blacklist = ast.literal_eval(node.value)
            assert cell_blacklist == v.STATE_KEYS_BLACKLIST
            break
    else:
        raise AssertionError("STATE_KEYS_BLACKLIST introuvable dans la cellule")


def test_verdict_fallacy_requires_existing_target():
    """Strict (#18395, check 2b) : une cible inexistante n'est pas un lien
    faible mais un lien absent. Le prédicat historique (cible non vide)
    reste disponible pour les appelants sans état sous la main."""
    from argumentation_lib._verdict import (
        count_substantive_fallacies,
        fallacy_has_substance,
    )

    ghost = {
        "type": "Appel a l'autorite",
        "justification": "L'orateur invoque son voisin ingenieur comme expert absolu.",
        "target_argument_id": "arg_9",
    }
    assert fallacy_has_substance(ghost) is True  # historique : cible non vide

    s = _state()
    s.add_argument(_substantive_arg_desc())  # arg_1
    s.add_fallacy(ghost["type"], ghost["justification"], "arg_9")
    assert count_substantive_fallacies(s) == 0  # strict : cible fantôme


def test_verdict_normalizes_argument_id_families():
    """argument_3 / arg_3 / arg_N3 désignent le même objet : un sophisme
    qui cite l'une pendant que l'état nomme l'autre reste substantif."""
    from argumentation_lib._verdict import (
        count_substantive_fallacies,
        normalize_argument_id,
    )

    assert normalize_argument_id("argument_3") == "arg_3"
    assert normalize_argument_id("arg_N3") == "arg_3"
    assert normalize_argument_id("arg_3") == "arg_3"

    s = _state()
    s.add_argument(_substantive_arg_desc())  # arg_1
    # le sophisme cite la forme longue de l'id que l'état a généré
    s.add_fallacy(
        "Appel a l'autorite",
        "L'orateur invoque son voisin ingenieur comme expert absolu.",
        "argument_1",
    )
    assert count_substantive_fallacies(s) == 1


def test_verdict_state_key_and_phantom_reported_in_metrics():
    """compute_verdict_metrics expose les deux symptômes mesurés (#18395)
    pour le carnet comme pour la porte de reprise."""
    from argumentation_lib._verdict import compute_verdict_metrics

    s = _state()
    s.add_argument(_substantive_arg_desc())
    s.add_argument("analysis_state")  # clé d'état -> check 1b
    _substantive_fallacy_add(s, target="arg_1")
    s.add_fallacy(
        "Appel a l'autorite",
        "L'orateur invoque son voisin ingenieur comme expert absolu.",
        "arg_99",
    )  # cible fantôme -> check 2b
    m = compute_verdict_metrics(s)
    assert m["state_key_arguments"] == 1
    assert m["phantom_target_fallacies"] == 1
    assert m["validation_status"] == "INVALIDATED_FORM"
    assert m["failed_reason"] == "ARGUMENTS_STATE_KEY"


def test_verdict_failed_formal_when_no_meaningful_query():
    """Sans un seul verdict du moteur formel, le run est FAILED_FORMAL —
    pas COMPLETE_VALIDATED (port verbatim du durcissement du carnet 08b)."""
    from argumentation_lib._verdict import compute_verdict_metrics

    s = _state()
    s.add_argument(_substantive_arg_desc())
    s.add_argument("Donc le chat est a l'interieur selon le raisonnement du texte")
    _substantive_fallacy_add(s, target="arg_1")
    _substantive_fallacy_add(s, target="arg_2")
    s.add_belief_set("propositional", "Le chat est sur le paillasson.")
    s.query_log.append({"raw_result": "timeout"})  # soumis, non significatif
    s.final_conclusion = "Synthese du texte."
    m = compute_verdict_metrics(s)
    assert m["failed_reason"] == "QUERIES_NOT_MEANINGFUL"
    assert m["validation_status"] == "FAILED_FORMAL"


def test_resumption_hygiene_prunes_poisoned_entries():
    """Le nettoyage déterministe précède la porte : clé d'état et cible
    fantôme sont retirées AVANT tout remplissage (aucun ajout ne peut les
    éliminer), et l'entrée resumption_hygiene le rapporte."""
    s = _state()
    s.add_argument(_substantive_arg_desc())  # arg_1 substantif
    poisoned_id = s.add_argument("analysis_state")  # arg_2 : clé d'état
    _substantive_fallacy_add(s, target="arg_1")  # fallacy_1 valide
    phantom_id = s.add_fallacy(
        "Appel a l'autorite",
        "L'orateur invoque son voisin ingenieur comme expert absolu.",
        "arg_99",
    )
    runner = AnalysisRunner(
        _kernel(), "svc", s, targeted_resumption=True,
        min_substantive_arguments=1, min_substantive_fallacies=1,
    )
    out = _run(runner)
    hygiene = [p for p in out["phases"] if p["name"] == "resumption_hygiene"]
    assert len(hygiene) == 1
    assert hygiene[0]["state_key_arguments"] == [poisoned_id]
    assert hygiene[0]["phantom_target_fallacies"] == [phantom_id]
    assert poisoned_id not in s.identified_arguments
    assert phantom_id not in s.identified_fallacies
    # après purge les seuils 1/1 sont tenus : aucune phase de reprise
    names = [p["name"] for p in out["phases"]]
    assert names == ["informal", "resumption_hygiene", "formal", "synthesis"]
