# test_state_manager_plugin.py — tests for StateManagerPlugin (the @kernel_function wrapper layer)
#
# See #2137. Complements test_argumentation_state.py, which tests _shared_state
# (RhetoricalAnalysisState) directly. This file locks the CONTRACT of the
# Semantic-Kernel plugin surface that the analysis agents actually call:
#
#   - delegation: every @kernel_function forwards to the matching _state method
#   - validation: add_belief_set accepts only propositional/pl/fol/first_order
#     (case-insensitive) and rejects the rest with FUNC_ERROR
#   - parsing: NL->logic + phase writers parse their JSON string args
#   - JTMS shim: jtms_* always returns FUNC_ERROR (JTMS disabled in pedagogical
#     mode -- the methods `raise ImportError` as a deliberate shim)
#   - error handling: a _state method that raises is caught -> FUNC_ERROR /
#     {"error": ...}, never a crash propagating to the SK kernel
#
# semantic_kernel is NOT installed in coursia-ml-training (and must not be a
# hard dep of the shim -- see __init__.py lazy get_state_manager_plugin()). We
# install a minimal mock: @kernel_function becomes a no-op decorator that
# leaves the method callable. If the real semantic_kernel is present, the mock
# is skipped and the tests run against the real decorator (which also preserves
# callability).

from __future__ import annotations

import json
import logging
import os
import sys
from types import ModuleType

import pytest

# --- Make argumentation_lib importable regardless of pytest CWD -----------------
_THIS_DIR = os.path.dirname(os.path.abspath(__file__))
_ARGUMENT_ANALYSIS_DIR = os.path.dirname(_THIS_DIR)  # .../Argument_Analysis/
if _ARGUMENT_ANALYSIS_DIR not in sys.path:
    sys.path.insert(0, _ARGUMENT_ANALYSIS_DIR)


# --- Install a minimal semantic_kernel mock BEFORE importing the plugin ---------
def _install_sk_mock() -> None:
    """Mock semantic_kernel so _state_manager_plugin imports without the real dep.

    @kernel_function(description=..., name=...) is reduced to a no-op decorator
    that returns the function unchanged, leaving every plugin method directly
    callable from the test.
    """
    if "semantic_kernel" in sys.modules:
        return  # real semantic_kernel present -- nothing to mock

    sk = ModuleType("semantic_kernel")
    functions = ModuleType("semantic_kernel.functions")

    def kernel_function(*args, **kwargs):
        # Used both as @kernel_function (bare, args=(func,)) and as
        # @kernel_function(description=..., name=...) (kwargs only -> decorator).
        def decorator(func):
            return func

        # Bare form: first positional arg is the function being decorated.
        if args and callable(args[0]) and not kwargs:
            return args[0]
        return decorator

    functions.kernel_function = kernel_function
    sk.functions = functions
    sys.modules["semantic_kernel"] = sk
    sys.modules["semantic_kernel.functions"] = functions


_install_sk_mock()

from argumentation_lib._state_manager_plugin import StateManagerPlugin  # noqa: E402
from argumentation_lib import UnifiedAnalysisState  # noqa: E402

# NOTE on the state class: the plugin's ~25 @kernel_function methods span TWO
# layers of the shared state. The base RhetoricalAnalysisState provides the
# core (add_belief_set, log_query, add_argument, add_task, ...); the subclass
# UnifiedAnalysisState adds the formal-synthesis phase writers
# (add_nl_to_logic_translation, add_quality_score, add_dung_framework,
# add_counter_argument, set_workflow_results, ...). StateManagerPlugin targets
# the FULL surface, so its realistic target is UnifiedAnalysisState -- wrapping
# a bare RhetoricalAnalysisState silently works until a phase writer is called,
# which then returns FUNC_ERROR (AttributeError on the missing method). The
# agents in #2137 operate on a UnifiedAnalysisState, so we use it here.


# --- Fixtures ------------------------------------------------------------------


@pytest.fixture
def state() -> UnifiedAnalysisState:
    return UnifiedAnalysisState("Texte de test pour l'analyse argumentative.")


@pytest.fixture
def plugin(state: UnifiedAnalysisState) -> StateManagerPlugin:
    return StateManagerPlugin(state)


# --- Construction --------------------------------------------------------------


class TestConstruction:
    def test_holds_state_reference(self, plugin, state):
        # The plugin must keep the SAME state instance (single source of truth).
        assert plugin._state is state

    def test_has_logger(self, plugin):
        assert plugin._logger is not None


# --- Snapshot delegation -------------------------------------------------------


class TestSnapshot:
    def test_snapshot_summarized_returns_valid_json(self, plugin):
        result = plugin.get_current_state_snapshot(summarize=True)
        data = json.loads(result)  # must be valid JSON
        assert isinstance(data, dict)

    def test_snapshot_full_returns_valid_json(self, plugin):
        result = plugin.get_current_state_snapshot(summarize=False)
        data = json.loads(result)
        assert isinstance(data, dict)

    def test_snapshot_reflects_state_mutation(self, plugin, state):
        plugin.add_identified_argument("un argument specifique xyz")
        result = plugin.get_current_state_snapshot(summarize=False)
        # The argument text must appear verbatim in the full snapshot (the plugin
        # forwards to _state, which stores description under identified_arguments).
        assert "un argument specifique xyz" in result


# --- Task delegation -----------------------------------------------------------


class TestTasks:
    def test_add_analysis_task_returns_task_id(self, plugin):
        tid = plugin.add_analysis_task("Identifier les arguments")
        assert isinstance(tid, str)
        assert tid.startswith("task_")

    def test_mark_task_as_answered_returns_ok(self, plugin):
        tid = plugin.add_analysis_task("tache")
        result = plugin.mark_task_as_answered(tid, "reponse")
        assert "OK" in result

    def test_add_answer_returns_ok(self, plugin):
        tid = plugin.add_analysis_task("tache")
        result = plugin.add_answer(tid, "InformalAgent", "reponse", [])
        assert "OK" in result


# --- Argument + fallacy delegation --------------------------------------------


class TestArgumentsAndFallacies:
    def test_add_identified_argument(self, plugin):
        aid = plugin.add_identified_argument("argument 1")
        assert aid.startswith("arg_")

    def test_add_identified_arguments_list(self, plugin):
        result = plugin.add_identified_arguments(["a", "b", "c"])
        assert "OK" in result
        assert "3" in result  # count echoed back

    def test_add_identified_fallacy(self, plugin):
        fid = plugin.add_identified_fallacy("ad hominem", "attaque personnelle")
        assert fid.startswith("fallacy_")

    def test_add_identified_fallacies_list(self, plugin):
        fallacies = [{"type": "ad hominem", "justification": "j1"}]
        result = plugin.add_identified_fallacies(fallacies)
        assert "OK" in result


# --- belief_set logic_type VALIDATION (core contract) -------------------------


class TestBeliefSetValidation:
    @pytest.mark.parametrize(
        "logic_type",
        ["propositional", "pl", "PL", "Pl", "fol", "first_order", "First_Order"],
    )
    def test_valid_logic_types_accepted(self, plugin, logic_type):
        # Valid types delegate to _state and return an id (NOT FUNC_ERROR).
        result = plugin.add_belief_set(logic_type, "p OR q")
        assert not str(result).startswith("FUNC_ERROR"), (
            f"logic_type {logic_type!r} should be accepted"
        )

    @pytest.mark.parametrize("logic_type", ["modal", "temporal", "fuzzy", "", "PROB"])
    def test_invalid_logic_types_rejected(self, plugin, logic_type):
        result = plugin.add_belief_set(logic_type, "p")
        assert str(result).startswith("FUNC_ERROR")
        # The offending type is echoed in the error for agent debuggability.
        assert logic_type in result

    def test_invalid_type_message_lists_valid_keys(self, plugin):
        result = plugin.add_belief_set("modal", "p")
        # Agents read this to self-correct; the valid keys must be present.
        assert "propositional" in result
        assert "fol" in result


# --- NL -> logic translation (parsing) ----------------------------------------


class TestNLTranslation:
    @pytest.mark.parametrize("is_valid", ["true", "1", "yes", "True", "TRUE"])
    def test_is_valid_truthy_normalization(self, plugin, is_valid):
        result = plugin.add_nl_to_logic_translation(
            "texte", "p AND q", "propositional", is_valid, "{}", "0.9"
        )
        assert not str(result).startswith("FUNC_ERROR")

    def test_variables_json_string_parsed(self, plugin):
        result = plugin.add_nl_to_logic_translation(
            "texte", "p(x)", "fol", "true", '{"x": 1}', "0.8"
        )
        assert not str(result).startswith("FUNC_ERROR")

    def test_confidence_string_coerced_to_float(self, plugin):
        result = plugin.add_nl_to_logic_translation(
            "texte", "p", "pl", "true", "{}", "0.75"
        )
        assert not str(result).startswith("FUNC_ERROR")


# --- designate_next_agent + conclusion ----------------------------------------


class TestAgentDesignation:
    def test_designate_next_agent(self, plugin, state):
        result = plugin.designate_next_agent("LogicAgent")
        assert "OK" in result
        assert "LogicAgent" in result

    def test_set_final_conclusion(self, plugin):
        result = plugin.set_final_conclusion("Conclusion finale.")
        assert "OK" in result


# --- log_query delegation ------------------------------------------------------


class TestLogQuery:
    def test_log_query_result(self, plugin):
        bs_id = plugin.add_belief_set("propositional", "p OR q")
        result = plugin.log_query_result(bs_id, "p", "True")
        assert not str(result).startswith("FUNC_ERROR")


# --- JTMS shim: jtms_* must ALWAYS fail loud (pedagogical mode) ---------------


class TestJTMSShim:
    """The jtms_* kernel functions are shims: they `raise ImportError` to signal
    that JTMS is unavailable in CoursIA pedagogical mode. They must NEVER appear
    to succeed (that would be theatre -- selling a capability that isn't wired).
    """

    @pytest.mark.parametrize(
        "method,args",
        [
            ("jtms_create_belief", ("belief1",)),
            ("jtms_create_belief", ("belief1", "agent", 0.7)),
            ("jtms_add_justification", (["a"], ["b"], "c")),
            ("jtms_query_beliefs", ()),
            ("jtms_query_beliefs", ("agent1",)),
            ("jtms_check_consistency", ()),
            ("jtms_retract_belief", ("belief1", "fallacy: ...")),
        ],
    )
    def test_jtms_always_func_error(self, plugin, method, args):
        fn = getattr(plugin, method)
        result = fn(*args)
        assert "FUNC_ERROR" in str(result), (
            f"{method} must fail loud (JTMS shim), got: {result!r}"
        )


# --- Error handling: _state raising must be contained -------------------------


class _BoomState:
    """Minimal stand-in: the one method the plugin calls raises."""

    def __init__(self, boom_method: str):
        self._boom = boom_method

    def add_task(self, description):
        if self._boom == "add_task":
            raise RuntimeError("boom-add-task")
        return "task_0"


class TestErrorHandling:
    def test_add_task_exception_returns_func_error(self):
        plugin = StateManagerPlugin.__new__(StateManagerPlugin)
        plugin._state = _BoomState("add_task")
        plugin._logger = logging.getLogger("test.plugin")
        result = plugin.add_analysis_task("x")
        assert "FUNC_ERROR" in result
        assert "boom-add-task" in result

    def test_snapshot_exception_returns_error_json(self):
        class SnapBoom:
            def get_state_snapshot(self, summarize=False):
                raise ValueError("snap-corrupt")

        plugin = StateManagerPlugin.__new__(StateManagerPlugin)
        plugin._state = SnapBoom()
        plugin._logger = logging.getLogger("test.plugin")
        result = plugin.get_current_state_snapshot()
        data = json.loads(result)  # still valid JSON
        assert "error" in data
        assert "snap-corrupt" in data["error"]


# --- Phase-result writers (JSON string parsing contract) ----------------------


class TestPhaseWriters:
    def test_add_quality_score_ok(self, plugin):
        aid = plugin.add_identified_argument("arg")
        result = plugin.add_quality_score(aid, '{"clarity": 8}', "0.8")
        assert "OK" in result

    def test_add_quality_score_bad_json_func_error(self, plugin):
        aid = plugin.add_identified_argument("arg")
        result = plugin.add_quality_score(aid, "not-json{{", "0.5")
        assert "FUNC_ERROR" in result

    def test_add_dung_framework_ok(self, plugin):
        result = plugin.add_dung_framework(
            "debate1", '["a", "b"]', '[["a", "b"]]'
        )
        assert not str(result).startswith("FUNC_ERROR")

    def test_add_counter_argument_ok(self, plugin):
        result = plugin.add_counter_argument(
            "original", "counter", "rebuttal", "0.6"
        )
        assert not str(result).startswith("FUNC_ERROR")

    def test_set_workflow_results_ok(self, plugin):
        result = plugin.set_workflow_results("wf1", '{"steps": 3}')
        assert "OK" in result

    def test_set_workflow_results_bad_json_func_error(self, plugin):
        result = plugin.set_workflow_results("wf1", "not-json")
        assert "FUNC_ERROR" in result
