# test_pl_verdict_contract.py — le contrat de verdict moteur de la phase formelle
#
# Voir #22981. Le carnet `Argumentation-08b-Executor-Python.ipynb` a consigne,
# sur deux runs independants et deux generations de modele, 2 requetes en
# langage naturel et 0 verdict : le contrat d'appel exigeait l'APPEL de
# `log_query_result`, pas un VERDICT de moteur.
#
# Ce fichier verrouille le contrat correctif :
#   - `split_formulas` : decoupage du contenu d'un belief set
#   - `VerdictRegistry` : un verdict existe seulement s'il a ete EMIS
#   - `GuardedStateManagerPlugin.log_query_result` : refus d'une phrase libre
#   - `PLReasonerPlugin.pl_query` : le SEUL chemin d'obtention d'un verdict
#   - integration : le VRAI solveur Tweety (marquee, sautee sans les jars)
#
# semantic_kernel n'est pas une dependance dure de la shim : on installe le
# meme mock minimal que `test_state_manager_plugin.py`.

from __future__ import annotations

import os
import sys
from types import ModuleType

import pytest

_THIS_DIR = os.path.dirname(os.path.abspath(__file__))
_ARGUMENT_ANALYSIS_DIR = os.path.dirname(_THIS_DIR)
if _ARGUMENT_ANALYSIS_DIR not in sys.path:
    sys.path.insert(0, _ARGUMENT_ANALYSIS_DIR)


def _install_sk_mock() -> None:
    """Mock semantic_kernel si absent (meme strategie que le test d'origine)."""
    if "semantic_kernel" in sys.modules:
        return

    sk = ModuleType("semantic_kernel")
    functions = ModuleType("semantic_kernel.functions")

    def kernel_function(*args, **kwargs):
        def decorator(func):
            return func

        if args and callable(args[0]) and not kwargs:
            return args[0]
        return decorator

    functions.kernel_function = kernel_function
    sk.functions = functions
    sys.modules["semantic_kernel"] = sk
    sys.modules["semantic_kernel.functions"] = functions


_install_sk_mock()

from argumentation_lib import UnifiedAnalysisState  # noqa: E402
from argumentation_lib._guarded_state import GuardedStateManagerPlugin  # noqa: E402
from argumentation_lib._pl_reasoner import (  # noqa: E402
    EngineUnavailableError,
    FormulaSyntaxError,
    PLReasonerPlugin,
    split_formulas,
)
from argumentation_lib._pl_verdict import (  # noqa: E402
    ACCEPTED,
    REJECTED,
    VerdictRegistry,
    format_verdict,
    is_verdict,
    normalize,
    registry_for,
)


class FakeEngine:
    """Faux moteur : permet de tester le contrat sans JVM."""

    name = "fake-engine"

    def __init__(self, entails: bool = True, error: Exception | None = None):
        self._entails = entails
        self._error = error
        self.calls: list[tuple[tuple[str, ...], str]] = []

    def entails(self, formulas, query):
        self.calls.append((tuple(formulas), query))
        if self._error is not None:
            raise self._error
        return self._entails


@pytest.fixture
def state() -> UnifiedAnalysisState:
    return UnifiedAnalysisState("Texte de test pour l'analyse argumentative.")


# --- Decoupage des formules ----------------------------------------------------


class TestSplitFormulas:
    def test_one_formula_per_line(self):
        assert split_formulas("p => q\np") == ["p => q", "p"]

    def test_semicolon_separator(self):
        assert split_formulas("p => q ; p") == ["p => q", "p"]

    def test_blank_lines_ignored(self):
        assert split_formulas("  \n\n p => q \n") == ["p => q"]

    def test_empty_content(self):
        assert split_formulas("") == []


# --- Registre des verdicts ------------------------------------------------------


class TestVerdictRegistry:
    def test_record_then_get(self):
        registry = VerdictRegistry()
        verdict = format_verdict("bs_1", "q", True, "engine")
        registry.record("bs_1", "q", verdict)
        assert registry.get("bs_1", "q") == verdict

    def test_get_unknown_returns_none(self):
        assert VerdictRegistry().get("bs_1", "q") is None

    def test_whitespace_normalized_on_lookup(self):
        registry = VerdictRegistry()
        verdict = format_verdict("bs_1", "q", True, "engine")
        registry.record("bs_1", "q", verdict)
        assert registry.get("bs_1", "  q \n") == verdict

    def test_natural_language_is_not_a_verdict(self):
        registry = VerdictRegistry()
        registry.record("bs_1", "q", format_verdict("bs_1", "q", True, "engine"))
        assert not registry.is_engine_verdict(
            "bs_1", "q", "Les inferences principales sont-elles valides ?"
        )

    def test_verdict_of_another_belief_set_is_refused(self):
        registry = VerdictRegistry()
        registry.record("bs_1", "q", format_verdict("bs_1", "q", True, "engine"))
        assert not registry.is_engine_verdict(
            "bs_2", "q", format_verdict("bs_1", "q", True, "engine")
        )

    def test_format_verdict_starts_with_the_marker(self):
        verdict = format_verdict("bs_1", "q", True, "engine")
        assert verdict.startswith(ACCEPTED + ":")
        assert is_verdict(verdict)
        assert not is_verdict("une question ?")
        assert format_verdict("bs_1", "q", False, "engine").startswith(REJECTED + ":")

    def test_normalize(self):
        assert normalize(" a  b \n c ") == "a b c"

    def test_registry_for_is_scoped_per_state(self):
        first = UnifiedAnalysisState("a")
        second = UnifiedAnalysisState("b")
        assert registry_for(first) is registry_for(first)
        assert registry_for(first) is not registry_for(second)


# --- Garde de consignation ------------------------------------------------------


class TestGuardedStateManager:
    def test_natural_language_query_is_refused(self, state):
        plugin = GuardedStateManagerPlugin(state)
        bs_id = state.add_belief_set("Propositional", "p => q")
        result = plugin.log_query_result(
            bs_id, "Les inferences sont-elles valides ?", "Les inferences sont valides"
        )
        assert result.startswith("FUNC_ERROR")
        assert state.query_log == []

    def test_engine_verdict_is_recorded(self, state):
        plugin = GuardedStateManagerPlugin(state)
        bs_id = state.add_belief_set("Propositional", "p => q")
        verdict = format_verdict(bs_id, "q", True, "fake-engine")
        registry_for(state).record(bs_id, "q", verdict)
        log_id = plugin.log_query_result(bs_id, "q", verdict)
        assert not log_id.startswith("FUNC_ERROR")
        assert len(state.query_log) == 1
        assert state.query_log[0]["raw_result"] == verdict

    def test_verdict_from_another_belief_set_is_refused(self, state):
        plugin = GuardedStateManagerPlugin(state)
        bs_id = state.add_belief_set("Propositional", "p => q")
        other_id = state.add_belief_set("Propositional", "r => s")
        verdict = format_verdict(other_id, "s", True, "fake-engine")
        registry_for(state).record(other_id, "s", verdict)
        result = plugin.log_query_result(bs_id, "q", verdict)
        assert result.startswith("FUNC_ERROR")
        assert state.query_log == []


# --- Plugin solveur -------------------------------------------------------------


class TestPLReasonerPlugin:
    def test_unknown_belief_set(self, state):
        plugin = PLReasonerPlugin(state, engine=FakeEngine())
        result = plugin.pl_query("bs_inconnu", "q")
        assert result.startswith("FUNC_ERROR")
        assert "bs_inconnu" in result

    def test_empty_belief_set(self, state):
        plugin = PLReasonerPlugin(state, engine=FakeEngine())
        bs_id = state.add_belief_set("Propositional", "   ")
        result = plugin.pl_query(bs_id, "q")
        assert result.startswith("FUNC_ERROR")

    def test_entailed_returns_accepted_and_records(self, state):
        plugin = PLReasonerPlugin(state, engine=FakeEngine(entails=True))
        bs_id = state.add_belief_set("Propositional", "p => q\np")
        verdict = plugin.pl_query(bs_id, "q")
        assert verdict.startswith(ACCEPTED + ":")
        assert registry_for(state).get(bs_id, "q") == verdict

    def test_not_entailed_returns_rejected(self, state):
        plugin = PLReasonerPlugin(state, engine=FakeEngine(entails=False))
        bs_id = state.add_belief_set("Propositional", "p => q\np")
        verdict = plugin.pl_query(bs_id, "!q")
        assert verdict.startswith(REJECTED + ":")

    def test_formulas_are_passed_to_the_engine(self, state):
        engine = FakeEngine(entails=True)
        plugin = PLReasonerPlugin(state, engine=engine)
        bs_id = state.add_belief_set("Propositional", "p => q\np")
        plugin.pl_query(bs_id, "q")
        assert engine.calls == [(("p => q", "p"), "q")]

    def test_syntax_error_is_reported(self, state):
        engine = FakeEngine(error=FormulaSyntaxError("p -> q", "General parsing error"))
        plugin = PLReasonerPlugin(state, engine=engine)
        bs_id = state.add_belief_set("Propositional", "p -> q")
        result = plugin.pl_query(bs_id, "q")
        assert result.startswith("FUNC_ERROR")
        assert "=>" in result  # la syntaxe attendue est rappelee

    def test_engine_unavailable_is_reported(self, state):
        engine = FakeEngine(error=EngineUnavailableError("JVM absente"))
        plugin = PLReasonerPlugin(state, engine=engine)
        bs_id = state.add_belief_set("Propositional", "p => q")
        result = plugin.pl_query(bs_id, "q")
        assert result.startswith("FUNC_ERROR")
        assert "JVM absente" in result

    def test_verdict_is_accepted_by_the_guard(self, state):
        plugin = PLReasonerPlugin(state, engine=FakeEngine(entails=True))
        guard = GuardedStateManagerPlugin(state)
        bs_id = state.add_belief_set("Propositional", "p => q\np")
        verdict = plugin.pl_query(bs_id, "q")
        log_id = guard.log_query_result(bs_id, "q", verdict)
        assert not log_id.startswith("FUNC_ERROR")
        assert state.query_log[0]["raw_result"].startswith(ACCEPTED + ":")


# --- Integration avec le VRAI solveur --------------------------------------------
#
# La JVM est demarree dans un SOUS-PROCESSUS, pas dans le processus pytest :
# sous pytest, `jpype.startJVM` declenche une « Windows fatal exception:
# access violation » qui tue la session de test entiere (mesure du 28/10 sur
# `epita_symbolic_ai`/Python 3.10 : 26 tests verts puis arret du process).
# Isoler la JVM dans un enfant rend l'echec visible (le test echoue avec la
# sortie de l'enfant) sans emporter le reste de la suite.


_SOLVER_PROBE = r"""
import sys

sys.path.insert(0, sys.argv[1])

from argumentation_lib import UnifiedAnalysisState
from argumentation_lib._guarded_state import GuardedStateManagerPlugin
from argumentation_lib._pl_reasoner import PLReasonerPlugin

state = UnifiedAnalysisState("texte")
plugin = PLReasonerPlugin(state)
guard = GuardedStateManagerPlugin(state)
bs_id = state.add_belief_set("Propositional", "rain => wet\nrain")
wet = plugin.pl_query(bs_id, "wet")
not_wet = plugin.pl_query(bs_id, "!wet")
log_id = guard.log_query_result(bs_id, "wet", wet)
print("WET=" + wet)
print("NOTWET=" + not_wet)
print("GUARD=" + log_id)
"""


def _tweety_jars_present() -> bool:
    """Vrai si les jars Tweety sont provisions (ils ne sont pas versionnes)."""
    try:
        from argumentation_lib._paths import get_tweety_jar_dir

        jar_dir = get_tweety_jar_dir()
        return bool(jar_dir) and os.path.isdir(str(jar_dir))
    except Exception:
        return False


@pytest.mark.skipif(
    not _tweety_jars_present(),
    reason="jars Tweety absents : provisionner via "
    "Tweety/scripts/download_tweety_tools.py --jars --jdk",
)
def test_real_tweety_solver_in_subprocess():
    """Le solveur REEL decide (mandat anti-theatre #2137).

    Modus ponens : `wet` est entail (ACCEPTED), `!wet` ne l'est pas
    (REJECTED) ; le verdict du solveur est accepte par la garde.
    """
    import subprocess

    proc = subprocess.run(
        [sys.executable, "-c", _SOLVER_PROBE, _ARGUMENT_ANALYSIS_DIR],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        timeout=600,
    )
    assert proc.returncode == 0, (
        f"le solveur a echoue (rc={proc.returncode})\n"
        f"stdout:\n{proc.stdout[-2000:]}\nstderr:\n{proc.stderr[-2000:]}"
    )
    assert "WET=" + ACCEPTED + ":" in proc.stdout, proc.stdout
    assert "NOTWET=" + REJECTED + ":" in proc.stdout, proc.stdout
    assert "GUARD=FUNC_ERROR" not in proc.stdout, proc.stdout
    assert "GUARD=qlog" in proc.stdout, proc.stdout
