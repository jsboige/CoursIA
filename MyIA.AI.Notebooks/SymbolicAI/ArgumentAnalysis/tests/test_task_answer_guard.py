"""Tests du contrat « reponse sur tache inexistante » de GuardedStateManagerPlugin (See #23726).

Le plugin StateManager et l'etat `RhetoricalAnalysisState` sont des copies
VERBATIM de l'amont EPITA (cf `_guarded_state.py`, NOTICE-EPITA) : le
comportement amont — avertir puis jeter la reponse (`mark_task_as_answered`)
ou avertir puis ecrire sous la tache fantome (`add_answer`) — n'est PAS
modifiable chez nous. La garde vit dans `GuardedStateManagerPlugin`, le
point d'extension CoursIA (deja utilise par #22981 pour `log_query_result`).

Ces tests prouvent le contrat demande par #23726 :
- une reponse sur tache inexistante est REFUSEE explicitement (FUNC_ERROR
  diagnostiquable, identifiants connus listes) — jamais perdue en silence ;
- aucune ecriture sous une tache fantome (`state.answers` reste propre) ;
- une reponse sur tache EXISTANTE delegue au verbatim et est enregistree.

Le dernier test egalement le comportement du bloc verbatim lui-meme :
il reste « warning + perte silencieuse » — ce pin detecte un changement
amont lors d'une re-vendorisation (si l'amont corrige, la garde devient
redondante et ce test rougit : aller voir).
"""

from __future__ import annotations

import os
import sys

import pytest

_TESTS_DIR = os.path.dirname(os.path.abspath(__file__))
_ARG_ANALYSIS_DIR = os.path.dirname(_TESTS_DIR)
if _ARG_ANALYSIS_DIR not in sys.path:
    sys.path.insert(0, _ARG_ANALYSIS_DIR)


def _install_sk_mock() -> None:
    """Mock semantic_kernel si absent (helper des voisins, #24974).

    `_guarded_state` importe `semantic_kernel.functions.kernel_function` au
    niveau module : sans SK installe, l'import du fichier seul echoue. Meme
    strategie que `test_pl_verdict_contract.py:32-54`.
    """
    if "semantic_kernel" in sys.modules:
        return

    from types import ModuleType

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

from argumentation_lib._guarded_state import GuardedStateManagerPlugin  # noqa: E402
from argumentation_lib._shared_state import RhetoricalAnalysisState  # noqa: E402


def _guarded() -> tuple[GuardedStateManagerPlugin, RhetoricalAnalysisState]:
    state = RhetoricalAnalysisState("texte de test")
    state.add_task("analyse informelle du texte")
    plugin = GuardedStateManagerPlugin(state)
    return plugin, state


class TestMarkTaskAsAnswered:
    def test_unknown_task_is_refused_not_lost(self):
        """Tache inexistante : FUNC_ERROR diagnostiquable, reponse jamais ecrite."""
        plugin, state = _guarded()
        result = plugin.mark_task_as_answered("task_999", "ma reponse")
        assert result.startswith("FUNC_ERROR")
        assert "task_999" in result  # l'agent voit QUEL id est fautif
        assert "task_1" in result  # ...et quels ids existent
        assert "task_999" not in state.answers

    def test_known_task_delegates_and_records(self):
        """Tache existante : delegation au verbatim, reponse enregistree."""
        plugin, state = _guarded()
        result = plugin.mark_task_as_answered("task_1", "ma reponse")
        assert result.startswith("OK")
        assert state.answers["task_1"]["answer_text"] == "ma reponse"


class TestAddAnswer:
    def test_unknown_task_is_refused_without_phantom_write(self):
        """Tache inexistante : refus AVANT delegation — le verbatim n'ecrit pas.

        Sans la garde, le verbatim amont avertit puis ecrit quand meme la
        reponse sous la tache fantomme (pollution de l'etat) : ce test epingle
        les deux a la fois — refus explicite ET absence d'ecriture.
        """
        plugin, state = _guarded()
        result = plugin.add_answer("task_999", "agent_x", "reponse", ["arg_1"])
        assert result.startswith("FUNC_ERROR")
        assert "task_999" not in state.answers

    def test_known_task_delegates_and_records(self):
        plugin, state = _guarded()
        result = plugin.add_answer("task_1", "agent_x", "reponse", ["arg_1"])
        assert result.startswith("OK")
        entry = state.answers["task_1"]
        assert entry["author_agent"] == "agent_x"
        assert entry["source_ids"] == ["arg_1"]


class TestVerbatimBlockPinned:
    def test_verbatim_state_still_silently_drops_unknown_task(self):
        """Pin du bloc verbatim : il reste « warning + perte silencieuse ».

        Ce comportement amont est la RAISON d'etre de la garde aval. Si ce
        test rougit, l'amont a change (re-vendor) : la garde est peut-etre
        devenue redondante — verifier NOTICE-EPITA avant d'ajuster.
        """
        state = RhetoricalAnalysisState("texte")
        state.mark_task_as_answered("task_999", "reponse")  # ne leve pas (verbatim)
        assert "task_999" not in state.answers
