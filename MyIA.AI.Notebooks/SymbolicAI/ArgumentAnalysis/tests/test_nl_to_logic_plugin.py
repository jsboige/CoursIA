"""Tests for argumentation_lib._nl_to_logic_plugin (See #18390).

Verifies the NLToLogicPlugin adapter: LLM translation text->PL validated
by the real parser.

Trois familles de tests :
- le chemin nominal (traduction, filtrage, requetes) sur un service factice ;
- le CONTRAT `settings=` d'un service SK (B1 de la revue de #24951) : une
  instance, jamais le dict `{service_id: settings}` de `KernelArguments` ;
- la cohabitation avec `test_runner.py` dans un meme processus (B2) : ce
  fichier installe un mock SK minimal, `test_runner.py` un mock complet, et
  l'ordre de collecte pytest ne doit pas casser la collecte de l'autre.

Incident CI (gate de #24951, 2026-11-06) : `importorskip("semantic_kernel")`
passait TOUJOURS dans ce processus — le mock de `_ensure_sk_importable`
satisfait l'import — alors que la probe du contrat reel execute un
sous-processus propre ou le vrai paquet est absent du runner CPU
(`ModuleNotFoundError`). La disponibilite se sonde desormais dans un
sous-processus propre avant la probe : skip honnete la ou l'outil est absent
(meme garde que `_tweety_jars_present` pour le solveur), echec reel ailleurs.
"""
from __future__ import annotations

import asyncio
import json
import os
import subprocess
import sys
from collections.abc import Mapping
from types import ModuleType, SimpleNamespace

import pytest

# Make `argumentation_lib` importable
_TESTS_DIR = os.path.dirname(os.path.abspath(__file__))
_ARG_ANALYSIS_DIR = os.path.dirname(_TESTS_DIR)
if _ARG_ANALYSIS_DIR not in sys.path:
    sys.path.insert(0, _ARG_ANALYSIS_DIR)


def _ensure_sk_importable():
    """Rendre importables les symboles SK dont depend le plugin, sans ecraser.

    Deux situations, dans cet ordre :
    1. un mock SK est deja en place et porte `contents.chat_history` (cas de
       `test_runner.py` collecte avant ce fichier) -> on le reutilise tel quel ;
    2. sinon -> mock minimal, en COMPLETANT les modules deja presents.

    Ce fichier ne lit JAMAIS le vrai Semantic Kernel, meme quand il est
    installe : le laisser importer le vrai paquet laissait ses sous-modules
    dans `sys.modules`, que `test_runner.py` heritait ensuite — le mock du
    runner n'etait plus maitre du processus et 37 de ses tests rougissaient
    (mesure sur la collecte naturelle). Le contrat `settings=` du VRAI SK est
    verifie dans un sous-processus propre (`test_real_sk_contract_...`), ou
    aucune contamination croisee n'est possible.

    Ce fichier ne pose JAMAIS `_coursia_mock` : ce drapeau designe le mock
    complet du runner, et le poser ici faisait sauter son garde, qui heritait
    alors d'un mock tronque (`ImportError: cannot import name 'Kernel'`) et
    perdait toute sa suite (B2 de la revue de #24951).
    """
    if "semantic_kernel.contents.chat_history" in sys.modules:
        mod_hist = sys.modules["semantic_kernel.contents.chat_history"]
        if hasattr(mod_hist, "ChatHistory") and hasattr(
            sys.modules.get("semantic_kernel.functions"), "kernel_function"
        ):
            return

    sk = sys.modules.get("semantic_kernel") or ModuleType("semantic_kernel")

    functions = sys.modules.get("semantic_kernel.functions") or ModuleType(
        "semantic_kernel.functions"
    )
    if not hasattr(functions, "kernel_function"):

        def kernel_function(*args, **kwargs):
            def decorator(func):
                return func

            if args and callable(args[0]) and not kwargs:
                return args[0]
            return decorator

        functions.kernel_function = kernel_function

    contents = sys.modules.get("semantic_kernel.contents") or ModuleType(
        "semantic_kernel.contents"
    )
    mod_hist = sys.modules.get("semantic_kernel.contents.chat_history") or ModuleType(
        "semantic_kernel.contents.chat_history"
    )
    if not hasattr(mod_hist, "ChatHistory"):

        class ChatHistory:
            def __init__(self):
                self.messages = []

            def add_user_message(self, content):
                self.messages.append(content)

        mod_hist.ChatHistory = ChatHistory

    contents.chat_history = mod_hist
    sk.functions = functions
    sk.kernel_function = functions.kernel_function
    sk.contents = contents

    for name, mod in {
        "semantic_kernel": sk,
        "semantic_kernel.functions": functions,
        "semantic_kernel.contents": contents,
        "semantic_kernel.contents.chat_history": mod_hist,
    }.items():
        sys.modules[name] = mod


_ensure_sk_importable()

from argumentation_lib._nl_to_logic_plugin import NLToLogicPlugin  # noqa: E402
from argumentation_lib._pl_reasoner import EngineUnavailableError  # noqa: E402


# ---------------------------------------------------------------------------
# Fake LLM services
# ---------------------------------------------------------------------------

_TRANSLATION_RESPONSE = json.dumps({
    "propositions": ["socrates_man", "socrates_mortal"],
    "formulas": ["socrates_man", "socrates_man => socrates_mortal"],
})

_QUERIES_RESPONSE = json.dumps({
    "query_ideas": ["socrates_mortal"],
})


class FakeChatService:
    """Fake AIChatCompletion returning canned responses.

    `settings` est optionnel ici : ces tests portent sur la traduction, pas sur
    le contrat de reglages. Les tests de contrat utilisent `StrictChatService`.
    """

    def __init__(self, responses):
        self._responses = list(responses)
        self.seen_settings = []
        self._prompts = []

    async def get_chat_message_contents(self, chat_history, settings=None, **kwargs):
        self.seen_settings.append(settings)
        self._prompts.append("".join(str(m) for m in getattr(chat_history, "messages", [])))
        content = self._responses.pop(0) if self._responses else "{}"
        return [SimpleNamespace(content=content)]


class StrictChatService:
    """Service dont la signature est celle de SK 1.44.

    `settings` est un parametre OBLIGATOIRE et doit etre une INSTANCE : c'est
    la coercition de SK qui echoue sur un dict (`pack_extension_data`). Le fake
    permissif (`**kwargs` sans `settings`) ne pouvait structurellement pas voir
    B1 — ce service-la le voit.
    """

    def __init__(self, responses):
        self._responses = list(responses)
        self.seen_settings = []

    async def get_chat_message_contents(self, chat_history, settings, **kwargs):
        if isinstance(settings, Mapping):
            # Ce que SK leve lui-meme sur un dict de KernelArguments.
            raise AttributeError("'dict' object has no attribute 'pack_extension_data'")
        self.seen_settings.append(settings)
        content = self._responses.pop(0) if self._responses else "{}"
        return [SimpleNamespace(content=content)]


class FactoryChatService:
    """Service exposant `get_prompt_execution_settings_class` (comme SK)."""

    class _Settings:
        pass

    def __init__(self, responses):
        self._responses = list(responses)
        self.seen_settings = []

    @classmethod
    def get_prompt_execution_settings_class(cls):
        return cls._Settings

    async def get_chat_message_contents(self, chat_history, settings, **kwargs):
        if isinstance(settings, Mapping):
            raise AttributeError("'dict' object has no attribute 'pack_extension_data'")
        self.seen_settings.append(settings)
        content = self._responses.pop(0) if self._responses else "{}"
        return [SimpleNamespace(content=content)]


def _fake_parse_ok(formula):
    """Accept any formula (simulates Tweety PlParser)."""
    return formula


def _fake_parse_reject_arrow(formula):
    """Reject formulas containing '->' (simulates Tweety refusing '->')."""
    if "->" in formula:
        raise ValueError(f"General parsing error: {formula}")
    return formula


def _fake_parse_engine_down(formula):
    """Simule une JVM / des jars absents (panne d'environnement)."""
    raise EngineUnavailableError("JVM/Tweety indisponible : jdk-17-portable absent")


# ---------------------------------------------------------------------------
# Tests — chemin nominal
# ---------------------------------------------------------------------------


def test_translate_to_pl_happy_path():
    """Translation returns propositions + validated formulas."""
    service = FakeChatService([_TRANSLATION_RESPONSE])
    plugin = NLToLogicPlugin(llm_service=service, parse_fn=_fake_parse_ok)
    result = json.loads(asyncio.run(plugin.translate_to_pl("Socrate est un homme.")))
    assert result["propositions"] == ["socrates_man", "socrates_mortal"]
    assert "socrates_man" in result["formulas"]
    assert "socrates_man => socrates_mortal" in result["formulas"]
    assert result["rejected"] == []


def test_translate_to_pl_rejects_bad_syntax():
    """Formulas refused by the parser land in `rejected`."""
    response = json.dumps({
        "propositions": ["a", "b"],
        "formulas": ["a", "a -> b"],
    })
    service = FakeChatService([response])
    plugin = NLToLogicPlugin(llm_service=service, parse_fn=_fake_parse_reject_arrow)
    result = json.loads(asyncio.run(plugin.translate_to_pl("test")))
    assert "a" in result["formulas"]
    assert "a -> b" not in result["formulas"]
    assert len(result["rejected"]) == 1
    assert result["rejected"][0]["formula"] == "a -> b"


def test_translate_to_pl_filters_undeclared_propositions():
    """Formulas using undeclared propositions are filtered out."""
    response = json.dumps({
        "propositions": ["a"],
        "formulas": ["a", "b"],
    })
    service = FakeChatService([response])
    plugin = NLToLogicPlugin(llm_service=service, parse_fn=_fake_parse_ok)
    result = json.loads(asyncio.run(plugin.translate_to_pl("test")))
    assert "a" in result["formulas"]
    assert "b" not in result["formulas"]


def test_generate_queries_consumes_translate_output():
    """Enchainement reel des deux fonctions : la sortie de l'une nourrit l'autre.

    C'est l'appel de production : l'agent passe a `generate_queries` le JSON
    serialise que `translate_to_pl` vient de rendre (deux cles, pas les listes
    a la main). La reserve de revue portait sur l'absence de ce lien.
    """
    service = FakeChatService([_TRANSLATION_RESPONSE, _QUERIES_RESPONSE])
    plugin = NLToLogicPlugin(llm_service=service, parse_fn=_fake_parse_ok)

    translation = asyncio.run(plugin.translate_to_pl("Socrate est un homme."))
    parsed = json.loads(translation)

    queries = json.loads(asyncio.run(plugin.generate_queries(
        "Socrate est un homme.",
        json.dumps(parsed["propositions"], ensure_ascii=False),
        json.dumps(parsed["formulas"], ensure_ascii=False),
    )))
    assert queries == ["socrates_mortal"]
    # le second appel porte bien le belief set issu du premier dans son prompt
    assert "socrates_man => socrates_mortal" in service._prompts[-1]


def test_generate_queries():
    """Query generation returns a list of formulas."""
    service = FakeChatService([_QUERIES_RESPONSE])
    plugin = NLToLogicPlugin(llm_service=service, parse_fn=_fake_parse_ok)
    result = json.loads(asyncio.run(plugin.generate_queries(
        "Socrate est mortel.",
        '["socrates_man", "socrates_mortal"]',
        '["socrates_man", "socrates_man => socrates_mortal"]',
    )))
    assert "socrates_mortal" in result


def test_plugin_construction_requires_service_and_parser():
    """Missing collaborators are refused before an agent can use the plugin."""
    with pytest.raises(ValueError, match="llm_service"):
        NLToLogicPlugin(llm_service=None, parse_fn=_fake_parse_ok)
    with pytest.raises(TypeError, match="parse_fn"):
        NLToLogicPlugin(llm_service=FakeChatService([]), parse_fn=None)

    service = FakeChatService([_TRANSLATION_RESPONSE])
    plugin = NLToLogicPlugin(llm_service=service, parse_fn=_fake_parse_ok)
    assert plugin._llm_service is service
    assert plugin._parse_fn is _fake_parse_ok


# ---------------------------------------------------------------------------
# Tests — contrat `settings=` d'un service SK (B1 de la revue de #24951)
# ---------------------------------------------------------------------------


def test_chat_passes_settings_instance_unchanged():
    """L'instance injectee arrive TELLE QUELLE au service (identite)."""
    settings = SimpleNamespace(reasoning_effort="none")
    service = StrictChatService([_TRANSLATION_RESPONSE])
    plugin = NLToLogicPlugin(
        llm_service=service, parse_fn=_fake_parse_ok, execution_settings=settings
    )
    asyncio.run(plugin.translate_to_pl("test"))
    assert service.seen_settings == [settings]
    assert service.seen_settings[0] is settings


def test_plugin_refuses_kernel_arguments_settings_dict():
    """La forme `{service_id: settings}` de KernelArguments est refusee net.

    C'est la forme que `_execution_settings_for` rend : la passer faisait
    echouer tout appel (`'dict' object has no attribute 'pack_extension_data'`).
    Le refus a la construction rend le contrat impossible a re-perdre.
    """
    settings_map = {"global_llm_service": SimpleNamespace(reasoning_effort="none")}
    with pytest.raises(TypeError, match="KernelArguments"):
        NLToLogicPlugin(
            llm_service=StrictChatService([]),
            parse_fn=_fake_parse_ok,
            execution_settings=settings_map,
        )


def test_chat_builds_settings_from_service_factory():
    """Sans instance injectee, l'instance vient de la fabrique du service.

    Ni la classe, ni un dict : une instance. C'est le chemin nominal d'un
    service SK reel (`get_prompt_execution_settings_class`).
    """
    service = FactoryChatService([_TRANSLATION_RESPONSE])
    plugin = NLToLogicPlugin(llm_service=service, parse_fn=_fake_parse_ok)
    asyncio.run(plugin.translate_to_pl("test"))
    assert len(service.seen_settings) == 1
    assert isinstance(service.seen_settings[0], FactoryChatService._Settings)


_REAL_SK_PROBE = r"""
import asyncio, json, sys
from types import SimpleNamespace

from semantic_kernel.connectors.ai.prompt_execution_settings import (
    PromptExecutionSettings,
)

from argumentation_lib._nl_to_logic_plugin import NLToLogicPlugin


class StrictService:
    # signature de SK 1.44 : `settings` obligatoire, instance attendue
    def __init__(self):
        self.seen = []

    async def get_chat_message_contents(self, chat_history, settings, **kwargs):
        if isinstance(settings, dict):
            raise AttributeError(
                "'dict' object has no attribute 'pack_extension_data'"
            )
        self.seen.append(settings)
        return [SimpleNamespace(content=json.dumps({"propositions": ["a"], "formulas": ["a"]}))]


service = StrictService()
plugin = NLToLogicPlugin(llm_service=service, parse_fn=lambda f: f)
asyncio.run(plugin.translate_to_pl("test"))
assert len(service.seen) == 1, service.seen
assert isinstance(service.seen[0], PromptExecutionSettings), type(service.seen[0])
print("REAL_SK_OK")
"""


def test_real_sk_contract_settings_is_an_instance():
    """Contre le VRAI Semantic Kernel : `settings` est une instance, pas un dict.

    Execute dans un sous-processus propre : dans ce processus-ci, SK est
    mocke (cf `_ensure_sk_importable`), et le vrai paquet doit rester hors du
    `sys.modules` partage. C'est la verification que B1 demandait — un helper
    qui rendrait `{service_id: settings}` echoue ici a l'assertion d'instance.
    """
    # `importorskip` ne suffit pas ici : ce processus mocke SK
    # (`_ensure_sk_importable`), donc l'import reussit meme sans le vrai
    # paquet — alors que la probe ci-dessous l'exige, VRAI. La disponibilite
    # se sonde dans un sous-processus propre (meme garde que
    # `_tweety_jars_present` pour le solveur : le contrat reel ne se joue
    # que la ou l'outil est reellement installe).
    _probe_env = dict(os.environ)
    _probe_env["PYTHONPATH"] = os.pathsep.join(
        filter(None, [_ARG_ANALYSIS_DIR, _probe_env.get("PYTHONPATH")])
    )
    _availability = subprocess.run(
        [sys.executable, "-c", "import semantic_kernel"],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        cwd=_ARG_ANALYSIS_DIR,
        env=_probe_env,
        timeout=120,
    )
    if _availability.returncode != 0:
        pytest.skip(
            "vrai semantic_kernel absent de cet environnement (sonde en "
            "sous-processus propre, hors mock) : le contrat settings= ne peut "
            "pas etre verifie contre le vrai paquet ici"
        )
    env = dict(os.environ)
    env["PYTHONPATH"] = os.pathsep.join(
        filter(None, [_ARG_ANALYSIS_DIR, env.get("PYTHONPATH")])
    )
    proc = subprocess.run(
        [sys.executable, "-c", _REAL_SK_PROBE],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        cwd=_ARG_ANALYSIS_DIR,
        env=env,
        timeout=300,
    )
    assert "REAL_SK_OK" in proc.stdout, (proc.stdout + proc.stderr)[-3000:]


# ---------------------------------------------------------------------------
# Tests — une panne de moteur n'est pas un rejet pedagogique (P1)
# ---------------------------------------------------------------------------


def test_engine_unavailable_propagates_instead_of_being_rejected():
    """Une JVM absente remonte, elle ne se deguise pas en refus de syntaxe."""
    service = FakeChatService([_TRANSLATION_RESPONSE])
    plugin = NLToLogicPlugin(llm_service=service, parse_fn=_fake_parse_engine_down)
    with pytest.raises(EngineUnavailableError, match="indisponible"):
        asyncio.run(plugin.translate_to_pl("Socrate est un homme."))


def test_syntax_error_still_lands_in_rejected():
    """Le rejet de syntaxe, lui, reste une information pedagogique."""
    response = json.dumps({"propositions": ["a"], "formulas": ["a -> a"]})
    service = FakeChatService([response])
    plugin = NLToLogicPlugin(llm_service=service, parse_fn=_fake_parse_reject_arrow)
    result = json.loads(asyncio.run(plugin.translate_to_pl("test")))
    assert result["formulas"] == []
    assert len(result["rejected"]) == 1


# ---------------------------------------------------------------------------
# Test — cohabitation des deux mocks SK dans un meme processus (B2)
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("order", ["nl_then_runner", "runner_then_nl"])
def test_both_sk_mocks_coexist_in_one_process(order):
    """La collecte des deux fichiers reussit, quel que soit l'ordre.

    La CI collecte le repertoire entier : `test_nl_to_logic_plugin` passe avant
    `test_runner` par ordre alphabetique, et son mock minimal arrivait en
    premier. Le garde du runner doit REPARER un mock incomplet, pas le sauter.
    Le sous-processus reproduit la collecte reelle (les mocks sont installes a
    l'import des modules).
    """
    nl_file = os.path.join(_TESTS_DIR, "test_nl_to_logic_plugin.py")
    runner_file = os.path.join(_TESTS_DIR, "test_runner.py")
    targets = (
        [nl_file, runner_file] if order == "nl_then_runner" else [runner_file, nl_file]
    )
    proc = subprocess.run(
        [sys.executable, "-m", "pytest", "--collect-only", "-q", *targets],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        cwd=_ARG_ANALYSIS_DIR,
        timeout=300,
    )
    assert proc.returncode == 0, (proc.stdout + proc.stderr)[-3000:]
