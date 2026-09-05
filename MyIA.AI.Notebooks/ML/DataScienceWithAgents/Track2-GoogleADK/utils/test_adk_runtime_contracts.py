"""Contrats comportementaux EPITA mesures contre le runtime ADK reel (#14058, tranche 1).

L'oracle de proprietes (#14058) : EPITA dit CE QUI DOIT TENIR, le runtime
ADK dit si c'est porte. Ces tests mesurent les trois premiers contrats du
corpus EPITA -- isolation d'etat par session, round-trip d'outil, budget de
tour -- sur le VRAI ADK 2.8 (Runner, InMemorySessionService,
auto-function-calling, execution de l'outil reel ``dataset_profile``).
Seul le modele est scripte : le contrat teste la mecanique du runtime,
pas les reponses d'un LLM.

Critere 4 de l'acceptance -- un contrat n'est porte que si un test echoue
quand on le retire : chaque test ci-dessous a ete verifie AU RETRAIT par
mutation locale du runtime (journal des mutations dans le body de la PR) :

- C2 retire (le runtime cesse de relayer les tool responses) -> le test
  round-trip echoue ;
- C3 retire (``asyncio.wait_for`` neutralise) -> le test budget echoue ;
- C1 (isolement) se falsifie par fusion des sessions : meme session_id ->
  le test isolement echoue, ce qui prouve qu'il detecte la fuite.

Le contrat EPITA d'etat partage DURABLE entre tours n'est PAS porte par le
runtime actuel : ``run_agent_turn`` instancie un service frais a chaque
appel. C'est mesure (pas suppose) par ``test_state_does_not_persist_across_calls``,
et le portage est un grain au-dessus d'ADK, jamais une restauration SK.
Ce test documente le non-portage : il sera inverse par le grain qui porte
la persistance.
"""

import asyncio
import sys
from pathlib import Path

import pytest

_PKG = Path(__file__).resolve().parent.parent
if str(_PKG) not in sys.path:
    sys.path.insert(0, str(_PKG))

from google.adk.agents import Agent
from google.adk.models import BaseLlm, LlmResponse
from google.adk.runners import Runner
from google.adk.sessions import InMemorySessionService
from google.genai import types

from utils import adk_runtime
from utils.adk_runtime import (
    AdkRunResult,
    AdkRuntimeUnavailable,
    dataset_profile,
    run_agent_turn,
)

# ---------------------------------------------------------------------------
# Fake LLM : script module-level, consomme par le VRAI Runner ADK.
# ---------------------------------------------------------------------------

_SCRIPT: list = []
_REQUESTS: list = []


class ScriptedLlm(BaseLlm):
    """Modele scripte pour le Runner reel : appels d'outil ou texte final."""

    async def generate_content_async(self, llm_request, stream=False):
        _REQUESTS.append(llm_request)
        if not _SCRIPT:
            yield _text_response("(script epuise : reponse finale par defaut)")
            return
        kind, payload = _SCRIPT.pop(0)
        if kind == "call":
            yield _tool_call_response(payload[0], payload[1])
        elif kind == "usage":
            yield _text_response_with_usage(payload[0], payload[1], payload[2])
        elif kind == "sleep":
            # Dort PUIS repond : sous mutation du budget de tour (wait_for
            # neutralise), le tour finit normalement et le test budget
            # echoue -- dormir sans repondre masquerait la difference (le
            # catch-all du runtime transformerait la reponse vide en
            # AdkRuntimeUnavailable pour la mauvaise raison).
            await asyncio.sleep(payload)
            yield _text_response(f"(retour apres {payload:g} s)")
        else:
            yield _text_response(payload)


def _text_response(text):
    return LlmResponse(content=types.Content(
        role="model", parts=[types.Part(text=text)]))


def _text_response_with_usage(text, prompt, completion):
    # LlmResponse/Event portent GenerateContentResponseUsageMetadata (champ
    # candidates_token_count), pas types.UsageMetadata (response_token_count) :
    # le type attendu par le runtime ADK est le premier.
    return LlmResponse(
        content=types.Content(
            role="model", parts=[types.Part(text=text)]),
        usage_metadata=types.GenerateContentResponseUsageMetadata(
            prompt_token_count=prompt,
            candidates_token_count=completion,
            total_token_count=prompt + completion,
        ))


def _tool_call_response(name, args):
    return LlmResponse(content=types.Content(
        role="model",
        parts=[types.Part(function_call=types.FunctionCall(
            name=name, args=args))]))


def _scripted_agent(name="contract_agent", tools=(dataset_profile,)):
    return Agent(
        name=name,
        description="porte-contrat de test",
        instruction="scripte",
        model=ScriptedLlm(model="scripted"),
        tools=list(tools),
    )


@pytest.fixture(autouse=True)
def _reset_script():
    _SCRIPT.clear()
    _REQUESTS.clear()
    yield
    _SCRIPT.clear()
    _REQUESTS.clear()


def _run_turn(agent, prompt, **kwargs):
    return asyncio.run(run_agent_turn(agent, prompt, **kwargs))


# ---------------------------------------------------------------------------
# C1 -- Etat partage scopé par session : les sessions s'isolent.
# ---------------------------------------------------------------------------

async def _session_event_texts(session_service, session_id):
    session = await session_service.get_session(
        app_name="contracts", user_id="u", session_id=session_id)
    texts = []
    for event in session.events:
        if event.content and event.content.parts:
            texts.append("".join(p.text or "" for p in event.content.parts))
    return texts


def test_c1_sessions_isolate_state():
    # Contrat EPITA "etat partage" : l'etat partage l'est AU SEIN d'une
    # session, jamais ENTRE sessions. Mesure sur la mecanique exacte que
    # run_agent_turn instancie (Runner + InMemorySessionService).
    svc = InMemorySessionService()
    agent = _scripted_agent()
    runner = Runner(agent=agent, app_name="contracts", session_service=svc)
    for sid in ("session-a", "session-b"):
        asyncio.run(svc.create_session(
            app_name="contracts", user_id="u", session_id=sid))
    message = types.Content(role="user", parts=[types.Part(text="message de A")])
    _SCRIPT.append(("text", "recu"))

    async def one_turn():
        async for _ in runner.run_async(
                user_id="u", session_id="session-a", new_message=message):
            pass

    asyncio.run(one_turn())

    a_texts = asyncio.run(_session_event_texts(svc, "session-a"))
    b_texts = asyncio.run(_session_event_texts(svc, "session-b"))
    assert any("message de A" in t for t in a_texts)
    assert not any("message de A" in t for t in b_texts), (
        "fuite d'etat entre sessions : le contrat d'isolation est retire")


def test_state_does_not_persist_across_calls():
    # MESURE DU NON-PORTAGE (acceptance point 2) : deux tours avec le MEME
    # session_id ne partagent rien -- run_agent_turn instancie un service
    # frais a chaque appel, l'historique du tour 1 n'atteint jamais le tour 2.
    # Observable : le llm_request du 2e tour ne contient pas le message du 1er.
    agent = _scripted_agent()
    _SCRIPT.append(("text", "tour 1"))
    _run_turn(agent, "premier message", session_id="same-session")
    assert len(_REQUESTS) == 1

    _SCRIPT.append(("text", "tour 2"))
    _run_turn(agent, "second message", session_id="same-session")

    second_request_contents = list(_REQUESTS[-1].contents)
    texts = "".join(
        (p.text or "") for c in second_request_contents
        for p in (c.parts or []))
    assert "premier message" not in texts, (
        "le runtime porte desormais un etat durable entre tours : ce test "
        "documentait le non-portage, il doit etre inverse par le grain qui "
        "porte le contrat (cf #14058)")


# ---------------------------------------------------------------------------
# C2 -- Round-trip d'outil : appel ET reponse observables, outil reel execute.
# ---------------------------------------------------------------------------

def test_c2_tool_round_trip_exposes_both_legs():
    # Contrat EPITA de designation d'outil : un appel d'outil laisse une
    # trace observable dans les DEUX sens, exposee par AdkRunResult.
    agent = _scripted_agent()
    _SCRIPT.extend([
        ("call", ("dataset_profile", {"rows": 120, "columns": 8})),
        ("text", "profil calcule"),
    ])
    result = _run_turn(agent, "profil de 120 lignes x 8 colonnes")
    assert result.tool_calls == ("dataset_profile",)
    assert result.tool_responses == ("dataset_profile",)
    assert result.tool_was_invoked


def test_c2_tool_response_carries_the_real_tool_output():
    # La jambe reponse n'est pas un echo du modele : c'est le resultat
    # calcule par le VRAI outil (dataset_profile(120, 8) -> 960 cellules,
    # 15.0 lignes par colonne). Mesure au niveau mecanique des evenements
    # ADK, ou le payload complet est observable.
    import json

    svc = InMemorySessionService()
    agent = _scripted_agent()
    runner = Runner(agent=agent, app_name="contracts", session_service=svc)
    asyncio.run(svc.create_session(
        app_name="contracts", user_id="u", session_id="tool-leg"))
    message = types.Content(role="user", parts=[types.Part(text="profil")])
    _SCRIPT.extend([
        ("call", ("dataset_profile", {"rows": 120, "columns": 8})),
        ("text", "ok"),
    ])

    payloads = []

    async def one_turn():
        async for event in runner.run_async(
                user_id="u", session_id="tool-leg", new_message=message):
            for response in (event.get_function_responses() or []):
                payloads.append(json.dumps(response.response, default=str))

    asyncio.run(one_turn())
    assert any("960" in p and "15" in p for p in payloads), (
        "la reponse d'outil ne porte pas la valeur calculee par l'outil reel")


# ---------------------------------------------------------------------------
# C3 -- Budget de tour : un tour ne court pas indefiniment.
# ---------------------------------------------------------------------------

def test_c3_turn_budget_raises_recoverable_local_on_timeout():
    # Contrat EPITA de budget : un tour est borne. Le runtime porte le
    # budget via asyncio.wait_for(timeout_seconds) et leve
    # AdkRuntimeUnavailable avec le verdict SOTA RECOVERABLE-LOCAL.
    agent = _scripted_agent()
    _SCRIPT.append(("sleep", 5))
    with pytest.raises(AdkRuntimeUnavailable) as excinfo:
        _run_turn(agent, "tour qui ne finit jamais", timeout_seconds=0.25)
    assert "RECOVERABLE-LOCAL" in str(excinfo.value)


def test_c3_llm_call_budget_is_a_real_adk_mechanic():
    # Mesure d'existence : ADK 2.8 porte une limite dure d'appels LLM par
    # invocation (LlmCallsLimitExceededError, plafond par defaut 500) --
    # observee firsthand au developpement de ces tests (un script bouclant
    # sur un appel d'outil est coupe par le runtime, pas par le test).
    # Ce test verifie que la mecanique est joignable depuis le run_config :
    # un plafond abaisse a 2 coupe une boucle de 3 appels.
    from google.adk.runners import RunConfig

    svc = InMemorySessionService()
    agent = _scripted_agent()
    runner = Runner(agent=agent, app_name="contracts", session_service=svc)
    asyncio.run(svc.create_session(
        app_name="contracts", user_id="u", session_id="budget"))
    message = types.Content(role="user", parts=[types.Part(text="boucle")])
    run_config = RunConfig(max_llm_calls=2)
    # Trois appels LLM forces par deux allers-retours d'outil puis une
    # reponse finale ; un tour user unique n'en ferait qu'un.
    _SCRIPT.extend([
        ("call", ("dataset_profile", {"rows": 10, "columns": 2})),
        ("call", ("dataset_profile", {"rows": 20, "columns": 2})),
        ("text", "fin"),
    ])

    async def one_turn():
        async for _ in runner.run_async(
                user_id="u", session_id="budget", new_message=message,
                run_config=run_config):
            pass

    # Trois reponses scriptees sous un plafond de 2 : le runtime doit
    # refuser le troisieme appel. La forme exacte de l'erreur depend
    # d'ADK, donc on assert seulement qu'elle survient.
    with pytest.raises(Exception) as excinfo:
        asyncio.run(one_turn())
    assert "limit" in str(excinfo.value).lower()


# ---------------------------------------------------------------------------
# C1b (tranche 3) -- Persistance d'etat entre tours : portee au-dessus d'ADK.
# ---------------------------------------------------------------------------

def test_c1b_history_reaches_next_turn():
    # Le contrat : l'historique du tour 1 atteint le tour 2, au sein d'une
    # meme conversation. Porte par ConversationRunner (adk_conversation) :
    # un seul InMemorySessionService + un seul session_id partages par tous
    # les tours -- mecanique native d'ADK, assemblee durablement.
    # Verifie AU RETRAIT (critere 4) : si la conversation reinstancie un
    # service/session a chaque tour (retour au comportement de
    # run_agent_turn), le llm_request du tour 2 perd le marqueur du tour 1
    # et ce test echoue.
    from utils.adk_conversation import ConversationRunner

    agent = _scripted_agent(name="persist_agent", tools=())
    marker = "le code d'acces est XYZZY-7431"

    async def scenario():
        _SCRIPT.extend([("text", "code memorise"), ("text", "voici le code")])
        async with ConversationRunner(
                agent, app_name="contracts", user_id="u") as conv:
            await conv.turn(marker)
            await conv.turn("quel est le code d'acces ?")
            history = await conv.history()
        return history

    history = asyncio.run(scenario())
    assert len(_REQUESTS) == 2
    second_request_texts = "".join(
        (p.text or "") for c in _REQUESTS[-1].contents
        for p in (c.parts or []))
    assert "XYZZY-7431" in second_request_texts, (
        "l'historique du tour 1 n'atteint pas le tour 2 : la persistance "
        "C1b est retiree")
    history_texts = "".join(
        (p.text or "") for event in history
        for p in ((event.content and event.content.parts) or []))
    assert "XYZZY-7431" in history_texts and "quel est le code" in history_texts, (
        "la session ne cumule pas les deux tours : la preuve mecanique du "
        "contrat C1b est absente")


def test_c1b_conversations_still_isolate():
    # Contre-preuve C1 : porter la persistance INTRA-conversation ne doit
    # pas creer de fuite INTER-conversations. Deux ConversationRunner sont
    # deux sessions ADK distinctes, isolees l'une de l'autre.
    from utils.adk_conversation import ConversationRunner

    async def scenario():
        conversations = {}
        for label, marker in (("premiere", "projet-alpha-120"),
                              ("seconde", "projet-beta-64")):
            agent = _scripted_agent(name=f"agent_{label}", tools=())
            _SCRIPT.append(("text", f"note {marker}"))
            async with ConversationRunner(
                    agent, app_name="contracts", user_id="u") as conv:
                await conv.turn(f"je travaille sur {marker}")
                conversations[label] = await conv.history()
        return conversations

    conversations = asyncio.run(scenario())
    first_texts = "".join(
        (p.text or "") for e in conversations["premiere"]
        for p in ((e.content and e.content.parts) or []))
    second_texts = "".join(
        (p.text or "") for e in conversations["seconde"]
        for p in ((e.content and e.content.parts) or []))
    assert "projet-alpha-120" in first_texts
    assert "projet-alpha-120" not in second_texts, (
        "fuite d'etat entre conversations : porter C1b a casse C1")


# ---------------------------------------------------------------------------
# Tranche 3 -- Mesures C4 a C7 (acceptance point 2 : mesure, pas supposition).
# Les contrats NON portes restent des grains ouverts (#14058 point 3) ; ces
# tests documentent l'etat mesure et seront inverses par les grains a venir.
# ---------------------------------------------------------------------------

def test_c4_designation_exists_in_adk_but_runtime_is_single_agent():
    # C4 (designation : qui parle ensuite selon une strategie explicite) --
    # MESURE : ADK 2.8 embarque une orchestration dynamique
    # (workflow/_dynamic_node_scheduler, importe ici comme preuve
    # d'existence), mais le runtime du depot n'expose AUCUNE strategie de
    # selection : run_agent_turn et ConversationRunner acceptent exactement
    # un agent, l'ordre multi-etapes de Lab11 est code par l'appelant en
    # Python, pas decide par le runtime. Non porte -> grain ouvert.
    import google.adk.workflow as adk_workflow  # noqa: F401 (preuve import)

    import inspect
    from utils import adk_conversation, adk_runtime

    single_agent_surfaces = (
        inspect.signature(adk_runtime.run_agent_turn).parameters["agent"],
        inspect.signature(adk_conversation.ConversationRunner.__init__).parameters["agent"],
    )
    assert all(p is not None for p in single_agent_surfaces)
    selection_terms = ("selection", "next_agent", "strategy", "orchestrat")
    runtime_surface = (
        dir(adk_runtime) + dir(adk_conversation)
    )
    wired = [t for t in selection_terms if any(
        t in name.lower() for name in runtime_surface)]
    assert wired == [], (
        f"le runtime expose desormais une mecanique de designation ({wired}) "
        ": ce test documentait le non-portage C4, il doit etre inverse par "
        "le grain qui porte le contrat")


def test_c5_transfer_exists_in_adk_but_is_not_wired():
    # C5 (handoff : transfert observable entre agents) -- MESURE : ADK 2.8
    # porte le transfer natif (TransferToAgentTool, importe ici comme
    # preuve), mais aucun agent du depot ne declare de sub_agents et
    # build_agent ne les accepte pas : le transfer n'est pas exercable
    # depuis le runtime du depot. Non porte -> grain ouvert.
    from google.adk.tools import TransferToAgentTool  # noqa: F401 (preuve)

    import inspect
    from utils import adk_runtime

    build_params = inspect.signature(adk_runtime.build_agent).parameters
    assert "sub_agents" not in build_params, (
        "build_agent accepte desormais sub_agents : le transfer C5 est "
        "cable, ce test documentait le non-portage, il doit etre inverse "
        "par le grain qui porte le contrat")
    turn_params = inspect.signature(adk_runtime.run_agent_turn).parameters
    assert "agents" not in turn_params


def test_c6_no_native_token_budget_but_usage_is_observable():
    # C6 (budgets de jetons / couts) -- TRACABILITE PORTEE (#14687) :
    # AdkRunResult remonte desormais l'usage LLM de chaque appel
    # (usage_turns / usage_total), et ConversationRunner cumule par
    # conversation. La MESURE initiale reste vraie cote budget NATIF :
    # RunConfig ne porte toujours aucun champ de consommation (max_llm_calls
    # borne des APPELS, pas les jetons) -- le budget au-dessus d'ADK est
    # la jambe 2 du grain, pas suppose natif.
    # Critere 4 -- ce test echoue au retrait de la collecte : sans le
    # releve _event_usage dans consume_events, usage_turns est vide et
    # chaque assert ci-dessous rouge (verifie par mutation locale).
    from dataclasses import fields
    from google.adk.runners import RunConfig

    run_config_budget_fields = [
        f for f in RunConfig.model_fields
        if "token" in f.lower() or "cost" in f.lower()
    ]
    assert run_config_budget_fields == [], (
        f"RunConfig porte un budget natif ({run_config_budget_fields}) : "
        "la jambe budget doit documenter ce changement de fond")

    result_fields = {f.name for f in fields(AdkRunResult)}
    assert "usage_turns" in result_fields, (
        "AdkRunResult ne remonte plus l'usage : la tracabilite C6 est "
        "retiree")

    _SCRIPT.append(("usage", ("profil", 42, 17)))
    result = _run_turn(_scripted_agent(tools=()), "question simple")
    assert len(result.usage_turns) == 1, (
        f"un appel LLM doit laisser exactement un snapshot d'usage, "
        f"mesure : {result.usage_turns}")
    assert result.usage_turns[0] == adk_runtime.AdkUsage(
        prompt_tokens=42, completion_tokens=17, total_tokens=59)
    assert result.usage_total == adk_runtime.AdkUsage(
        prompt_tokens=42, completion_tokens=17, total_tokens=59)


def test_c6_usage_accumulates_across_conversation_turns():
    # C6, versant ConversationRunner : chaque tour rend son usage (contrat
    # du tour) ET la conversation cumule (profil de consommation multi-tours).
    # Critere 4 -- au retrait de la collecte d'usage dans
    # ConversationRunner.turn, conversation.usage_total reste nul -> rouge.
    from utils.adk_conversation import ConversationRunner

    async def scenario():
        agent = _scripted_agent(tools=())
        async with ConversationRunner(agent) as conversation:
            tour1 = await conversation.turn("premier tour")
            tour2 = await conversation.turn("second tour")
            return conversation, tour1, tour2

    _SCRIPT.append(("usage", ("reponse un", 40, 10)))
    _SCRIPT.append(("usage", ("reponse deux", 60, 25)))
    conversation, tour1, tour2 = asyncio.run(scenario())
    assert tour1.usage_turns and tour2.usage_turns, (
        "chaque tour doit rendre son propre snapshot d'usage")
    assert conversation.usage_total == adk_runtime.AdkUsage(
        prompt_tokens=100, completion_tokens=35, total_tokens=135), (
        f"le cumul conversation doit sommer les tours, mesure : "
        f"{conversation.usage_total}")


def test_c6_budget_cuts_mid_turn_with_explicit_verdict():
    # C6 jambe 2 -- le plafond de jetons cumules coupe PROPREMENT : verdict
    # type AdkBudgetExceeded (pas une exception brute du stream), portant
    # plafond, cumul exact au moment de la coupe et numero du tour. Le VRAI
    # Runner ADK tourne (seul le LLM est scripte) ; le 1er tour consomme 50
    # jetons, le 2e (85) franchit le plafond de 100 pose d'office.
    # Critere 4 -- au retrait du releve de plafond dans consume_events
    # (comparaison neutralisee), le tour 2 se termine normalement et ce
    # test echoue (verifie par mutation locale).
    from utils.adk_conversation import AdkBudgetExceeded, ConversationRunner

    async def scenario():
        agent = _scripted_agent(tools=())
        async with ConversationRunner(
            agent, budget_total_tokens=100
        ) as conversation:
            tour1 = await conversation.turn("premier tour")
            try:
                await conversation.turn("second tour qui depasse")
            except AdkBudgetExceeded as verdict:
                return conversation, tour1, verdict
            raise AssertionError("le tour 2 devait couper sur le plafond")

    _SCRIPT.append(("usage", ("reponse un", 40, 10)))
    _SCRIPT.append(("usage", ("reponse deux", 60, 25)))
    conversation, tour1, verdict = asyncio.run(scenario())
    assert tour1.usage_total.total_tokens == 50, (
        "le tour 1 (sous plafond) doit se derouler normalement")
    assert verdict.verdict == "BUDGET_EXCEEDED"
    assert verdict.budget_total == 100
    assert verdict.tour == 2
    assert verdict.usage_total.total_tokens == 135, (
        f"le cumul au moment de la coupe doit inclure l'appel qui franchit "
        f"le plafond, mesure : {verdict.usage_total}")
    assert verdict.usage_total == conversation.usage_total, (
        "les jetons consommes avant la coupe restent dans le cumul "
        "(comptabilite honnete)")


def test_c6_budget_refuses_next_turn_without_calling_the_llm():
    # C6 jambe 2, versant refus pre-tour : plafond atteint des le 1er tour
    # -> le tour 2 est refuse AVANT tout appel LLM. La preuve mecanique :
    # _REQUESTS n'enregistre qu'UN appel (celui du tour 1) -- un second
    # appel LLM serait comptee la.
    # Critere 4 -- au retrait du garde pre-tour dans turn(), le tour 2
    # declenche un appel LLM (script epuise -> reponse par defaut) et ce
    # test echoue sur len(_REQUESTS) == 1.
    from utils.adk_conversation import AdkBudgetExceeded, ConversationRunner

    async def scenario():
        agent = _scripted_agent(tools=())
        async with ConversationRunner(
            agent, budget_total_tokens=50
        ) as conversation:
            await conversation.turn("premier tour consomme tout le plafond")
            try:
                await conversation.turn("tour refuse d'office")
            except AdkBudgetExceeded as verdict:
                return conversation, verdict
            raise AssertionError("le tour 2 devait etre refuse pre-tour")

    _SCRIPT.append(("usage", ("reponse un", 40, 10)))
    conversation, verdict = asyncio.run(scenario())
    assert verdict.verdict == "BUDGET_EXCEEDED"
    assert verdict.tour == 2
    assert verdict.budget_total == 50
    assert len(_REQUESTS) == 1, (
        f"le tour refuse ne doit declencher AUCUN appel LLM, "
        f"appels mesures : {len(_REQUESTS)}")
    assert conversation.budget_exhausted
    assert conversation.usage_total.total_tokens == 50


def test_c7_roles_are_declared_and_required():
    # C7 (specialistes : role declare, orchestration appuyee dessus) --
    # MESURE : PORTE. L'API Agent exige name + description + instruction
    # (champs obligatoires du modele), build_agent les exige aussi, et
    # Lab11 execute quatre specialistes declares (Planner -> Coder ->
    # Executor -> Verifier) sur ce runtime.
    from pathlib import Path

    from google.adk.agents import Agent

    agent_fields = set(Agent.model_fields)
    assert {"name", "description", "instruction"} <= agent_fields
    import inspect
    from utils import adk_runtime
    build_params = inspect.signature(adk_runtime.build_agent).parameters
    assert {"name", "description", "instruction"} <= set(build_params)
    lab11 = Path(__file__).resolve().parents[1] / (
        "Day5-DS-Star") / "Lab11-Planner-Coder-Loop.ipynb"
    lab11_source = lab11.read_text(encoding="utf-8")
    for role in ("Planner", "Coder", "Executor", "Verifier"):
        assert role in lab11_source, (
            f"le specialiste {role} n'est plus execute par Lab11 : C7 "
            "perd sa preuve d'orchestration")
