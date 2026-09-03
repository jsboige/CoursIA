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
