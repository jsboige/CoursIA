"""Pilote P2 (issue #14499, point 3) : la MEME charge de distillation, moteur MAF.

Deuxieme replique du pilote identique dans les trois moteurs. Ce qui ne change
PAS par rapport a P1 (replica SK, `sk_distillation_pilot.py`) :
- la charge : la fixture figee `distill_charge_fixture.md` (cellules 0..8 de
  01-SemanticKernel-Intro.ipynb, tete 8e9eaaaa0) — byte-stable entre moteurs ;
- les trois roles et leurs instructions : producteur (<= 120 mots), critique a
  verdict impose (`VERDICT: ACCEPTE|REVISION:`), arbitre (`DECISION:`) ;
- la politique de tour : producteur -> critique -> [revision -> producteur ->
  critique] -> arbitre, au plus 2 tours ;
- le modele EPINGLE `gpt-4o-mini`, temperature 0 (aucune sonde ne bascule) ;
- les mesures : LOC, appels LLM (budget dur), latence par appel et mur,
  comportement en echec (sonde a type nomme), determinisme sur la DECISION.

Ce qui change : L'ORGANE. La ou P1 deleguait la boucle a un manager custom de
`GroupChatOrchestration` (SK), P2 l'encode dans une **selection function**
appelee par le moteur a chaque tour avec l'etat (`GroupChatState`) —
`GroupChatBuilder` (orchestrations 1.3.1). C'est l'idiome MAF de la meme
politique conditionnelle : le routage vit dans NOTRE callable, comme dans
`select_next_agent` de P1. Comparaison par construction : meme charge, meme
politique, meme reglage, organe different.
"""

import asyncio
import os
import sys
import time
from pathlib import Path

from agent_framework import Agent, ChatOptions, Content, Message
from agent_framework.orchestrations import GroupChatBuilder, GroupChatResponseReceivedEvent
from agent_framework_openai import OpenAIChatCompletionClient

HERE = Path(__file__).resolve().parent
MASTER_ENV = HERE.parents[3] / ".secrets" / "master.env"
FIXTURE = HERE / "distill_charge_fixture.md"
OPENAI_BASE = "https://api.openai.com/v1"  # epingle : l'env du poste pointe vers un proxy local
BUDGET = 16
MODEL_ID = "gpt-4o-mini"
MAX_TOKENS = 400
MAX_TOURS = 2

PRODUCTEUR = "producteur"
CRITIQUE = "critique"
ARBITRE = "arbitre"

llm_calls = 0
call_log: list[dict] = []


def maf_versions() -> str:
    from importlib.metadata import version

    return (
        f"agent-framework-core {version('agent-framework-core')}, "
        f"agent-framework-orchestrations {version('agent-framework-orchestrations')}, "
        f"agent-framework-openai {version('agent-framework-openai')}"
    )


def load_api_key() -> str:
    """Lit OPENAI_API_KEY dans master.env (repli : variable d'environnement)."""
    if not MASTER_ENV.is_file():
        if os.getenv("OPENAI_API_KEY"):
            return os.environ["OPENAI_API_KEY"]
        raise SystemExit(f"ERREUR: {MASTER_ENV} introuvable et OPENAI_API_KEY absente de l'environnement")
    with open(MASTER_ENV, encoding="utf-8") as fh:
        for line in fh:
            stripped = line.strip().removeprefix("export ")
            if stripped.startswith("OPENAI_API_KEY="):
                value = stripped.split("=", 1)[1].strip().strip('"').strip("'")
                if not value:
                    raise SystemExit("ERREUR: OPENAI_API_KEY vide dans master.env")
                return value
    raise SystemExit("ERREUR: OPENAI_API_KEY absent de " + str(MASTER_ENV))


# Instructions : IDENTIQUES a P1, mot pour mot (la comparaison le doit).
INSTR_PRODUCTEUR = (
    "Tu es l'agent producteur d'une chaine de distillation pedagogique. On te donne une section "
    "de carnet Jupyter (markdown + code) et, eventuellement, la critique du tour precedent. "
    "Redige une distillation d'au plus 120 mots en francais : l'idee directrice de la section, "
    "les concepts cles, ce que le code montre. N'invente rien qui ne soit dans la section. "
    "Si une critique te parvient, corrige precisement le point qu'elle nomme. "
    "Reponds par le texte de la distillation seul, sans preambule."
)
INSTR_CRITIQUE = (
    "Tu es l'agent critique d'une chaine de distillation. On te donne la section source et la "
    "distillation proposee. Verifie exactement trois criteres : (1) exactitude factuelle par "
    "rapport a la source ; (2) absence de contenu invente ; (3) concision (120 mots max). "
    "Ta reponse tient en deux lignes, format impose : "
    "'VERDICT: ACCEPTE' si les trois criteres passent, sinon "
    "'VERDICT: REVISION: <le critere precise qui echoue, en une phrase>'. "
    "Rien d'autre."
)
INSTR_ARBITRE = (
    "Tu es l'agent arbitre d'une chaine de distillation. On te donne l'historique du tour ou des "
    "deux tours. Tu ne reecris pas la distillation. Ta reponse tient en une ligne, format impose : "
    "'DECISION: ACCEPTE tour <N>' si la derniere distillation est recevable, sinon "
    "'DECISION: RESIDUEL tour <N>: <le blocage en une phrase>'. "
    "Rien d'autre."
)


class CountingClient(OpenAIChatCompletionClient):
    """Client MAF qui compte chaque appel LLM (jette au-dela du budget) et
    mesure latence + jetons quand la reponse les porte."""

    async def _inner_get_response(self, *args, **kwargs):
        global llm_calls
        llm_calls += 1
        if llm_calls > BUDGET:
            raise RuntimeError(f"Budget LLM depasse ({llm_calls}/{BUDGET})")
        started = time.perf_counter()
        response = await super()._inner_get_response(*args, **kwargs)
        elapsed = time.perf_counter() - started
        usage = getattr(response, "usage_details", None)
        usage_text = None
        if usage is not None:
            usage_text = {
                "prompt_tokens": getattr(usage, "input_token_count", None),
                "completion_tokens": getattr(usage, "output_token_count", None),
            }
        call_log.append({"latency_s": round(elapsed, 2), "usage": usage_text, "mode": "complet"})
        return response


def make_client(model_id: str, api_key: str) -> CountingClient:
    """base_url explicite : les env OpenAI du poste pointent vers un proxy local."""
    return CountingClient(
        model=model_id,  # le connecteur prend `model`, pas `model_id` (openai 1.16.0)
        api_key=api_key,
        base_url=OPENAI_BASE,
    )


def _texte(message) -> str:
    contenus = getattr(message, "contents", None) or []
    return "".join(getattr(c, "text", "") or "" for c in contenus)


def _auteur(message) -> str:
    return getattr(message, "author_name", None) or getattr(message, "name", None) or "?"


def selection_distillation(etat) -> str:
    """La politique de tour, dans l'idiome MAF : notre selection function est
    appelee par le moteur a chaque tour avec `GroupChatState(current_round,
    participants, conversation)`.

    Meme logique que `DistillationGroupChatManager.select_next_agent` de P1 :
    au depart le producteur ; apres le producteur le critique ; apres le
    critique, l'arbitre si ACCEPTE, sinon le producteur tant que le budget de
    tours le permet. La borne MAX_TOURS se calcule sur le nombre de passages
    du producteur, comme P1.
    """
    participants = getattr(etat, "participants", None) or {}
    conversation = getattr(etat, "conversation", None) or []
    auteurs = [_auteur(m) for m in conversation]
    # Garde du tour initial : la conversation est DEJA non vide au round 0
    # (le message utilisateur de la charge, author_name=None). Tant qu'aucun
    # participant n'a parle, c'est le producteur qui ouvre — jamais l'arbitre.
    if not any(a in (PRODUCTEUR, CRITIQUE, ARBITRE) for a in auteurs):
        return PRODUCTEUR
    dernier = auteurs[-1]
    if dernier == PRODUCTEUR:
        return CRITIQUE
    if dernier == CRITIQUE:
        verdict = _texte(conversation[-1])
        if "VERDICT: ACCEPTE" in verdict:
            return ARBITRE
        tours_produits = sum(1 for a in auteurs if a == PRODUCTEUR)
        if tours_produits < MAX_TOURS:
            return PRODUCTEUR
        return ARBITRE
    return ARBITRE  # etat terminal : apres l'arbitre la borne max_rounds scelle


def _apres_arbitre(conversation) -> bool:
    """Termination condition MAF : la boucle s'arrete des que l'arbitre a parle.

    Recoit la conversation complete (list[Message]) ; on inspecte le dernier
    auteur. Sans cette condition, la selection function re-elirait l'arbitre
    jusqu'a max_rounds (elle n'a pas d'etat terminal a lui seul).
    """
    if not conversation:
        return False
    return _auteur(conversation[-1]) == ARBITRE


async def run_distillation(client: CountingClient, options: ChatOptions, charge: str) -> dict:
    """Une execution complete de la boucle ; retourne le releve de mesures."""

    def fabrique(nom: str, instructions: str, description: str) -> Agent:
        return Agent(
            client=client,
            instructions=instructions,
            name=nom,
            description=description,
            default_options=options,
        )

    producteur = fabrique(
        PRODUCTEUR, INSTR_PRODUCTEUR, "Redige la distillation pedagogique de la section (au plus 120 mots)."
    )
    critique = fabrique(
        CRITIQUE, INSTR_CRITIQUE, "Verifie exactitude, absence d'invention et concision ; rend VERDICT: ACCEPTE ou REVISION."
    )
    arbitre = fabrique(
        ARBITRE, INSTR_ARBITRE, "Scelle le resultat : DECISION: ACCEPTE tour N, ou RESIDUEL tour N."
    )

    builder = GroupChatBuilder(
        participants=[producteur, critique, arbitre],
        selection_func=selection_distillation,
        max_rounds=MAX_TOURS * 3 + 1,  # garde-fou structurel ; la termination_condition scelle apres l'arbitre
        termination_condition=_apres_arbitre,
    )
    started = time.perf_counter()
    workflow = builder.build()  # orchestration fraiche par invocation, comme P1/T8
    message = Message(role="user", contents=[Content(type="text", text=charge)])
    resultat = await workflow.run(message)
    wall_s = round(time.perf_counter() - started, 2)

    # Le resultat est un FLUX D'EVENEMENTS (lecon T8). Un tour de parole est
    # atteste par un `GroupChatResponseReceivedEvent` (round_index +
    # participant_name, SANS texte) ; le texte vit dans l'event
    # `executor_invoked` dont `data` est un `AgentExecutorResponse` portant
    # `executor_id` (= nom de l'agent) et `agent_response` (AgentResponse,
    # `.messages` / `.text`). On joint les deux : la sequence d'auteurs vient
    # des group_chat, les textes des AgentExecutorResponse.
    from agent_framework._workflows._agent_executor import AgentExecutorResponse

    auteurs: list[str] = []
    textes_par_agent: dict[str, list[str]] = {}
    for event in resultat:
        etype = getattr(event, "type", None)
        donnee = getattr(event, "data", None)
        if etype == "group_chat" and isinstance(donnee, GroupChatResponseReceivedEvent):
            nom = getattr(donnee, "participant_name", None)
            if nom and (not auteurs or nom != auteurs[-1]):
                auteurs.append(nom)
        elif etype == "executor_invoked" and isinstance(donnee, AgentExecutorResponse):
            nom = getattr(donnee, "executor_id", None)
            if nom not in (PRODUCTEUR, CRITIQUE, ARBITRE):
                continue
            reponse = getattr(donnee, "agent_response", None)
            texte = ""
            if reponse is not None:
                texte = getattr(reponse, "text", None) or ""
                if not texte:
                    texte = "".join(_texte(msg) for msg in (getattr(reponse, "messages", None) or []))
            if texte:
                textes_par_agent.setdefault(nom, []).append(texte)

    tours = max(1, sum(1 for a in auteurs if a == PRODUCTEUR))
    decision = ""
    for texte in textes_par_agent.get(ARBITRE, []):
        if "DECISION:" in texte:
            lignes = [l.strip() for l in texte.splitlines() if l.strip().startswith("DECISION:")]
            if lignes:
                decision = lignes[0]
    last_verdict = "?"
    for texte in reversed(textes_par_agent.get(CRITIQUE, [])):
        if "VERDICT:" in texte:
            last_verdict = "ACCEPTE" if "VERDICT: ACCEPTE" in texte else "REVISION"
            break
    return {
        "speakers": auteurs,
        "tours": tours,
        "decision": decision,
        "last_verdict": last_verdict,
        "wall_s": wall_s,
    }


async def sonde(client: CountingClient) -> str:
    """Sonde le modele epingle avec 1 appel minuscule ; echoue fort, ne bascule jamais."""
    agent = Agent(client=client, instructions="Reponds exactement: OK", name="sonde")
    reponse = await agent.run(messages="ping")
    return (getattr(reponse, "text", None) or str(reponse))[:20]


async def sonde_echec(api_key: str) -> str:
    """Comportement en echec : un modele inexistant doit echouer avec un type nomme."""
    client = make_client("ce-modele-n-existe-pas", api_key)
    agent = Agent(client=client, instructions="Reponds: OK", name="sonde_echec")
    try:
        await agent.run(messages="ping")
    except Exception as exc:  # l'erreur exacte, jamais la cle
        return f"{type(exc).__name__}"
    return "AUCUNE_ERREUR (inespere)"


async def main() -> int:
    api_key = load_api_key()

    try:
        pong = await sonde(make_client(MODEL_ID, api_key))
        print(f"probe {MODEL_ID}: OK -> {pong}")
    except Exception as exc:
        print(f"probe {MODEL_ID}: ECHEC {type(exc).__name__}: {str(exc)[-200:]}")
        print("Modele de comparaison epingle : aucun repli automatique (exit 2).")
        return 2

    print(f"MAF versions: {maf_versions()}")
    failure = await sonde_echec(api_key)
    print(f"sonde echec (modele inexistant): {failure}")
    if failure.startswith("AUCUNE_ERREUR"):
        print("Sonde d'echec non concluante : le faux modele n'a pas leve d'erreur (exit 3).")
        return 3

    charge = FIXTURE.read_text(encoding="utf-8")
    print(f"charge: {FIXTURE.name} ({len(charge)} caracteres, fixture figee)")

    client = make_client(MODEL_ID, api_key)
    options = ChatOptions(temperature=0.0, max_tokens=MAX_TOKENS)

    runs = []
    for run_index in (1, 2):
        before_calls = llm_calls
        before_log = len(call_log)
        summary = await run_distillation(client, options, charge)
        runs.append(summary)
        print(f"[run {run_index}] tours={summary['tours']} verdict_final={summary['last_verdict']} "
              f"wall={summary['wall_s']}s appels={llm_calls - before_calls}")
        print(f"    sequence: {' -> '.join(summary['speakers'])}")
        print(f"    decision: {summary['decision'][:100]}")
        for entry in call_log[before_log:]:
            usage = entry["usage"]
            usage_text = (
                f"in={usage['prompt_tokens']} out={usage['completion_tokens']}" if usage else "n/d"
            )
            print(f"    appel[{entry['mode']}]: latence={entry['latency_s']}s jetons={usage_text}")

    def structure_decision(decision: str) -> tuple:
        # On asserte la STRUCTURE, jamais la prose : type de decision (ACCEPTE /
        # RESIDUEL) et tour d'arbitrage (entier apres "tour"). Le motif RESIDUEL
        # porte une phrase libre apres "tour N:" — on ne retient que l'entier.
        import re

        type_decision = "ACCEPTE" if "ACCEPTE" in decision else ("RESIDUEL" if "RESIDUEL" in decision else "?")
        match = re.search(r"tour\s+(\d+)", decision)
        tour = match.group(1) if match else "?"
        return (type_decision, tour)

    struct1 = (runs[0]["tours"],) + structure_decision(runs[0]["decision"])
    struct2 = (runs[1]["tours"],) + structure_decision(runs[1]["decision"])
    decision_presente = all(r["decision"] for r in runs)
    deterministic = decision_presente and struct1 == struct2
    print(f"DETERMINISME (tours, decision, tour d'arbitrage): {'OK' if deterministic else 'FAIL'} {struct1} vs {struct2}")
    print(f"LLM CALLS: {llm_calls}/{BUDGET}")
    print(f"LOC PILOT: {len(Path(__file__).read_text(encoding='utf-8').splitlines())} lignes")
    verdict_final = "PILOT OK" if deterministic else "PILOT FAIL"
    print(f"{verdict_final} orchestration=GroupChat(selection_func) charge=distillation")
    return 0 if deterministic else 1


if __name__ == "__main__":
    try:
        sys.exit(asyncio.run(main()))
    except SystemExit:
        raise
    except BaseException as exc:  # erreur exacte, jamais la cle
        print(f"ERREUR FATALE {type(exc).__name__}: {str(exc)[:300]}")
        sys.exit(2)
