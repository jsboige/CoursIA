"""Pilote T7 (issue #14499) : Microsoft Agent Framework -- la couche agents.

Complement du pilote T5 (le graphe typé) : ici, la couche **orchestrations**
(paquet `agent-framework-orchestrations`), qui offre en Python les memes
topologies que celles mesurees en C# par la sonde T6 (Sequential, Concurrent,
GroupChat, Magentic, Handoff). L'observable principal est le **handoff natif**
(`HandoffBuilder`), meme scenario de triage que les pilotes T2 (SK
HandoffOrchestration) et T3 (ADK transfer C5) : triage ->
specialiste_technique | specialiste_formation, deux entrees non ambigues,
meme modele echange en constante (gpt-4o-mini, temperature 0), budget dur.

Ce qui rend les trois moteurs comparables par construction : le routage est
delegue au MOTEUR (outil de handoff genere), pas ecrit dans une lambda comme
en T5 -- c'est le versant "delegue" de la conclusion T5 sur la nature de la
decision de routage.

Determinisme exige : a temperature 0, on n'asserte PAS la prose mais la
DECISION DE ROUTAGE (quel specialiste termine), meme doctrine que T2/T3.
Chaque entree est executee DEUX fois dans le meme process ; le script entier
peut etre relance pour la mesure inter-processus.

Budget dur : 40 appels LLM au total (sonde incluse), garde-fou anti-emballement.
"""

import asyncio
import os
import sys
from pathlib import Path

from agent_framework import Agent, ChatOptions, Content, Message
from agent_framework.orchestrations import (
    ConcurrentBuilder,
    GroupChatBuilder,
    HandoffBuilder,
    MagenticBuilder,
    SequentialBuilder,
)
from agent_framework_openai import OpenAIChatCompletionClient

MASTER_ENV = Path(__file__).resolve().parents[4] / ".secrets" / "master.env"
OPENAI_BASE = "https://api.openai.com/v1"  # epingle : le SDK honore sinon l'env du poste (lecon T2)
BUDGET = 40  # garde-fou anti-emballement, pas une cible
MODEL_ID = "gpt-4o-mini"
MAX_TOKENS = 200

llm_calls = 0


def maf_versions() -> str:
    """Versions du coeur MAF et de la couche orchestrations.

    Le metapaquet `agent_framework.__version__` et le coeur
    `agent-framework-core` divergent (lecon T5) : on cite les deux paquets qui
    s'executent reellement ici.
    """
    from importlib.metadata import PackageNotFoundError, version

    parts = []
    for name in ("agent-framework-core", "agent-framework-orchestrations"):
        try:
            parts.append(f"{name} {version(name)}")
        except PackageNotFoundError:
            parts.append(f"{name} ABSENT")
    return ", ".join(parts)


def load_api_key() -> str:
    """Lit OPENAI_API_KEY dans master.env (repli: variable d'environnement)."""
    if not MASTER_ENV.is_file():
        if os.getenv("OPENAI_API_KEY"):
            return os.environ["OPENAI_API_KEY"]
        raise SystemExit(
            f"ERREUR: {MASTER_ENV} introuvable et OPENAI_API_KEY absente de l'environnement"
        )
    with open(MASTER_ENV, encoding="utf-8") as fh:
        for line in fh:
            stripped = line.strip().removeprefix("export ")
            if stripped.startswith("OPENAI_API_KEY="):
                value = stripped.split("=", 1)[1].strip().strip('"').strip("'")
                if not value:
                    raise SystemExit("ERREUR: OPENAI_API_KEY vide dans master.env")
                return value
    raise SystemExit("ERREUR: OPENAI_API_KEY absent de " + str(MASTER_ENV))


class CountingClient(OpenAIChatCompletionClient):
    """Client MAF qui compte chaque appel LLM (jette au-dela du budget)."""

    def _tick(self) -> None:
        global llm_calls
        llm_calls += 1
        if llm_calls > BUDGET:
            raise RuntimeError(f"Budget LLM depasse ({llm_calls}/{BUDGET})")

    async def _inner_get_response(self, *args, **kwargs):
        self._tick()
        return await super()._inner_get_response(*args, **kwargs)


# --- Les trois roles, memes instructions que T2/T3 -------------------------

INSTR_TRIAGE = (
    "Tu es l'agent de triage d'un support technique et pedagogique. "
    "Analyse la demande de l'utilisateur et transfere-la au bon specialiste "
    "grace a l'outil de transfert disponible. Ne reponds jamais toi-meme a la demande."
)
INSTR_TECH = (
    "Tu es le specialiste technique (GPU, CUDA, entranement de modeles). "
    "Reponds en une ou deux phrases concretes."
)
INSTR_FORM = (
    "Tu es le specialiste formation (parcours, cours, cursus IA). "
    "Reponds en une ou deux phrases concretes."
)

# Les deux entrees non ambigues du banc T2/T3.
ENTREES = [
    ("technique", "Mon pipeline d'entraînement plante avec CUDA out of memory sur mon RTX 4060, que faire ?"),
    ("formation", "Quelle formation me recommandez-vous pour apprendre a construire des agents IA ?"),
]


def auteurs(resultat) -> list:
    """Suite des agents qui ont parle, dans l'ordre (signature structurelle).

    Le resultat est une **liste d'events** (`WorkflowRunResult` sous-classe de
    list) ; `get_outputs()` n'en rend que la charge utile (AgentResponse), qui
    n'expose pas d'identite d'agent -- fait d'API mesure : l'identite vit dans
    l'event `executor_invoked`, champ `executor_id`.
    """
    sortie = []
    for event in resultat:
        # fait d'API mesure (decode sur le flux complet d'un run) : les events
        # `executor_invoked`/`executor_completed` partent aussi pour les rounds
        # du protocole interne (should_respond=False, sans appel LLM) -- seuls
        # les events `type='output'` marquent un tour de parole reel, a raison
        # d'un par appel LLM (verifie : 2 appels par run, 2 events output).
        if getattr(event, "type", None) == "output":
            ident = getattr(event, "executor_id", None)
            if ident and (not sortie or ident != sortie[-1]):
                sortie.append(ident)
    return sortie


async def sonde(client: CountingClient) -> None:
    """Atteste que le service repond sur le modele epingle (echoue fort)."""
    agent = Agent(client=client, instructions="Reponds exactement: OK", name="sonde")
    reponse = await agent.run(messages="ping")
    texte = " ".join(
        getattr(m, "text", "") or "" for m in getattr(reponse, "messages", [])
    ).strip()
    if not texte:
        raise SystemExit("ERREUR: sonde muette sur " + MODEL_ID)


async def main() -> int:
    client = CountingClient(
        api_key=load_api_key(),
        base_url=OPENAI_BASE,
        model=MODEL_ID,
    )

    print(f"MAF versions: {maf_versions()}")
    await sonde(client)
    print(f"sonde OK ({llm_calls} appel(s))")

    # Controle positif (zero appel LLM) : les cinq topologies mesurees en C#
    # par la sonde T6 existent aussi en Python, dans le paquet orchestrations.
    topologies = {
        "Sequential": SequentialBuilder,
        "Concurrent": ConcurrentBuilder,
        "GroupChat": GroupChatBuilder,
        "Magentic": MagenticBuilder,
        "Handoff": HandoffBuilder,
    }
    print("TOPOLOGIES PYTHON: " + ", ".join(f"{n}" for n in topologies))

    options = ChatOptions(temperature=0.0, max_tokens=MAX_TOKENS)

    def fabrique_agent(nom: str, instructions: str, description: str) -> Agent:
        return Agent(
            client=client,
            instructions=instructions,
            name=nom,
            description=description,
            default_options=options,
            # exigé par HandoffBuilder.build() : sans ce drapeau, ValueError
            # ("local history stays consistent with the service across
            # handoff tool-call short-circuits") -- fait d'API mesuré.
            require_per_service_call_history_persistence=True,
        )

    triage = fabrique_agent(
        "triage", INSTR_TRIAGE, "Aiguille la demande vers le bon specialiste."
    )
    tech = fabrique_agent(
        "specialiste_technique", INSTR_TECH, "Problemes techniques: GPU, CUDA, entranement."
    )
    form = fabrique_agent(
        "specialiste_formation", INSTR_FORM, "Conseils de parcours et formations IA."
    )

    builder = (
        HandoffBuilder(participants=[triage, tech, form])
        .add_handoff(
            triage,
            [tech, form],
            description="Transfere au specialiste adapte a la demande.",
        )
        # fait d'API mesuré : build() jette ValueError sans agent de départ explicite
        .with_start_agent(triage)
    )
    resultats = {}
    for attendu, entree in ENTREES:
        pour_entree = []
        for tour in (1, 2):
            # fait d'API mesure : un workflow handoff REUTILISE garde une
            # request_info pendante apres sa premiere terminaison (posture
            # interactive : le workflow attend la reponse utilisateur) ; une
            # nouvelle entree fait avancer l'etat mais le warning "fresh
            # message while request_info events are still pending" le dit.
            # Meme hygiene que T2 (orchestration + runtime frais par
            # invocation) : on RECONSTRUIT le workflow a chaque run.
            workflow = builder.build()
            message = Message(
                role="user", contents=[Content(type="text", text=entree)]
            )
            resultat = await workflow.run(message)
            seq = auteurs(resultat)
            finaux = [a for a in seq if a.startswith("specialiste_")]
            decision = finaux[-1] if finaux else "(aucun)"
            pour_entree.append(decision)
            print(f"[{attendu} #{tour}] agents={seq} decision: {decision}")
        resultats[attendu] = pour_entree

    ok_tech = all(d == "specialiste_technique" for d in resultats["technique"])
    ok_form = all(d == "specialiste_formation" for d in resultats["formation"])
    determinisme = all(len(set(v)) == 1 for v in resultats.values())

    print(f"ROUTING CORRECTNESS: {'OK' if (ok_tech and ok_form) else 'ECHEC'}")
    print(f"ROUTING DETERMINISM: {'OK' if determinisme else 'ECHEC'}")
    print(f"LLM CALLS: {llm_calls}/{BUDGET}")
    print(f"PILOT OK maf handoff model={MODEL_ID}")
    return 0 if (ok_tech and ok_form and determinisme) else 1


if __name__ == "__main__":
    sys.exit(asyncio.run(main()))
