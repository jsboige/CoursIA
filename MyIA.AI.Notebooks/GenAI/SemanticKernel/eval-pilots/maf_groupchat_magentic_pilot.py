"""Pilote T8 (issue #14499) : MAF orchestrations -- GroupChat et Magentic.

Suite directe du pilote T7 (HandoffBuilder) : les deux topologies dont
l'executabilite restait a mesurer en Python apres le controle d'import T7.

**GroupChat** -- la difference topologique decisive face au handoff : qui
parle ensuite n'est PAS negocie par un protocole du moteur, c'est une
**selection function** QUE NOUS ECRIVONS, appelee a chaque tour avec l'etat
de la conversation (`GroupChatState`). Le pilote mesure ce seam : le triage
repond en nommant son specialiste, la selection function lit la conversation
et route. Meme banc que T2/T3/T7 (deux entrees non ambigues, gpt-4o-mini,
temperature 0), observable = quel specialiste a parle (tour 2, borne
`max_rounds=2`).

**Magentic** -- le pattern orchestrateur (manageur + ledger de taches) :
un agent manageur decoupe la demande, des specialiste executent, le ledger
piste l'avancement. Observable = la participation (le bon specialiste a-t-il
travaille ?) sous borne `max_round_count=1`.

Determinisme exige : a temperature 0, on n'asserte PAS la prose mais la
DECISION (quel specialiste parle / participe), meme doctrine que T2/T3/T7.
Chaque entree est executee DEUX fois dans le meme process ; le script entier
peut etre relance pour la mesure inter-processus.

Budget dur : 60 appels LLM au total (sonde incluse), garde-fou anti-emballement.
"""

import asyncio
import os
import sys
from pathlib import Path

from agent_framework import Agent, ChatOptions, Content, Message
from agent_framework.orchestrations import (
    GroupChatBuilder,
    GroupChatResponseReceivedEvent,
    MagenticBuilder,
    StandardMagenticManager,
)
from agent_framework_openai import OpenAIChatCompletionClient

MASTER_ENV = Path(__file__).resolve().parents[4] / ".secrets" / "master.env"
OPENAI_BASE = "https://api.openai.com/v1"  # epingle : le SDK honore sinon l'env du poste (lecon T2)
BUDGET = 60  # garde-fou anti-emballement, pas une cible
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


# --- Les roles --------------------------------------------------------------
# Specialistes : memes instructions que T2/T3/T7. Triage : ADAPTE -- pas
# d'outil de transfert ici, la selection function lit sa reponse.

INSTR_TRIAGE_GC = (
    "Tu es l'agent de triage d'un support technique et pedagogique. "
    "Analyse la demande de l'utilisateur et designe le specialiste adapte. "
    "Termine ta reponse par la designation EXACTE du specialiste vise, "
    "en majuscules : SPECIALISTE TECHNIQUE ou SPECIALISTE FORMATION. "
    "Ne reponds jamais toi-meme a la demande."
)
INSTR_MANAGER = (
    "Tu es le manageur d'une equipe de deux specialistes (technique: GPU, "
    "CUDA, entrainement de modeles ; formation: parcours et cours IA). "
    "Decoupe la demande de l'utilisateur en UNE SEULE tache, confiee au "
    "specialiste concerne. Ne reponds jamais toi-meme a la demande."
)
INSTR_TECH = (
    "Tu es le specialiste technique (GPU, CUDA, entranement de modeles). "
    "Reponds en une ou deux phrases concretes."
)
INSTR_FORM = (
    "Tu es le specialiste formation (parcours, cours, cursus IA). "
    "Reponds en une ou deux phrases concretes."
)

# Les deux entrees non ambigues du banc T2/T3/T7.
ENTREES = [
    ("technique", "Mon pipeline d'entraînement plante avec CUDA out of memory sur mon RTX 4060, que faire ?"),
    ("formation", "Quelle formation me recommandez-vous pour apprendre a construire des agents IA ?"),
]


def auteurs(resultat) -> list:
    """Suite des participants qui ont reellement parle, dans l'ordre.

    Faits d'API mesures (sondage du flux complet d'un run, T8) :
    - les events `type='output'` portent l'id de l'ORCHESTRATEUR
      (`group_chat_orchestrator` / `magentic_orchestrator`), pas des
      participants -- l'observable T7 ne dit pas QUI a parle ici ;
    - les events `type='group_chat'` portent en `data` soit un
      `GroupChatRequestSentEvent` (tache envoyee, round_index +
      participant_name) soit un `GroupChatResponseReceivedEvent` (vraie
      reponse). Seul le SECOND marque un tour de parole avec appel LLM ;
    - Magentic embarque un group chat interne : le MEME extracteur
      fonctionne pour les deux topologies (le plan du manageur vit dans
      les events `magentic_orchestrator`, hors tours de parole).
    """
    sortie = []
    for event in resultat:
        if getattr(event, "type", None) == "group_chat":
            donnee = getattr(event, "data", None)
            if isinstance(donnee, GroupChatResponseReceivedEvent):
                nom = getattr(donnee, "participant_name", None)
                if nom and (not sortie or nom != sortie[-1]):
                    sortie.append(nom)
    return sortie


def _texte(message) -> str:
    """Texte plat d'un Message (union des contents texte)."""
    return " ".join(
        getattr(c, "text", "") or "" for c in getattr(message, "contents", [])
    )


async def sonde(client: CountingClient) -> None:
    """Atteste que le service repond sur le modele epingle (echoue fort)."""
    agent = Agent(client=client, instructions="Reponds exactement: OK", name="sonde")
    reponse = await agent.run(messages="ping")
    texte = " ".join(
        getattr(m, "text", "") or "" for m in getattr(reponse, "messages", [])
    ).strip()
    if not texte:
        raise SystemExit("ERREUR: sonde muette sur " + MODEL_ID)


# --- GroupChat : la selection function est NOTRE code ------------------------

def selection_par_contenu(etat) -> str:
    """Selection function mesuree : round 0 -> triage, ensuite on lit SA
    reponse (dernier message de la conversation) et on route vers le
    specialiste qu'elle designe.

    C'est le seam evaluable du GroupChat : le routage vit dans NOTRE callable
    appele par le moteur avec `GroupChatState(current_round, participants,
    conversation)` -- par opposition au handoff T7 ou le routage vit dans le
    protocole du moteur.
    """
    participants = getattr(etat, "participants", None) or {}
    if getattr(etat, "current_round", 0) <= 0 or not etat.conversation:
        for ident, nom in participants.items():
            if "triage" in str(ident) or "triage" in str(nom):
                return ident
        raise RuntimeError("selection: aucun participant 'triage' " + repr(participants))
    # Dernier message = la reponse du triage au tour precedent.
    dernier = etat.conversation[-1]
    texte = _texte(dernier).upper()
    cible = "technique" if "SPECIALISTE TECHNIQUE" in texte else (
        "formation" if "SPECIALISTE FORMATION" in texte else None
    )
    if cible is None:
        raise RuntimeError(
            "selection: le triage ne designe pas son specialiste: " + texte[:200]
        )
    for ident, nom in participants.items():
        if cible in str(ident) or cible in str(nom):
            return ident
    raise RuntimeError(f"selection: aucun participant pour '{cible}'")


async def banc_groupchat(client, options) -> dict:
    """GroupChatBuilder : triage -> specialiste, borne max_rounds=2."""

    def fabrique_agent(nom: str, instructions: str, description: str) -> Agent:
        return Agent(
            client=client,
            instructions=instructions,
            name=nom,
            description=description,
            default_options=options,
        )

    triage = fabrique_agent(
        "triage", INSTR_TRIAGE_GC, "Aiguille la demande vers le bon specialiste."
    )
    tech = fabrique_agent(
        "specialiste_technique", INSTR_TECH, "Problemes techniques: GPU, CUDA, entrainement."
    )
    form = fabrique_agent(
        "specialiste_formation", INSTR_FORM, "Conseils de parcours et formations IA."
    )

    builder = GroupChatBuilder(
        participants=[triage, tech, form],
        selection_func=selection_par_contenu,
        max_rounds=2,
    )
    resultats = {}
    for attendu, entree in ENTREES:
        pour_entree = []
        for tour in (1, 2):
            # Meme hygiene que T2/T7 : orchestration fraiche par invocation.
            workflow = builder.build()
            message = Message(role="user", contents=[Content(type="text", text=entree)])
            resultat = await workflow.run(message)
            seq = auteurs(resultat)
            finaux = [a for a in seq if "specialiste" in a]
            decision = finaux[-1] if finaux else "(aucun)"
            pour_entree.append(decision)
            print(f"[GC {attendu} #{tour}] agents={seq} decision: {decision}")
        resultats[attendu] = pour_entree
    return resultats


# --- Magentic : manageur + ledger, borne max_round_count=1 -------------------

async def banc_magentic(client, options) -> dict:
    """MagenticBuilder : le manageur planifie, les specialistes executent.

    Fait d'API mesure : le manageur doit produire des LEDGERS EN JSON (plan,
    avancement). A max_tokens=200 le JSON est tronque -> "Unbalanced JSON
    braces" -> l'orchestrateur RESET puis "Max round count reached" SANS que
    le plan n'ait jamais ete consomme. Le manageur a donc son propre
    plafond (600 tokens), les specialistes gardent celui du banc (200).
    """

    options_manager = ChatOptions(temperature=0.0, max_tokens=600)

    def fabrique_agent(nom: str, instructions: str, description: str, opts) -> Agent:
        return Agent(
            client=client,
            instructions=instructions,
            name=nom,
            description=description,
            default_options=opts,
        )

    manager = fabrique_agent(
        "manageur", INSTR_MANAGER, "Decoupe la demande et confie chaque tache au bon specialiste.",
        options_manager,
    )
    tech = fabrique_agent(
        "specialiste_technique", INSTR_TECH, "Problemes techniques: GPU, CUDA, entrainement.",
        options,
    )
    form = fabrique_agent(
        "specialiste_formation", INSTR_FORM, "Conseils de parcours et formations IA.",
        options,
    )

    builder = MagenticBuilder(
        participants=[tech, form],
        manager=StandardMagenticManager(
            agent=manager,
            max_round_count=1,
            max_stall_count=1,
        ),
    )
    resultats = {}
    for attendu, entree in ENTREES:
        pour_entree = []
        for tour in (1, 2):
            workflow = builder.build()
            message = Message(role="user", contents=[Content(type="text", text=entree)])
            resultat = await workflow.run(message)
            seq = auteurs(resultat)
            decision = (
                "specialiste_technique" if any("technique" in a for a in seq)
                else "specialiste_formation" if any("formation" in a for a in seq)
                else "(aucun)"
            )
            pour_entree.append(decision)
            print(f"[MG {attendu} #{tour}] agents={seq} participation: {decision}")
        resultats[attendu] = pour_entree
    return resultats


async def main() -> int:
    client = CountingClient(
        api_key=load_api_key(),
        base_url=OPENAI_BASE,
        model=MODEL_ID,
    )

    print(f"MAF versions: {maf_versions()}")
    await sonde(client)
    print(f"sonde OK ({llm_calls} appel(s))")

    options = ChatOptions(temperature=0.0, max_tokens=MAX_TOKENS)

    gc = await banc_groupchat(client, options)
    apres_gc = llm_calls
    mg = await banc_magentic(client, options)

    ok_gc_tech = all("technique" in d for d in gc["technique"])
    ok_gc_form = all("formation" in d for d in gc["formation"])
    det_gc = all(len(set(v)) == 1 for v in gc.values())
    ok_mg_tech = all("technique" in d for d in mg["technique"])
    ok_mg_form = all("formation" in d for d in mg["formation"])
    det_mg = all(len(set(v)) == 1 for v in mg.values())

    print(f"GC ROUTING CORRECTNESS: {'OK' if (ok_gc_tech and ok_gc_form) else 'ECHEC'}")
    print(f"GC ROUTING DETERMINISM: {'OK' if det_gc else 'ECHEC'}")
    print(f"MG PARTICIPATION CORRECTNESS: {'OK' if (ok_mg_tech and ok_mg_form) else 'ECHEC'}")
    print(f"MG PARTICIPATION DETERMINISM: {'OK' if det_mg else 'ECHEC'}")
    print(f"LLM CALLS: total {llm_calls}/{BUDGET} (groupchat {apres_gc - 1}, magentic {llm_calls - apres_gc})")
    ok = ok_gc_tech and ok_gc_form and det_gc and ok_mg_tech and ok_mg_form and det_mg
    print(f"PILOT OK maf groupchat+magentic model={MODEL_ID}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(asyncio.run(main()))
