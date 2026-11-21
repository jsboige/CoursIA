"""Pilote T3 (issue #14499) : orchestration multi-agents Google ADK.

Invoque l'organe du track -- utils/adk_runtime.py (run_agent_turn, build_agent)
et utils/adk_orchestrator.py (AdkOrchestrator, designation C4) -- sans aucune
reimplementation. Deux observables, sur le meme service LLM reel que le pilote
T2 SK (gpt-4o-mini, temperature 0, max_tokens 200, cle lue dans master.env,
jamais affichee) :

1. Handoff natif C5 : le triage transfere vers specialiste_technique |
   specialiste_formation via transfer_to_agent (outil injecte par ADK via
   sub_agents). Determinisme exige : l'agent qui TERMINE la tache doit etre
   identique sur 2 executions de chaque entree -- decisions structurantes,
   jamais la prose (doctrine du doc d'evaluation, parite avec T2).
2. Designation C4 : AdkOrchestrator execute une chaine de 2 specialistes selon
   un plan DECLARE par l'appelant avant tout appel LLM ; l'ordre des mains
   (agent_hands) doit suivre le plan exactement.

Budget ex-post : <= 12 appels LLM au total (chaque appel contribue un snapshot
d'usage, contrat C6 de l'organe). L'execution echoue proprement (exit 2) si le
runtime reel est injoignable (AdkRuntimeUnavailable -> RECOVERABLE-LOCAL).
"""

import asyncio
import os
import sys
from pathlib import Path

TRACK_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(TRACK_ROOT))

import google.adk
from google.genai import types

from config.providers import ProviderConfig, ProviderType
from utils.adk_orchestrator import AdkOrchestrator
from utils.adk_runtime import AdkRuntimeUnavailable, build_agent, run_agent_turn

# Racine du depot depuis ce fichier : eval-pilots -> Track2 -> DataScienceWithAgents -> ML -> MyIA.AI.Notebooks -> racine
MASTER_ENV = Path(__file__).resolve().parents[5] / ".secrets" / "master.env"
OPENAI_BASE = "https://api.openai.com/v1"
BUDGET = 12

INPUTS: dict[str, str] = {
    "technique": "Comment configurer le kernel Semantic Kernel en C# pour appeler une API OpenAI ?",
    "formation": "Quel notebook suivre pour apprendre les agents dans la serie GenAI ?",
}
EXPECTED = {"technique": "specialiste_technique", "formation": "specialiste_formation"}

INSTR_TRIAGE = (
    "Tu es l'agent de triage du support CoursIA. Tu ne reponds jamais directement au user. "
    "Pour toute question TECHNIQUE (code, configuration du kernel, API, erreur, compilation), "
    "appelle immediatement transfer_to_agent vers specialiste_technique. "
    "Pour toute question de FORMATION ou de PEDAGOGIE (quel notebook suivre, comment apprendre, "
    "parcours), appelle immediatement transfer_to_agent vers specialiste_formation. "
    "Tu decides immediatement, tu ne poses jamais de question."
)
INSTR_TECH = (
    "Tu es le specialiste technique de CoursIA (Semantic Kernel, C#, Python). "
    "Reponds a la question en UNE phrase courte en francais."
)
INSTR_FORMA = (
    "Tu es le specialiste formation de CoursIA (parcours de notebooks pedagogiques). "
    "Reponds a la question en UNE phrase courte en francais."
)
INSTR_ANALYSEUR = (
    "Tu es l'analyseur d'une chaine de traitement. Reponds en UNE phrase qui liste "
    "les deux points cles de la demande."
)
INSTR_SYNTHE = (
    "Tu es le synthetiseur d'une chaine de traitement. Tu vois la reponse de "
    "l'analyseur dans l'historique de la session. Reponds en UNE phrase de synthese."
)
CHAIN_PROMPT = (
    "Analyse cette demande d'apprentissage : un etudiant veut maitriser les "
    " moteurs d'agents (Semantic Kernel, Google ADK, MS Agent Framework) via des notebooks executes."
)


def load_api_key() -> str:
    """Lit OPENAI_API_KEY dans master.env (repli: variable d'environnement, en dernier
    recours -- sur certains postes les env OpenAI pointent vers un proxy local)."""
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
    raise SystemExit("ERREUR: OPENAI_API_KEY absent de " + MASTER_ENV)


def pin_temperature(agent, temperature: float = 0.0) -> None:
    """Epingle la temperature via le champ PUBLIC generate_content_config de l'Agent.

    L'organe (build_agent) n'expose pas la temperature ; ce champ public ADK
    est fusionne dans les parametres de generation APRES les kwargs du
    constructeur LiteLlm -- il gagne donc sur tout defaut, sans toucher l'organe.
    """
    agent.generate_content_config = types.GenerateContentConfig(temperature=temperature)


async def run_handoff_part(config: ProviderConfig) -> tuple[dict[str, list[str]], int]:
    """Partie 1 : handoff natif C5, meme scenario que le pilote T2 SK."""
    tech = build_agent(
        name="specialiste_technique",
        description="Specialiste des questions techniques (code, kernel, API, erreurs).",
        instruction=INSTR_TECH,
        config=config,
    )
    forma = build_agent(
        name="specialiste_formation",
        description="Specialiste des questions de formation (notebooks, parcours, pedagogie).",
        instruction=INSTR_FORMA,
        config=config,
    )
    triage = build_agent(
        name="triage",
        description="Agent de triage : transfere vers le specialiste adapte.",
        instruction=INSTR_TRIAGE,
        sub_agents=(tech, forma),
        config=config,
    )
    for agent in (triage, tech, forma):
        pin_temperature(agent)
    # Sans ces drapeaux publics, un sous-agent peut transferer VERS SON PARENT
    # (retour au triage) : boucle de transferts jusqu'au timeout, mesure sur
    # cet organe le 2026-10-05 (ADK 2.8.0). Le triage, racine, garde ses
    # transferts vers ses enfants.
    for specialist in (tech, forma):
        specialist.disallow_transfer_to_parent = True
        specialist.disallow_transfer_to_peers = True

    routes: dict[str, list[str]] = {}
    llm_calls = 0
    for branch, question in INPUTS.items():
        routes[branch] = []
        for run_index in (1, 2):
            result = await run_agent_turn(triage, question)
            llm_calls += len(result.usage_turns)
            routes[branch].append(result.final_agent)
            print(f"[{branch} #{run_index}] final_agent: {result.final_agent} | events: {result.event_count}")
    return routes, llm_calls


async def run_chain_part(config: ProviderConfig) -> tuple[list[str], int]:
    """Partie 2 : designation C4 -- le plan declare pilote la chaine."""
    analyseur = build_agent(
        name="analyseur",
        description="Premiere etape de la chaine : extrait les points cles.",
        instruction=INSTR_ANALYSEUR,
        config=config,
    )
    synthetiseur = build_agent(
        name="synthetiseur",
        description="Deuxieme etape de la chaine : condense la reponse precedente.",
        instruction=INSTR_SYNTHE,
        config=config,
    )
    for agent in (analyseur, synthetiseur):
        pin_temperature(agent)

    orchestrator = AdkOrchestrator(
        [analyseur, synthetiseur],
        plan=("analyseur", "synthetiseur"),
    )
    result = await orchestrator.run_chain(CHAIN_PROMPT)
    hands = [author for author in result.agent_hands if author != "user"]
    print(f"[chaine C4] mains: {' -> '.join(hands)} | events: {result.event_count}")
    return hands, len(result.usage_turns)


async def main() -> int:
    api_key = load_api_key()
    config = ProviderConfig(
        provider=ProviderType.OPENAI,
        model="gpt-4o-mini",
        api_key=api_key,
        base_url=OPENAI_BASE,
        max_tokens=200,
    )

    routes, calls_handoff = await run_handoff_part(config)
    hands, calls_chain = await run_chain_part(config)
    llm_calls = calls_handoff + calls_chain

    deterministic = all(len(set(r)) == 1 for r in routes.values())
    correct = all(r[0] == EXPECTED[b] for b, r in routes.items())
    plan_followed = hands == ["analyseur", "synthetiseur"]
    verdict = "OK" if (deterministic and correct and plan_followed) else "FAIL"

    print(f"ROUTING DETERMINISM: {'OK' if deterministic and correct else 'FAIL'}")
    print(f"PLAN ORDER (C4): {'OK' if plan_followed else 'FAIL'}")
    print(f"LLM CALLS: {llm_calls}/{BUDGET} (ex-post, snapshots d'usage C6)")
    print(f"PILOT OK adk={google.adk.__version__} orchestration=transfer_to_agent+AdkOrchestrator")
    return 0 if verdict == "OK" and llm_calls <= BUDGET else 1


if __name__ == "__main__":
    try:
        sys.exit(asyncio.run(main()))
    except SystemExit:
        raise
    except AdkRuntimeUnavailable as exc:
        print(str(exc)[:300])
        sys.exit(2)
    except BaseException as exc:  # erreur exacte, jamais la cle
        print(f"ERREUR FATALE {type(exc).__name__}: {str(exc)[:300]}")
        sys.exit(2)
