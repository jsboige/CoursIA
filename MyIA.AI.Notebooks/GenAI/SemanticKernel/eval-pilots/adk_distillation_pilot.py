"""Pilote P3 (issue #14499, point 3) : la MEME charge de distillation, moteur ADK.

Troisieme et derniere replique du pilote identique. Ce qui ne change PAS par
rapport a P1 (SK, `sk_distillation_pilot.py`) et P2 (MAF,
`maf_distillation_pilot.py`) :
- la charge : la fixture figee `distill_charge_fixture.md` (cellules 0..8 de
  01-SemanticKernel-Intro.ipynb, tete 8e9eaaaa0, cellule 8 tronquee declaree) ;
- les trois roles et leurs instructions : producteur (<= 120 mots), critique a
  verdict impose (`VERDICT: ACCEPTE|REVISION:`), arbitre (`DECISION:`) ;
- la politique de tour : producteur -> critique -> [revision -> producteur ->
  critique] -> arbitre, au plus 2 tours ;
- le modele EPINGLE `gpt-4o-mini`, temperature 0 (aucune sonde ne bascule) ;
- les mesures : LOC, appels LLM (budget dur), latence par appel et mur,
  comportement en echec (sonde a type nomme), determinisme sur la DECISION.

Ce qui change : L'ORGANE, et la nature de la designation. Ni SK ni MAF n'ont
l'idiome ADK : il n'existe pas de manager de group-chat. La politique de tour
vit dans une **boucle Python de designation explicite** (contrat C4 de l'organe
`AdkOrchestrator`) : notre code decide QUI PARLE ENSUITE, puis invoque l'agent
designe sur une SESSION PARTAGEE (`InMemorySessionService`), de sorte que chaque
role voit l'historique complet. La ou SK/MAF decident du prochain orateur a
chaque tour (selection function / manager), ADK execute une designation posee
par l'appelant -- la boucle conditionnelle est donc ecrite dans NOTRE code,
exactement la difference de nature que le point 3 veut mesurer.

Reutilise l'organe du track (`utils/adk_runtime.build_agent`, primitives ADK
publiques Runner/InMemorySessionService) -- aucune reimplementation du moteur.
"""

import asyncio
import os
import re
import sys
import time
from pathlib import Path

TRACK_ROOT = Path(__file__).resolve().parents[3] / "ML" / "DataScienceWithAgents" / "Track2-GoogleADK"
sys.path.insert(0, str(TRACK_ROOT))

import google.adk
from google.adk.runners import Runner
from google.adk.sessions import InMemorySessionService
from google.genai import types

from config.providers import ProviderConfig, ProviderType
from utils.adk_runtime import APP_NAME, AdkRuntimeUnavailable, build_agent

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


# Instructions : IDENTIQUES a P1/P2, mot pour mot (la comparaison le doit).
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


def pin_temperature(agent, temperature: float = 0.0) -> None:
    """Epingle la temperature via le champ PUBLIC generate_content_config (lecon T3 :
    fusionne APRES les kwargs du constructeur LiteLlm, donc gagne sur tout defaut)."""
    agent.generate_content_config = types.GenerateContentConfig(temperature=temperature)


async def run_role(agent, session_service, session_id: str, prompt: str | None) -> str:
    """Un tour de parole du role designe sur la session partagee.

    Designation explicite (C4) : `prompt` porte la charge au premier role, puis
    une consigne de designation aux roles suivants. L'historique complet reste
    visible dans la session partagee ; le prompt designe le role, il ne re-donne
    pas la charge. Compte l'appel LLM (budget dur) et mesure la latence.
    """
    global llm_calls
    llm_calls += 1
    if llm_calls > BUDGET:
        raise RuntimeError(f"Budget LLM depasse ({llm_calls}/{BUDGET})")

    message = types.Content(role="user", parts=[types.Part(text=prompt)]) if prompt is not None else None
    runner = Runner(agent=agent, app_name=APP_NAME, session_service=session_service)
    started = time.perf_counter()
    final_text = ""
    try:
        async for event in runner.run_async(
            user_id="track2-user",
            session_id=session_id,
            new_message=message,
        ):
            if event.is_final_response():
                content = getattr(event, "content", None)
                if content and content.parts:
                    final_text = "".join(part.text or "" for part in content.parts).strip()
    finally:
        await runner.close()
    elapsed = time.perf_counter() - started
    call_log.append({"agent": agent.name, "latency_s": round(elapsed, 2)})
    if not final_text:
        raise AdkRuntimeUnavailable(f"RECOVERABLE-LOCAL: le role {agent.name} n'a produit aucune reponse finale")
    return final_text


def selection_distillation(auteurs: list[str], dernier_verdict: str) -> str:
    """La politique de tour, dans l'idiome ADK : une fonction de DESIGNATION que
    notre boucle appelle entre les tours (le moteur n'a pas de selection
    function native -- c'est l'appelant qui designe).

    Meme logique que P1/P2 : au depart le producteur ; apres le producteur le
    critique ; apres le critique, l'arbitre si ACCEPTE, sinon le producteur tant
    que le budget de tours le permet ; apres l'arbitre, la boucle s'arrete.
    """
    if not auteurs:
        return PRODUCTEUR
    dernier = auteurs[-1]
    if dernier == PRODUCTEUR:
        return CRITIQUE
    if dernier == CRITIQUE:
        if "VERDICT: ACCEPTE" in dernier_verdict:
            return ARBITRE
        tours_produits = sum(1 for a in auteurs if a == PRODUCTEUR)
        if tours_produits < MAX_TOURS:
            return PRODUCTEUR
        return ARBITRE
    return ARBITRE  # etat terminal : la boucle scelle apres l'arbitre


async def run_distillation(config: ProviderConfig, charge: str, session_id: str) -> dict:
    """Une execution complete de la boucle de designation ; retourne les mesures."""
    agents = {
        PRODUCTEUR: build_agent(
            name=PRODUCTEUR,
            description="Redige la distillation pedagogique de la section (au plus 120 mots).",
            instruction=INSTR_PRODUCTEUR,
            config=config,
        ),
        CRITIQUE: build_agent(
            name=CRITIQUE,
            description="Verifie exactitude, absence d'invention et concision ; rend VERDICT: ACCEPTE ou REVISION.",
            instruction=INSTR_CRITIQUE,
            config=config,
        ),
        ARBITRE: build_agent(
            name=ARBITRE,
            description="Scelle le resultat : DECISION: ACCEPTE tour N, ou RESIDUEL tour N.",
            instruction=INSTR_ARBITRE,
            config=config,
        ),
    }
    for agent in agents.values():
        pin_temperature(agent)

    session_service = InMemorySessionService()
    await session_service.create_session(app_name=APP_NAME, user_id="track2-user", session_id=session_id)

    started = time.perf_counter()
    auteurs: list[str] = []
    textes: dict[str, list[str]] = {PRODUCTEUR: [], CRITIQUE: [], ARBITRE: []}
    dernier_verdict = ""

    # Boucle de designation explicite : on decide du prochain orateur, on
    # l'invoque avec un prompt de designation, on lit son verdict, on re-designe.
    # Le prompt de designation est EXPLICITE a chaque tour : passer prompt=None
    # laisserait ADK router par handoff implicite ("Event from an unknown
    # agent", mesure) au lieu d'invoquer le role designe. L'historique complet
    # reste visible dans la session partagee ; le prompt ne fait que designer.
    consignes = {
        PRODUCTEUR: "A toi de jouer, producteur : redige (ou revise) la distillation de la section ci-dessus.",
        CRITIQUE: "A toi de jouer, critique : rends ton VERDICT sur la derniere distillation proposee.",
        ARBITRE: "A toi de jouer, arbitre : scelle la DECISION sur l'historique ci-dessus.",
    }
    while True:
        prochain = selection_distillation(auteurs, dernier_verdict)
        prompt = charge if not auteurs else consignes[prochain]
        texte = await run_role(agents[prochain], session_service, session_id, prompt)
        auteurs.append(prochain)
        textes[prochain].append(texte)
        if prochain == CRITIQUE:
            dernier_verdict = texte
        if prochain == ARBITRE:
            break
        if len(auteurs) > MAX_TOURS * 3 + 1:  # garde-fou structurel
            break

    wall_s = round(time.perf_counter() - started, 2)

    tours = max(1, sum(1 for a in auteurs if a == PRODUCTEUR))
    decision = ""
    for texte in textes[ARBITRE]:
        for ligne in texte.splitlines():
            if ligne.strip().startswith("DECISION:"):
                decision = ligne.strip()
                break
    last_verdict = "?"
    for texte in reversed(textes[CRITIQUE]):
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


async def sonde(config: ProviderConfig) -> str:
    """Sonde le modele epingle avec 1 appel minuscule ; echoue fort, ne bascule jamais."""
    global llm_calls
    llm_calls += 1
    agent = build_agent(name="sonde", description="Sonde", instruction="Reponds exactement: OK", config=config)
    pin_temperature(agent)
    session_service = InMemorySessionService()
    sid = "sonde-probe"
    await session_service.create_session(app_name=APP_NAME, user_id="track2-user", session_id=sid)
    runner = Runner(agent=agent, app_name=APP_NAME, session_service=session_service)
    text = ""
    try:
        async for event in runner.run_async(
            user_id="track2-user",
            session_id=sid,
            new_message=types.Content(role="user", parts=[types.Part(text="ping")]),
        ):
            if event.is_final_response():
                content = getattr(event, "content", None)
                if content and content.parts:
                    text = "".join(p.text or "" for p in content.parts).strip()
    finally:
        await runner.close()
    return text[:20] or "OK"


async def sonde_echec(api_key: str) -> str:
    """Comportement en echec : un modele inexistant doit echouer avec un type nomme."""
    config = ProviderConfig(
        provider=ProviderType.OPENAI,
        model="ce-modele-n-existe-pas",
        api_key=api_key,
        base_url=OPENAI_BASE,
        max_tokens=MAX_TOKENS,
    )
    agent = build_agent(name="sonde_echec", description="Sonde", instruction="Reponds: OK", config=config)
    pin_temperature(agent)
    session_service = InMemorySessionService()
    sid = "sonde-echec"
    await session_service.create_session(app_name=APP_NAME, user_id="track2-user", session_id=sid)
    runner = Runner(agent=agent, app_name=APP_NAME, session_service=session_service)
    try:
        async for _ in runner.run_async(
            user_id="track2-user",
            session_id=sid,
            new_message=types.Content(role="user", parts=[types.Part(text="ping")]),
        ):
            pass
    except Exception as exc:  # l'erreur exacte, jamais la cle
        return f"{type(exc).__name__}"
    finally:
        await runner.close()
    return "AUCUNE_ERREUR (inespere)"


def structure_decision(decision: str) -> tuple:
    """Structure, jamais la prose : type de decision + entier du tour d'arbitrage."""
    type_decision = "ACCEPTE" if "ACCEPTE" in decision else ("RESIDUEL" if "RESIDUEL" in decision else "?")
    match = re.search(r"tour\s+(\d+)", decision)
    tour = match.group(1) if match else "?"
    return (type_decision, tour)


async def main() -> int:
    api_key = load_api_key()
    config = ProviderConfig(
        provider=ProviderType.OPENAI,
        model=MODEL_ID,
        api_key=api_key,
        base_url=OPENAI_BASE,
        max_tokens=MAX_TOKENS,
    )

    try:
        pong = await sonde(config)
        print(f"probe {MODEL_ID}: OK -> {pong}")
    except Exception as exc:
        print(f"probe {MODEL_ID}: ECHEC {type(exc).__name__}: {str(exc)[-200:]}")
        print("Modele de comparaison epingle : aucun repli automatique (exit 2).")
        return 2

    print(f"ADK version: google-adk {google.adk.__version__}")
    failure = await sonde_echec(api_key)
    print(f"sonde echec (modele inexistant): {failure}")
    if failure.startswith("AUCUNE_ERREUR"):
        print("Sonde d'echec non concluante : le faux modele n'a pas leve d'erreur (exit 3).")
        return 3

    charge = FIXTURE.read_text(encoding="utf-8")
    print(f"charge: {FIXTURE.name} ({len(charge)} caracteres, fixture figee)")

    runs = []
    for run_index in (1, 2):
        before_calls = llm_calls
        before_log = len(call_log)
        summary = await run_distillation(config, charge, session_id=f"distill-run-{run_index}-{int(time.time())}")
        runs.append(summary)
        print(f"[run {run_index}] tours={summary['tours']} verdict_critique={summary['last_verdict']} "
              f"wall={summary['wall_s']}s appels={llm_calls - before_calls}")
        print(f"    sequence: {' -> '.join(summary['speakers'])}")
        print(f"    decision: {summary['decision'][:100]}")
        for entry in call_log[before_log:]:
            print(f"    appel[{entry['agent']}]: latence={entry['latency_s']}s")

    struct1 = (runs[0]["tours"],) + structure_decision(runs[0]["decision"])
    struct2 = (runs[1]["tours"],) + structure_decision(runs[1]["decision"])
    decision_presente = all(r["decision"] for r in runs)
    deterministic = decision_presente and struct1 == struct2
    print(f"DETERMINISME (tours, decision, tour d'arbitrage): {'OK' if deterministic else 'FAIL'} {struct1} vs {struct2}")
    print(f"LLM CALLS: {llm_calls}/{BUDGET}")
    print(f"LOC PILOT: {len(Path(__file__).read_text(encoding='utf-8').splitlines())} lignes")
    verdict_final = "PILOT OK" if deterministic else "PILOT FAIL"
    print(f"{verdict_final} orchestration=ADK(designation explicite, session partagee) charge=distillation")
    return 0 if deterministic else 1


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
