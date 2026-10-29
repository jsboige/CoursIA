"""Pilote P1 (issue #14499, point 3) : la charge de distillation partagee, moteur Semantic Kernel.

Premiere replique du pilote identique dans les trois moteurs (protocole en tete du
body, mandat user 2026-09-23) : trois agents -- producteur, critique, arbitre --
distillent une section REELLE d'un carnet du depot (fixture figee
`distill_charge_fixture.md`, cellules 0..8 de 01-SemanticKernel-Intro.ipynb) sur
au plus deux tours.

Ce qui est delegue au MOTEUR ici : la boucle de conversation conditionnelle --
un `GroupChatOrchestration` pilote par un manager CUSTOM
(`DistillationGroupChatManager.select_next_agent` encode producteur ->
critique -> [revision -> producteur -> critique] -> arbitre,
`should_terminate` scelle apres l'arbitre). C'est l'idiome SK de la boucle de
refinement ; les repliques P2 (MAF, graphe type) et P3 (ADK, boucle) encodent la
MEME politique dans l'idiome de leur moteur, sur la MEME fixture.

Mesures du protocole (point 3) portees par ce pilote :
- lignes de code du pilote (self-mesure) ;
- appels LLM (budget dur) et jetons par appel, lus dans les metadonnees de
  reponse quand l'API les rend ;
- latence par appel et totale ;
- comportement en echec : une sonde sur un modele inexistant doit echouer FORT
  avec un type nomme, sans jamais afficher la cle ;
- determinisme : la DECISION (nombre de tours + ligne DECISION de l'arbitre)
  doit etre identique sur 2 executions -- jamais la prose.

Modele EPINGLE gpt-4o-mini, temperature 0 (meme doctrine que T2-T8 : le modele
ne se choisit pas a l'execution, la sonde echoue fort au lieu de basculer).
Budget dur : 16 appels LLM au total (sondes comprises).
"""

import asyncio
import os
import sys
import time
from pathlib import Path

import semantic_kernel
from openai import AsyncOpenAI
from semantic_kernel import Kernel
from semantic_kernel.agents import (
    ChatCompletionAgent,
    GroupChatManager,
    GroupChatOrchestration,
)
from semantic_kernel.agents.orchestration.group_chat import (
    BooleanResult,
    MessageResult,
    StringResult,
)
from semantic_kernel.agents.runtime import InProcessRuntime
from semantic_kernel.connectors.ai.open_ai import OpenAIChatCompletion
from semantic_kernel.connectors.ai.open_ai.prompt_execution_settings.open_ai_prompt_execution_settings import (
    OpenAIChatPromptExecutionSettings,
)
from semantic_kernel.contents import ChatHistory
from semantic_kernel.contents.chat_message_content import ChatMessageContent
from semantic_kernel.functions import KernelArguments

HERE = Path(__file__).resolve().parent
MASTER_ENV = HERE.parents[3] / ".secrets" / "master.env"
FIXTURE = HERE / "distill_charge_fixture.md"
OPENAI_BASE = "https://api.openai.com/v1"
BUDGET = 16
MODEL = "gpt-4o-mini"
MAX_TOURS = 2

PRODUCTEUR = "producteur"
CRITIQUE = "critique"
ARBITRE = "arbitre"

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

llm_calls = 0
call_log: list[dict] = []


def load_api_key() -> str:
    """Lit OPENAI_API_KEY dans master.env (repli: variable d'environnement)."""
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


class CountingOpenAI(OpenAIChatCompletion):
    """Connecteur qui compte chaque appel LLM (jette au-dela du budget) et mesure
    latence + jetons quand la reponse les porte."""

    async def get_chat_message_contents(self, *args, **kwargs):
        global llm_calls
        llm_calls += 1
        if llm_calls > BUDGET:
            raise RuntimeError(f"Budget LLM depasse ({llm_calls}/{BUDGET})")
        started = time.perf_counter()
        results = await super().get_chat_message_contents(*args, **kwargs)
        elapsed = time.perf_counter() - started
        usage = None
        for msg in results:
            meta = getattr(msg, "metadata", None) or {}
            if isinstance(meta, dict) and meta.get("usage") is not None:
                usage = meta["usage"]
                break
        call_log.append({"latency_s": round(elapsed, 2), "usage": usage, "mode": "complet"})
        return results

    async def get_streaming_chat_message_contents(self, *args, **kwargs):
        """L'orchestration GroupChat appelle les agents en STREAMING (lecon P1 :
        sans cet override, les appels d'agents echappent au compteur)."""
        global llm_calls
        llm_calls += 1
        if llm_calls > BUDGET:
            raise RuntimeError(f"Budget LLM depasse ({llm_calls}/{BUDGET})")
        started = time.perf_counter()
        usage = None
        async for item in super().get_streaming_chat_message_contents(*args, **kwargs):
            meta = getattr(item, "metadata", None) or {}
            if isinstance(meta, dict) and meta.get("usage") is not None:
                usage = meta["usage"]
            yield item
        elapsed = time.perf_counter() - started
        call_log.append({"latency_s": round(elapsed, 2), "usage": usage, "mode": "stream"})


def make_service(model_id: str, api_key: str) -> "CountingOpenAI":
    """base_url explicite : les env OpenAI du poste pointent vers un proxy local."""
    client = AsyncOpenAI(api_key=api_key, base_url=OPENAI_BASE, max_retries=1)
    return CountingOpenAI(ai_model_id=model_id, async_client=client)


async def probe_model(api_key: str, model_id: str) -> str:
    """Sonde un modele avec 1 appel minuscule ; echoue fort (exit 2), ne bascule jamais."""
    service = make_service(model_id, api_key)
    history = ChatHistory()
    history.add_user_message("Reponds exactement: OK")
    settings = OpenAIChatPromptExecutionSettings(temperature=0.0, max_completion_tokens=16)
    result = await service.get_chat_message_contents(chat_history=history, settings=settings)
    return (result[0].content or "").strip()


async def probe_failure(api_key: str) -> str:
    """Comportement en echec : un modele inexistant doit echouer avec un type nomme."""
    service = make_service("ce-modele-n-existe-pas", api_key)
    history = ChatHistory()
    history.add_user_message("Reponds: OK")
    settings = OpenAIChatPromptExecutionSettings(temperature=0.0, max_completion_tokens=16)
    try:
        await service.get_chat_message_contents(chat_history=history, settings=settings)
    except Exception as exc:  # l'erreur exacte, jamais la cle
        return f"{type(exc).__name__}"
    return "AUCUNE_ERREUR (inespere)"


def _speaker_names(history: ChatHistory) -> list[str]:
    return [m.name for m in history.messages if getattr(m, "name", None)]


def _last_message_from(history: ChatHistory, agent: str) -> str:
    for msg in reversed(history.messages):
        if getattr(msg, "name", None) == agent:
            return (msg.content or "").strip()
    return ""


class DistillationGroupChatManager(GroupChatManager):
    """La politique de tour, encodee dans l'idiome SK : le manager CHOISIT le
    prochain locuteur selon le verdict du critique et scelle apres l'arbitre.

    C'est la piece que les repliques P2/P3 re-encodent dans l'idiome de leur
    moteur (graphe type / boucle) : la politique est identique, l'organe change.
    """

    revision_count: int = 0

    async def filter_results(self, chat_history: ChatHistory) -> MessageResult:
        """Comportement par defaut : le resultat de l'orchestration est le dernier message."""
        return MessageResult(
            result=chat_history.messages[-1] if chat_history.messages else None,
            reason="dernier message de l'historique",
        )

    async def should_request_user_input(self, chat_history: ChatHistory) -> BooleanResult:
        """Jamais d'entree user : la charge est autonome."""
        return BooleanResult(result=False, reason="charge autonome")

    async def select_next_agent(
        self, chat_history: ChatHistory, participant_descriptions: dict[str, str]
    ) -> StringResult:
        names = _speaker_names(chat_history)
        if not names:
            return StringResult(result=PRODUCTEUR, reason="tour 1 : premiere distillation")
        last = names[-1]
        if last == PRODUCTEUR:
            return StringResult(result=CRITIQUE, reason="distillation produite -> critique")
        if last == CRITIQUE:
            verdict = _last_message_from(chat_history, CRITIQUE)
            if "VERDICT: ACCEPTE" in verdict:
                return StringResult(result=ARBITRE, reason="critique accepte -> arbitre")
            if self.revision_count < MAX_TOURS - 1:
                self.revision_count += 1
                return StringResult(result=PRODUCTEUR, reason="REVISION -> tour 2 du producteur")
            return StringResult(result=ARBITRE, reason="budget de tours epuise -> arbitre")
        return StringResult(result=ARBITRE, reason="etat terminal -> arbitre")

    async def should_terminate(self, chat_history: ChatHistory) -> BooleanResult:
        names = _speaker_names(chat_history)
        if names and names[-1] == ARBITRE:
            return BooleanResult(result=True, reason="l'arbitre a parle")
        if len(names) >= MAX_TOURS * 3:  # garde-fou structurel, jamais atteint normalement
            return BooleanResult(result=True, reason="plafond de messages")
        return BooleanResult(result=False, reason="boucle en cours")


async def run_distillation(kernel: Kernel, arguments: KernelArguments, charge: str) -> dict:
    """Une execution complete de la boucle ; retourne le releve de mesures."""
    producteur = ChatCompletionAgent(
        kernel=kernel, name=PRODUCTEUR, instructions=INSTR_PRODUCTEUR, arguments=arguments,
        description="Redige la distillation pedagogique de la section (au plus 120 mots).",
    )
    critique = ChatCompletionAgent(
        kernel=kernel, name=CRITIQUE, instructions=INSTR_CRITIQUE, arguments=arguments,
        description="Verifie exactitude, absence d'invention et concision ; rend VERDICT: ACCEPTE ou REVISION.",
    )
    arbitre = ChatCompletionAgent(
        kernel=kernel, name=ARBITRE, instructions=INSTR_ARBITRE, arguments=arguments,
        description="Scelle le resultat : DECISION: ACCEPTE tour N, ou RESIDUEL tour N.",
    )
    manager = DistillationGroupChatManager()
    messages: list[ChatMessageContent] = []
    orchestration = GroupChatOrchestration(
        members=[producteur, critique, arbitre],
        manager=manager,
        agent_response_callback=messages.append,
    )
    runtime = InProcessRuntime()
    runtime.start()  # methode synchrone en sk 1.41.3 (l'await leve TypeError)
    started = time.perf_counter()
    try:
        result = await orchestration.invoke(task=charge, runtime=runtime)
        final = await asyncio.wait_for(result.get(), timeout=300)
    finally:
        await asyncio.wait_for(runtime.stop_when_idle(), timeout=30)
    wall_s = round(time.perf_counter() - started, 2)

    speakers = [getattr(m, "name", "?") for m in messages]
    tours = max(1, speakers.count(PRODUCTEUR))
    decision = ""
    for msg in reversed(messages):
        if getattr(msg, "name", None) == ARBITRE and "DECISION:" in (msg.content or ""):
            decision = [l.strip() for l in (msg.content or "").splitlines() if l.strip().startswith("DECISION:")][0]
            break
    last_verdict = "ACCEPTE" if "VERDICT: ACCEPTE" in _last_message_from_chat(messages) else "REVISION"
    return {
        "speakers": speakers,
        "tours": tours,
        "decision": decision,
        "last_verdict": last_verdict,
        "wall_s": wall_s,
        "final": (getattr(final, "content", "") or "").strip()[:120],
    }


def _last_message_from_chat(messages: list[ChatMessageContent]) -> str:
    for msg in reversed(messages):
        if getattr(msg, "name", None) == CRITIQUE:
            return (msg.content or "").strip()
    return ""


def _fmt_usage(usage) -> str:
    if usage is None:
        return "n/d"
    if isinstance(usage, dict):
        return f"in={usage.get('prompt_tokens', '?')} out={usage.get('completion_tokens', '?')}"
    return str(usage)[:60]


async def main() -> int:
    api_key = load_api_key()

    # Modele epingle : la sonde atteste le service sur CE modele, aucun repli (exit 2).
    try:
        pong = await probe_model(api_key, MODEL)
        print(f"probe {MODEL}: OK -> {pong[:20]}")
    except Exception as exc:
        print(f"probe {MODEL}: ECHEC {type(exc).__name__}: {str(exc)[-200:]}")
        print("Modele de comparaison epingle : aucun repli automatique (exit 2).")
        return 2

    # Comportement en echec : un modele inexistant doit echouer fort, type nomme.
    failure = await probe_failure(api_key)
    print(f"sonde echec (modele inexistant): {failure}")

    charge = FIXTURE.read_text(encoding="utf-8")
    print(f"charge: {FIXTURE.name} ({len(charge)} caracteres, fixture figee)")

    kernel = Kernel()
    kernel.add_service(make_service(MODEL, api_key))
    settings = OpenAIChatPromptExecutionSettings(temperature=0.0, max_completion_tokens=400)
    arguments = KernelArguments(settings=settings)

    runs = []
    for run_index in (1, 2):
        before_calls = llm_calls
        before_log = len(call_log)
        summary = await run_distillation(kernel, arguments, charge)
        runs.append(summary)
        print(f"[run {run_index}] tours={summary['tours']} verdict_final={summary['last_verdict']} "
              f"wall={summary['wall_s']}s appels={llm_calls - before_calls}")
        print(f"    sequence: {' -> '.join(summary['speakers'])}")
        print(f"    decision: {summary['decision'][:100]}")
        for entry in call_log[before_log:]:
            print(f"    appel[{entry['mode']}]: latence={entry['latency_s']}s jetons={_fmt_usage(entry['usage'])}")

    struct1 = (runs[0]["tours"], runs[0]["decision"].split(":")[0], runs[0]["decision"].split("tour")[-1].strip()[:2])
    struct2 = (runs[1]["tours"], runs[1]["decision"].split(":")[0], runs[1]["decision"].split("tour")[-1].strip()[:2])
    deterministic = struct1 == struct2
    print(f"DETERMINISME (tours, decision, tour d'arbitrage): {'OK' if deterministic else 'FAIL'} {struct1} vs {struct2}")
    print(f"LLM CALLS: {llm_calls}/{BUDGET}")
    print(f"LOC PILOT: {len(Path(__file__).read_text(encoding='utf-8').splitlines())} lignes")
    print(f"PILOT OK sk={semantic_kernel.__version__} orchestration=GroupChat(manager_custom) charge=distillation")
    return 0 if deterministic else 1


if __name__ == "__main__":
    try:
        sys.exit(asyncio.run(main()))
    except SystemExit:
        raise
    except BaseException as exc:  # erreur exacte, jamais la cle
        print(f"ERREUR FATALE {type(exc).__name__}: {str(exc)[:300]}")
        sys.exit(2)
