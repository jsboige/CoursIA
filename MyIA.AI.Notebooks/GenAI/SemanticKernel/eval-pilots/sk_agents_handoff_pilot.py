"""Pilote T2 (issue #14499) : orchestration d'agents Semantic Kernel (Handoff).

Demonstration de la couche AGENTS : 3 ChatCompletionAgent (triage + 2 specialistes)
relies par HandoffOrchestration, service OpenAI reel (cle lue dans master.env,
jamais affichee). Determinisme exige : la DECISION DE ROUTAGE (quel specialiste
termine la tache) doit etre identique sur 2 executions de chaque entree.
Budget dur : 10 appels LLM au total (sondes incluses), comptes par un compteur.
"""

import asyncio
import os
import sys
from pathlib import Path

import semantic_kernel
from openai import AsyncOpenAI
from semantic_kernel import Kernel
from semantic_kernel.agents import ChatCompletionAgent, HandoffOrchestration, OrchestrationHandoffs
from semantic_kernel.agents.runtime import InProcessRuntime
from semantic_kernel.connectors.ai.open_ai import OpenAIChatCompletion
from semantic_kernel.connectors.ai.open_ai.prompt_execution_settings.open_ai_prompt_execution_settings import (
    OpenAIChatPromptExecutionSettings,
)
from semantic_kernel.contents import ChatHistory
from semantic_kernel.contents.chat_message_content import ChatMessageContent
from semantic_kernel.functions import KernelArguments

# Racine du depot depuis ce fichier : eval-pilots/ -> SemanticKernel -> GenAI -> MyIA.AI.Notebooks -> racine
MASTER_ENV = Path(__file__).resolve().parents[4] / ".secrets" / "master.env"
OPENAI_BASE = "https://api.openai.com/v1"
BUDGET = 10
llm_calls = 0

INPUTS: dict[str, str] = {
    "technique": "Comment configurer le kernel Semantic Kernel en C# pour appeler une API OpenAI ?",
    "formation": "Quel notebook suivre pour apprendre les agents dans la serie GenAI ?",
}
EXPECTED = {"technique": "specialiste_technique", "formation": "specialiste_formation"}

INSTR_TRIAGE = (
    "Tu es l'agent de triage du support CoursIA. Tu ne reponds jamais directement au user. "
    "Pour toute question TECHNIQUE (code, configuration du kernel, API, erreur, compilation), "
    "appelle immediatement la fonction transfer_to_specialiste_technique. "
    "Pour toute question de FORMATION ou de PEDAGOGIE (quel notebook suivre, comment apprendre, "
    "parcours), appelle immediatement la fonction transfer_to_specialiste_formation. "
    "Tu decides immediatement, tu ne poses jamais de question."
)
INSTR_TECH = (
    "Tu es le specialiste technique de CoursIA (Semantic Kernel, C#, Python). "
    "Reponds a la question en UNE phrase courte en francais, puis appelle la fonction "
    "complete_task avec un resume d'une phrase."
)
INSTR_FORMA = (
    "Tu es le specialiste formation de CoursIA (parcours de notebooks pedagogiques). "
    "Reponds a la question en UNE phrase courte en francais, puis appelle la fonction "
    "complete_task avec un resume d'une phrase."
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


class CountingOpenAI(OpenAIChatCompletion):
    """Connecteur OpenAI qui compte chaque appel LLM (jette au-dela du budget)."""

    def _tick(self) -> None:
        global llm_calls
        llm_calls += 1
        if llm_calls > BUDGET:
            raise RuntimeError(f"Budget LLM depasse ({llm_calls}/{BUDGET})")

    async def get_chat_message_contents(self, *args, **kwargs):
        self._tick()
        return await super().get_chat_message_contents(*args, **kwargs)

    async def get_streaming_chat_message_contents(self, *args, **kwargs):
        self._tick()
        async for item in super().get_streaming_chat_message_contents(*args, **kwargs):
            yield item


def make_service(model_id: str, api_key: str) -> "CountingOpenAI":
    """Construit le connecteur avec base_url explicite (les variables d'environnement
    OPENAI_BASE_URL du poste pointent vers un proxy local qui rejetterait la cle)."""
    client = AsyncOpenAI(api_key=api_key, base_url=OPENAI_BASE, max_retries=1)
    return CountingOpenAI(ai_model_id=model_id, async_client=client)


async def probe_model(api_key: str, model_id: str) -> str:
    """Sonde un modele avec 1 appel minuscule ; retourne le texte ou leve l'erreur exacte."""
    service = make_service(model_id, api_key)
    history = ChatHistory()
    history.add_user_message("Reponds exactement: OK")
    settings = OpenAIChatPromptExecutionSettings(temperature=0.0, max_completion_tokens=16)
    result = await service.get_chat_message_contents(chat_history=history, settings=settings)
    return (result[0].content or "").strip()


async def run_once(question: str, members: list[ChatCompletionAgent],
                   handoffs: OrchestrationHandoffs) -> tuple[str, str]:
    """Une invocation Handoff ; retourne (nom de l'agent qui termine, reponse)."""
    messages: list[ChatMessageContent] = []
    orchestration = HandoffOrchestration(
        members=members, handoffs=handoffs, agent_response_callback=messages.append
    )
    runtime = InProcessRuntime()
    runtime.start()  # methode synchrone en sk 1.41.3 (l'await leve TypeError)
    try:
        result = await orchestration.invoke(task=question, runtime=runtime)
        final = await asyncio.wait_for(result.get(), timeout=120)
    finally:
        await asyncio.wait_for(runtime.stop_when_idle(), timeout=30)
    routed_to = getattr(final, "name", None) or "?"
    answer = ""
    for msg in messages:
        if getattr(msg, "name", None) == routed_to and (msg.content or "").strip():
            answer = msg.content.strip()
    if not answer:
        answer = (final.content or "").strip()
    return routed_to, answer


async def main() -> int:
    api_key = load_api_key()
    model = "gpt-5-mini"
    try:
        pong = await probe_model(api_key, model)
        print(f"probe {model}: OK -> {pong[:20]}")
    except Exception as exc:
        print(f"probe {model}: ECHEC {type(exc).__name__}: {str(exc)[-200:]} -> repli gpt-4o-mini")
        model = "gpt-4o-mini"
        pong = await probe_model(api_key, model)
        print(f"probe {model}: OK -> {pong[:20]}")

    kernel = Kernel()
    kernel.add_service(make_service(model, api_key))
    settings = OpenAIChatPromptExecutionSettings(temperature=0.0, max_completion_tokens=200)
    arguments = KernelArguments(settings=settings)
    triage = ChatCompletionAgent(kernel=kernel, name="triage", instructions=INSTR_TRIAGE, arguments=arguments)
    tech = ChatCompletionAgent(kernel=kernel, name="specialiste_technique", instructions=INSTR_TECH, arguments=arguments)
    formation = ChatCompletionAgent(kernel=kernel, name="specialiste_formation", instructions=INSTR_FORMA, arguments=arguments)
    members = [triage, tech, formation]
    handoffs = OrchestrationHandoffs()
    handoffs.add_many(triage, {
        "specialiste_technique": "Transfere pour toute question technique: code, kernel, API, erreurs.",
        "specialiste_formation": "Transfere pour toute question de formation: notebooks, parcours, pedagogie.",
    })

    routes: dict[str, list[str]] = {}
    for branch, question in INPUTS.items():
        routes[branch] = []
        for run_index in (1, 2):
            routed_to, answer = await run_once(question, members, handoffs)
            routes[branch].append(routed_to)
            print(f"[{branch} #{run_index}] input: {question[:50]}")
            print(f"    decision: {routed_to} | reponse: {answer[:60]}")

    deterministic = all(len(set(r)) == 1 for r in routes.values())
    correct = all(r[0] == EXPECTED[b] for b, r in routes.items())
    verdict = "OK" if (deterministic and correct) else "FAIL"
    print(f"ROUTING DETERMINISM: {verdict}")
    print(f"LLM CALLS: {llm_calls}/{BUDGET}")
    print(f"PILOT OK sk={semantic_kernel.__version__} orchestration=Handoff")
    return 0 if verdict == "OK" else 1


if __name__ == "__main__":
    try:
        sys.exit(asyncio.run(main()))
    except SystemExit:
        raise
    except BaseException as exc:  # erreur exacte, jamais la cle
        print(f"ERREUR FATALE {type(exc).__name__}: {str(exc)[:300]}")
        sys.exit(2)
