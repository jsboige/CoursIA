"""Pilote T4 (issue #14499) : les quatre modes d'orchestration SK restants.

Complement de T2 (`sk_agents_handoff_pilot.py`, mode handoff) : couvre
SEQUENTIEL, CONCURRENT, GROUP CHAT et MAGENTIC sur semantic_kernel 1.41.3,
avec un service LLM reel (cle lue dans master.env, jamais affichee).

Determinisme exige : a temperature 0, on n'asserte PAS la prose (mesure T2 :
elle varie d'un process a l'autre) mais la STRUCTURE -- quels agents parlent,
combien de tours, dans quel ordre. Chaque mode est execute DEUX fois et les
deux signatures structurelles doivent coincider.

Budget dur : 110 appels LLM au total (sonde incluse), comptes par un connecteur
instrumente qui jette au-dela. C'est un garde-fou anti-emballement, pas une
cible : le run complet en consomme 32 (mesure du 08/10, reportee dans la doc).
Le manager Magentic est borne separement (`max_round_count`) -- non borne, il
boucle et epuise ce budget.
"""

import asyncio
import os
import sys
from pathlib import Path

import semantic_kernel
from openai import AsyncOpenAI
from semantic_kernel import Kernel
from semantic_kernel.agents import (
    ChatCompletionAgent,
    ConcurrentOrchestration,
    GroupChatOrchestration,
    MagenticOrchestration,
    RoundRobinGroupChatManager,
    SequentialOrchestration,
    StandardMagenticManager,
)
from semantic_kernel.agents.runtime import InProcessRuntime
from semantic_kernel.connectors.ai.open_ai import OpenAIChatCompletion
from semantic_kernel.connectors.ai.open_ai.prompt_execution_settings.open_ai_prompt_execution_settings import (
    OpenAIChatPromptExecutionSettings,
)
from semantic_kernel.contents import ChatHistory
from semantic_kernel.contents.chat_message_content import ChatMessageContent
from semantic_kernel.functions import KernelArguments

MASTER_ENV = Path(__file__).resolve().parents[4] / ".secrets" / "master.env"
OPENAI_BASE = "https://api.openai.com/v1"
BUDGET = 110  # garde-fou anti-emballement, pas une cible : mesure du run complet dans la doc
GROUP_CHAT_ROUNDS = 3
# Bornes du manager Magentic : sans elles le manager boucle (mesure : 8 tours).
# `max_round_count` est le seul des trois a valoir None (non borne) par defaut.
MAGENTIC_ROUNDS = 2
MAGENTIC_STALLS = 2
MAGENTIC_RESETS = 1
# Borne haute de l'assertion : elle ne fait que constater que le plafond
# structurel tient (mesure : 2 tours a `max_round_count=2`, ~1 delegation par
# round ; 3 rounds mesures donnent 3 tours). Elle n'est PAS le mecanisme qui
# borne -- c'est `max_round_count` qui le fait.
MAGENTIC_MAX_TURNS = 6
llm_calls = 0


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
    raise SystemExit("ERREUR: OPENAI_API_KEY absent de " + str(MASTER_ENV))


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


def make_service(model_id: str, api_key: str) -> CountingOpenAI:
    """base_url explicite : les OPENAI_BASE_URL du poste pointent vers un proxy local."""
    client = AsyncOpenAI(api_key=api_key, base_url=OPENAI_BASE, max_retries=1)
    return CountingOpenAI(ai_model_id=model_id, async_client=client)


async def probe_model(api_key: str, model_id: str) -> str:
    service = make_service(model_id, api_key)
    history = ChatHistory()
    history.add_user_message("Reponds exactement: OK")
    settings = OpenAIChatPromptExecutionSettings(temperature=0.0, max_completion_tokens=16)
    result = await service.get_chat_message_contents(chat_history=history, settings=settings)
    return (result[0].content or "").strip()


async def invoke(build, task: str, timeout_s: float = 240):
    """Invoque une orchestration sur un runtime en process ; retourne (resultat, messages).

    `build(callback)` construit l'orchestration : le callback doit etre passe AU
    CONSTRUCTEUR -- l'affecter apres coup (`orchestration.agent_response_callback = ...`)
    est silencieusement ignore sur 1.41.3 et rend une liste de messages vide.
    """
    messages: list[ChatMessageContent] = []
    orchestration = build(messages.append)
    runtime = InProcessRuntime()
    runtime.start()  # methode synchrone en sk 1.41.3
    try:
        result = await orchestration.invoke(task=task, runtime=runtime)
        final = await asyncio.wait_for(result.get(), timeout=timeout_s)
    finally:
        await asyncio.wait_for(runtime.stop_when_idle(), timeout=30)
    return final, messages


def signature(messages: list[ChatMessageContent]) -> tuple:
    """Signature STRUCTURELLE d'un run : suite des agents qui ont repondu."""
    return tuple(getattr(m, "name", None) or "?" for m in messages)


def canonical(sig: tuple, ordered: bool) -> tuple:
    """Forme comparable d'une signature.

    `ordered=True` pour les modes ou l'ORDRE est une propriete du mode
    (sequentiel = chaine declaree, group chat = tour de table). `ordered=False`
    pour les modes ou l'ordre est libre par construction : en concurrent les
    agents tournent en parallele, en magentic c'est le manager qui choisit qui
    parle -- exiger une sequence y serait un faux negatif (mesure : l'ordre
    concurrent a varie entre les deux runs, l'ensemble non).
    """
    return sig if ordered else tuple(sorted(sig))


# --------------------------------------------------------------------------- modes


def build_agents(kernel: Kernel, arguments: KernelArguments) -> dict:
    """Trois roles reutilises par tous les modes (meme charge, orchestration differente)."""
    # `description` est OBLIGATOIRE des qu'un manager choisit l'orateur
    # (group chat, magentic) : sans elle, `GroupChatOrchestration` leve
    # "All members must have a description."
    return {
        "redacteur": ChatCompletionAgent(
            kernel=kernel, name="redacteur", arguments=arguments,
            description="Redige une definition courte.",
            instructions=(
                "Tu es le redacteur. Tu produis UNE phrase courte en francais qui definit la "
                "distillation d'un modele. Pas de preambule, pas de liste."
            ),
        ),
        "critique": ChatCompletionAgent(
            kernel=kernel, name="critique", arguments=arguments,
            description="Releve un defaut precis dans ce qui precede.",
            instructions=(
                "Tu es le critique. Tu releves UN defaut precis de la phrase precedente, en une "
                "phrase courte. Pas de preambule."
            ),
        ),
        "arbitre": ChatCompletionAgent(
            kernel=kernel, name="arbitre", arguments=arguments,
            description="Tranche entre les positions.",
            instructions=(
                "Tu es l'arbitre. Tu tranches en UNE phrase courte en francais, sans reprendre "
                "les arguments."
            ),
        ),
    }


async def run_sequential(kernel: Kernel, agents: dict, task: str):
    """Chaine : redacteur -> critique -> arbitre. Chaque agent voit la sortie du precedent."""
    members = [agents["redacteur"], agents["critique"], agents["arbitre"]]
    final, messages = await invoke(
        lambda cb: SequentialOrchestration(members=members, agent_response_callback=cb), task
    )
    return signature(messages), (final.content or "").strip()[:80]


async def run_concurrent(kernel: Kernel, agents: dict, task: str):
    """Les trois agents traitent la MEME tache en parallele, sans se voir."""
    members = [agents["redacteur"], agents["critique"], agents["arbitre"]]
    final, messages = await invoke(
        lambda cb: ConcurrentOrchestration(members=members, agent_response_callback=cb), task
    )
    return signature(messages), " | ".join((m.content or "").strip()[:40] for m in messages)


async def run_group_chat(kernel: Kernel, agents: dict, task: str):
    """Tour de table a nombre de tours borne : le manager choisit qui parle."""
    members = [agents["redacteur"], agents["critique"]]
    manager = RoundRobinGroupChatManager(max_rounds=GROUP_CHAT_ROUNDS)
    final, messages = await invoke(
        lambda cb: GroupChatOrchestration(members=members, manager=manager, agent_response_callback=cb),
        task,
    )
    return signature(messages), (final.content or "").strip()[:80]


async def run_magentic(kernel: Kernel, agents: dict, task: str, service, settings):
    """Manager Magentic : planifie puis delegue aux membres jusqu'a la reponse finale."""
    members = [agents["redacteur"], agents["critique"]]
    # Le manager Magentic demande au service un `response_format=ProgressLedger`
    # (JSON structure) : il lui faut son PROPRE budget de tokens. Avec les 160
    # tokens des agents, le JSON est tronque et `ProgressLedger.model_validate_json`
    # leve "Invalid JSON: EOF while parsing a value" -- l'echec ne vient pas du
    # modele mais de la taille allouee a la reponse du manager.
    manager_settings = OpenAIChatPromptExecutionSettings(
        temperature=0.0, max_completion_tokens=1500
    )
    # Le manager est NON BORNE par defaut (`max_round_count=None`) et `max_stall_count`
    # vaut 3 : sur une tache a deux roles il boucle (mesure du 1er run non borne :
    # 8 tours, `critique` repete 5 fois, budget LLM epuise avant la fin du 2e run).
    # On borne explicitement -- un pilote pedagogique doit montrer le mode, pas
    # laisser un manager tourner jusqu'a epuisement du budget.
    manager = StandardMagenticManager(
        chat_completion_service=service,
        prompt_execution_settings=manager_settings,
        max_round_count=MAGENTIC_ROUNDS,
        max_stall_count=MAGENTIC_STALLS,
        max_reset_count=MAGENTIC_RESETS,
    )
    final, messages = await invoke(
        lambda cb: MagenticOrchestration(members=members, manager=manager, agent_response_callback=cb),
        task,
    )
    return signature(messages), (getattr(final, "content", "") or "").strip()[:80]


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
    service = make_service(model, api_key)
    kernel.add_service(service)
    settings = OpenAIChatPromptExecutionSettings(temperature=0.0, max_completion_tokens=160)
    arguments = KernelArguments(settings=settings)
    agents = build_agents(kernel, arguments)

    task = "Definir la distillation d'un modele de langage en une phrase."
    # Magentic a besoin d'une tache qui exige PLUSIEURS roles : confiee a une tache
    # triviale, le manager delegue une seule fois puis repond (mesure du 1er run :
    # 1 tour, un seul agent) -- ce qui ne demontre pas la planification.
    task_magentic = (
        "Etablir la definition de la distillation d'un modele de langage. "
        "Le redacteur propose une phrase, le critique en releve un defaut precis, "
        "et la reponse finale donne la phrase corrigee."
    )
    results: dict[str, dict] = {}

    plan = [
        ("sequentiel", lambda: run_sequential(kernel, agents, task), 3, 3, True),
        ("concurrent", lambda: run_concurrent(kernel, agents, task), 3, 3, False),
        ("group_chat", lambda: run_group_chat(kernel, agents, task), GROUP_CHAT_ROUNDS, GROUP_CHAT_ROUNDS, True),
        # magentic : borne BASSE `>= 2` (le mode doit deleguer, pas repondre seul) et
        # borne HAUTE `<= MAGENTIC_MAX_TURNS` (le manager borne ne doit pas s'emballer).
        ("magentic", lambda: run_magentic(kernel, agents, task_magentic, service, settings), 2, MAGENTIC_MAX_TURNS, False),
    ]

    for mode, runner, min_turns, max_turns, ordered in plan:
        print(f"\n===== MODE {mode} =====")
        runs = []
        for index in (1, 2):
            sig, preview = await runner()
            runs.append(canonical(sig, ordered))
            print(f"  run {index}: tours={len(sig)} agents={list(sig)}")
            print(f"    apercu: {preview[:70]}")
        stable = runs[0] == runs[1]
        turns = len(runs[0])
        covered = min_turns <= turns <= max_turns
        results[mode] = {
            "signatures": runs, "stable": stable, "turns": turns,
            "covered": covered, "min": min_turns, "max": max_turns,
        }
        print(
            f"  STRUCTURE STABLE: {'OK' if stable else 'NON'}"
            f" | TOURS dans [{min_turns}, {max_turns}]: {'OK' if covered else 'NON'}"
        )

    # chaque mode doit avoir fait parler AU MOINS deux agents distincts : un mode qui
    # ne sollicite qu'un agent ne demontre pas l'orchestration
    distinct_ok = all(len(set(s)) >= 2 for r in results.values() for s in r["signatures"])
    all_stable = all(r["stable"] for r in results.values())
    all_covered = all(r["covered"] for r in results.values())
    verdict = "OK" if (all_stable and all_covered and distinct_ok) else "FAIL"

    print("\n===== SYNTHESE =====")
    for mode, r in results.items():
        print(
            f"  {mode:12s} tours={r['turns']} (attendu [{r['min']},{r['max']}])"
            f" stable={r['stable']} couverture={r['covered']}"
        )
    print(f"MULTI-AGENTS PAR MODE: {'OK' if distinct_ok else 'NON'}")
    print(f"ROUTING DETERMINISM: {verdict}")
    print(f"LLM CALLS: {llm_calls}/{BUDGET}")
    print(f"PILOT OK sk={semantic_kernel.__version__} modes=4")
    return 0 if verdict == "OK" else 1


if __name__ == "__main__":
    try:
        sys.exit(asyncio.run(main()))
    except SystemExit:
        raise
    except BaseException as exc:  # erreur exacte, jamais la cle
        print(f"ERREUR FATALE {type(exc).__name__}: {str(exc)[:300]}")
        sys.exit(2)
