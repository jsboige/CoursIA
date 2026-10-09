"""Pilote T5 (issue #14499) : Microsoft Agent Framework -- le graphe typé.

Complement des pilotes SK (T2 handoff, T3 process, T4 les quatre autres modes).
MAF n'est pas un framework « objets d'orchestration » : c'est un **graphe typé**
(`WorkflowBuilder` + `Executor` + arêtes). Le depot l'utilise DEJA dans le
harnais du prover Lean (`SymbolicAI/Lean/agent_tests/prover/workflow.py`) --
l'organe natif existe, ce pilote mesure son idiome reel plutot que d'en inventer
un.

Les trois roles sont les memes que T4 (redacteur, critique, arbitre), la tache
aussi, ce qui rend les deux couches comparables : ce qui change n'est pas le
travail, c'est **qui decide de l'orateur suivant**. En SK/Magentic le manager est
un LLM qui emet un `ProgressLedger` ; ici la decision est une **lambda Python**
posee dans le graphe.

Determinisme exige : a temperature 0, on n'asserte PAS la prose mais la STRUCTURE.
Le graphe etant un chemin, l'ORDRE **et** le nombre de tours sont fixes -- meme
doctrine que sequentiel/group chat en T4, pas celle de concurrent/Magentic
(ensemble fixe, ordre libre). Chaque run est execute DEUX fois.

Budget dur : 40 appels LLM au total (sonde incluse), garde-fou anti-emballement.
"""

import asyncio
import os
import sys
from dataclasses import dataclass, field
from pathlib import Path

from agent_framework import (
    Agent,
    Case,
    Default,
    Executor,
    WorkflowBuilder,
    WorkflowContext,
    handler,
)
from agent_framework_openai import OpenAIChatCompletionClient
from openai import AsyncOpenAI

MASTER_ENV = Path(__file__).resolve().parents[4] / ".secrets" / "master.env"
OPENAI_BASE = "https://api.openai.com/v1"
BUDGET = 40  # garde-fou anti-emballement, pas une cible
MODEL_ID = "gpt-4o-mini"

# Plafond de boucle du graphe. Le controle est a DEUX niveaux, et c'est le
# second qui garantit : la lambda de la `Case` teste `revision_count`, et
# `max_iterations` du builder borne le graphe quoi qu'il arrive en aval.
MAX_REVISIONS = 2
MAX_ITERATIONS = 12

llm_calls = 0


def maf_version() -> str:
    """Version du coeur MAF, pas celle du metapaquet.

    `agent_framework.__version__` rend la version du **metapaquet** (1.2.2 sur
    cet env) alors que le coeur charge est `agent-framework-core` (1.9.0) : le
    premier est un simple agregateur de dependances, ses deux numeros divergent.
    C'est le second qui decrit ce qui s'execute.
    """
    from importlib.metadata import PackageNotFoundError, version

    for name in ("agent-framework-core", "agent-framework"):
        try:
            return f"{version(name)} ({name})"
        except PackageNotFoundError:
            continue
    return "?"


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


@dataclass
class Msg:
    """Message qui circule dans le graphe.

    `turns` porte la trace des executors traverses : c'est la signature
    structurelle du run, donc ce que les assertions comparent.
    """

    content: str = ""
    needs_revision: bool = False
    revision_count: int = 0
    turns: list = field(default_factory=list)


def first_line_flag(text: str, label: str) -> bool:
    """Lit un drapeau `LABEL: oui|non` en tete de reponse.

    La decision de routage reste deterministe : elle lit un marqueur que
    l'agent doit produire, elle n'interprete pas la prose.
    """
    for line in text.splitlines():
        head = line.strip().upper()
        if head.startswith(label.upper() + ":"):
            value = head.split(":", 1)[1].strip()
            return value.startswith("OUI") or value.startswith("YES")
    return False


class BaseExecutor(Executor):
    """Executor qui delegue a un `Agent` MAF et trace son passage."""

    role = "?"

    def __init__(self, agent: Agent, **kwargs):
        super().__init__(id=self.role, **kwargs)
        self._agent = agent

    async def ask(self, prompt: str) -> str:
        result = await self._agent.run(prompt)
        return (getattr(result, "text", None) or str(result)).strip()


class Redacteur(BaseExecutor):
    role = "redacteur"

    @handler
    async def handle(self, msg: Msg, ctx: WorkflowContext[Msg]) -> None:
        feedback = ""
        if msg.content:
            feedback = f"\nCorrige selon cette critique : {msg.content}"
        text = await self.ask(
            "Redige en une phrase la definition de la distillation d'un modele "
            "de langage." + feedback
        )
        await ctx.send_message(
            Msg(
                content=text,
                revision_count=msg.revision_count + 1,
                turns=msg.turns + [self.role],
            )
        )


class Critique(BaseExecutor):
    role = "critique"

    @handler
    async def handle(self, msg: Msg, ctx: WorkflowContext[Msg]) -> None:
        text = await self.ask(
            "Critique cette definition en un defaut precis.\n"
            f"Definition : {msg.content}\n"
            "Reponds en deux lignes exactement :\n"
            "REVISION: oui si la definition doit etre corrigee, non sinon\n"
            "DEFAUT: le defaut en une phrase"
        )
        await ctx.send_message(
            Msg(
                content=text,
                needs_revision=first_line_flag(text, "REVISION"),
                revision_count=msg.revision_count,
                turns=msg.turns + [self.role],
            )
        )


class Arbitre(BaseExecutor):
    role = "arbitre"

    @handler
    async def handle(self, msg: Msg, ctx: WorkflowContext[Msg]) -> None:
        text = await self.ask(
            "Donne la definition finale corrigee en une phrase, sans preambule.\n"
            f"Critique recue : {msg.content}"
        )
        await ctx.yield_output(
            Msg(
                content=text,
                revision_count=msg.revision_count,
                turns=msg.turns + [self.role],
            )
        )


def build_agents(client: CountingClient) -> dict:
    """Trois agents MAF, memes roles que le pilote SK de T4."""
    return {
        "redacteur": Agent(
            client,
            name="redacteur",
            instructions=(
                "Tu rediges des definitions techniques courtes et exactes. "
                "Une seule phrase, sans preambule."
            ),
        ),
        "critique": Agent(
            client,
            name="critique",
            instructions=(
                "Tu releves un defaut precis et verifiable dans une definition. "
                "Tu respectes le format demande a la lettre."
            ),
        ),
        "arbitre": Agent(
            client,
            name="arbitre",
            instructions=(
                "Tu tranches et rends la version finale. Une seule phrase, "
                "sans preambule ni commentaire."
            ),
        ),
    }


def build_workflow(agents: dict):
    """Construit le graphe typé : redacteur -> critique -> (boucle|arbitre).

    La `Case` est le point qui distingue MAF de SK : la branche est decidee par
    une **lambda sur le message**, pas par un manager LLM.
    """
    redacteur = Redacteur(agents["redacteur"])
    critique = Critique(agents["critique"])
    arbitre = Arbitre(agents["arbitre"])

    builder = WorkflowBuilder(
        start_executor=redacteur,
        max_iterations=MAX_ITERATIONS,
    )
    builder.add_edge(redacteur, critique)
    builder.add_switch_case_edge_group(
        critique,
        [
            Case(
                condition=lambda m: m.needs_revision and m.revision_count < MAX_REVISIONS,
                target=redacteur,
            ),
            Default(target=arbitre),
        ],
    )
    return builder.build()


async def run_once(client: CountingClient, agents: dict) -> Msg:
    workflow = build_workflow(agents)
    result = await workflow.run(Msg())
    outputs = result.get_outputs()
    if not outputs:
        raise RuntimeError("Le graphe n'a produit aucune sortie")
    return outputs[-1]


def signature(msg: Msg) -> tuple:
    """Signature STRUCTURELLE d'un run : suite des executors traverses."""
    return tuple(msg.turns)


def path(sig: tuple) -> tuple:
    """Ordre des noeuds du chemin, doublons replies (premiere occurrence).

    Ce qui est deterministe **par construction** dans un graphe MAF, c'est
    l'ordre des noeuds traverses -- redacteur, critique, arbitre -- pas le
    **nombre** de tours de boucle, qui depend du drapeau `REVISION` rendu par le
    LLM. La boucle alterne `redacteur, critique` : ses repetitions ne sont donc
    PAS consecutives, et replier les seuls voisins identiques ne replierait rien
    (mesure : `shape` rendait la sequence intacte et faisait echouer le pilote
    sur un graphe correct). On replie par identite de noeud, pas par voisinage.
    """
    out = []
    for role in sig:
        if role not in out:
            out.append(role)
    return tuple(out)


def alternates(sig: tuple) -> bool:
    """Le chemin suit-il l'alternance redacteur/critique puis un arbitre final ?

    Verifie la forme reelle du graphe : aucune autre suite n'est atteignable,
    `arbitre` n'apparait qu'une fois et seulement en derniere position.
    """
    if not sig or sig[-1] != "arbitre":
        return False
    if sig.count("arbitre") != 1:
        return False
    body = sig[:-1]
    if not body:
        return False
    return all(role == ("redacteur" if i % 2 == 0 else "critique") for i, role in enumerate(body))


async def main() -> int:
    api_key = load_api_key()
    client = CountingClient(model=MODEL_ID, api_key=api_key, base_url=OPENAI_BASE)
    agents = build_agents(client)

    print("MAF", maf_version())

    runs = []
    for i in (1, 2):
        msg = await run_once(client, agents)
        runs.append(msg)
        print(f"MAF run{i}: tours={len(msg.turns)} agents={list(msg.turns)}")

    sigs = [signature(m) for m in runs]
    paths = [path(s) for s in sigs]
    stable = paths[0] == paths[1]
    print(
        f"FORME STABLE: {'OK' if stable else 'FAIL (' + str(paths[0]) + ' != ' + str(paths[1]) + ')'}"
    )

    roles = set(sigs[0])
    multi = roles == {"redacteur", "critique", "arbitre"}
    print(f"MULTI-AGENTS: {'OK' if multi else 'FAIL ' + str(sorted(roles))}")

    # Le graphe est un chemin : l'ordre est fixe par les aretes.
    ordered = paths[0] == ("redacteur", "critique", "arbitre") and all(alternates(s) for s in sigs)
    print(f"ORDRE FIXE: {'OK' if ordered else 'FAIL ' + str(sigs)}")

    bounded = all(s.count("critique") <= MAX_REVISIONS + 1 and len(s) <= MAX_ITERATIONS for s in sigs)
    print(f"BOUCLE BORNEE: {'OK' if bounded else 'FAIL ' + str([len(s) for s in sigs])}")

    print(f"LLM CALLS: {llm_calls}/{BUDGET}")

    ok = stable and multi and ordered and bounded
    print(f"PILOT {'OK' if ok else 'FAIL'} maf workflow roles=3")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(asyncio.run(main()))
