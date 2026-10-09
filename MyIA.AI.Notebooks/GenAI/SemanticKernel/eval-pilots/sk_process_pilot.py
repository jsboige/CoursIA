"""Pilote minimal deterministe du Process Framework de Semantic Kernel (issue #14499).

Demonstre la vraie API event-driven (ProcessBuilder + KernelProcessStep + wiring
d'evenements), sans LLM : chaque etape calcule une transformation deterministe.
Chaine : intake -> enrich -> review -> (publish | reject), pilotee par evenements.
"""

import asyncio

from pydantic import BaseModel, Field

from semantic_kernel import Kernel
from semantic_kernel.functions import kernel_function
from semantic_kernel.processes import ProcessBuilder
from semantic_kernel.processes.kernel_process import KernelProcessStep, KernelProcessStepContext
from semantic_kernel.processes.kernel_process.kernel_process_step_state import KernelProcessStepState
from semantic_kernel.processes.local_runtime.local_event import KernelProcessEvent
from semantic_kernel.processes.local_runtime.local_kernel_process import start

TRACE: list[tuple[str, dict]] = []


class IntakeStep(KernelProcessStep):
    """Normalise le texte brut d'entree."""

    @kernel_function(name="intake")
    async def intake(self, context: KernelProcessStepContext, raw: str) -> dict:
        payload = {"text": raw.strip().lower()}
        TRACE.append(("intake", dict(payload)))
        await context.emit_event("EnrichRequested", data=payload)
        return payload


class EnrichStep(KernelProcessStep):
    """Enrichit le texte : compte de mots + etiquette longueur."""

    @kernel_function(name="enrich")
    async def enrich(self, context: KernelProcessStepContext, payload: dict) -> dict:
        n_words = len(payload["text"].split())
        enriched = dict(payload, words=n_words, label="long" if n_words >= 3 else "court")
        TRACE.append(("enrich", dict(enriched)))
        await context.emit_event("ReviewRequested", data=enriched)
        return enriched


class ReviewStep(KernelProcessStep):
    """Regle de seuil deterministe : >= 3 mots approuve, sinon rejette."""

    @kernel_function(name="review")
    async def review(self, context: KernelProcessStepContext, payload: dict) -> dict:
        approved = payload["words"] >= 3
        reviewed = dict(payload, verdict="approved" if approved else "rejected")
        TRACE.append(("review", dict(reviewed)))
        await context.emit_event("Approved" if approved else "Rejected", data=reviewed)
        return reviewed


class PublishState(BaseModel):
    """Etat du terminal de publication."""

    published: list[str] = Field(default_factory=list)


class PublishStep(KernelProcessStep):
    """Terminal "publie" de la chaine Generate -> Review -> Publish."""

    state: PublishState = Field(default_factory=PublishState)  # get_type_hints sur "state"

    @kernel_function(name="publish")
    async def publish(self, context: KernelProcessStepContext, payload: dict) -> str:
        self.state.published.append(payload["text"])
        TRACE.append(("publish", {"text": payload["text"], "verdict": payload["verdict"]}))
        return "published"

    async def activate(self, state: KernelProcessStepState) -> None:
        self.state = state.state


class RejectState(BaseModel):
    """Etat du terminal de rejet."""

    rejected: list[str] = Field(default_factory=list)


class RejectStep(KernelProcessStep):
    """Terminal "rejete" : embranchement evenementiel de la review."""

    state: RejectState = Field(default_factory=RejectState)

    @kernel_function(name="reject")
    async def reject(self, context: KernelProcessStepContext, payload: dict) -> str:
        self.state.rejected.append(payload["text"])
        TRACE.append(("reject", {"text": payload["text"], "verdict": payload["verdict"]}))
        return "rejected"

    async def activate(self, state: KernelProcessStepState) -> None:
        self.state = state.state


def build_process():
    """Construit le graphe : evenement d'entree + ciblage de fonctions par nom."""
    builder = ProcessBuilder(name="pilot_process")
    intake = builder.add_step(IntakeStep)
    enrich = builder.add_step(EnrichStep)
    review = builder.add_step(ReviewStep)
    publish = builder.add_step(PublishStep)
    reject = builder.add_step(RejectStep)
    builder.on_input_event("Start").send_event_to(intake, function_name="intake")
    intake.on_event("EnrichRequested").send_event_to(enrich, function_name="enrich")
    enrich.on_event("ReviewRequested").send_event_to(review, function_name="review")
    review.on_event("Approved").send_event_to(publish, function_name="publish")
    review.on_event("Rejected").send_event_to(reject, function_name="reject")
    return builder.build()


async def run(texts: list[str]) -> tuple[list[tuple[str, dict]], dict[str, list[str]]]:
    """Un run complet : evenement initial + evenements externes subsequents."""
    TRACE.clear()
    kernel = Kernel()
    context = await start(build_process(), kernel, "Start", data=texts[0])
    for extra in texts[1:]:
        # send_event ne fait que mettre en file : start_with_event draine la boucle.
        await context.start_with_event(KernelProcessEvent(id="Start", data=extra))
    final = await context.get_state()
    finals = {
        step.state.name: step.state.state.model_dump()
        for step in final.steps
        if step.state.name in ("PublishStep", "RejectStep")
    }
    await context.dispose()
    return list(TRACE), finals


def main() -> int:
    texts = ["le framework orchestre des etapes evenementielles", "ok"]
    first_trace, first_state = asyncio.run(run(texts))
    for name, payload in first_trace:
        print(f"[step] {name} -> {payload}")
    second_trace, second_state = asyncio.run(run(texts))
    deterministic = first_trace == second_trace and first_state == second_state
    print("DETERMINISM: OK" if deterministic else "DETERMINISM: FAIL")
    if not deterministic:
        return 1
    print(f"final publish state: {first_state['PublishStep']['published']}")
    print(f"final reject state: {first_state['RejectStep']['rejected']}")
    print(f"PILOT OK sk=1.41.3 steps={len(first_trace)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
