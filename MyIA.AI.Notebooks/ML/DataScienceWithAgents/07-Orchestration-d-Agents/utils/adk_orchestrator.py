"""Orchestration multi-agents au-dessus de Google ADK (contrat C4, #14058).

Le contrat EPITA de designation : le runtime designe le prochain agent
selon une strategie explicite. ADK 2.8 embarque un ordonnanceur dynamique
(workflow), mais aucune surface du depot n'exposait de strategie de
selection : l'ordre multi-etapes etait code par l'appelant, etape par
etape. Ce module porte le contrat AU-DESSUS d'ADK : un ``AdkOrchestrator``
accepte N specialistes et execute une chaine selon un ``plan`` declaratif
pose AVANT le premier appel LLM.

Jamais une restauration du moteur SK (#14058) : l'assemblage n'utilise
que les primitives publiques d'ADK (un ``Runner`` par etape, un
``InMemorySessionService`` partage, une session unique par chaine).
"""

from __future__ import annotations

import asyncio
from collections.abc import Mapping, Sequence
from uuid import uuid4

from google.adk.agents import BaseAgent
from google.adk.runners import Runner
from google.adk.sessions import InMemorySessionService
from google.genai import types

from utils.adk_runtime import (
    APP_NAME,
    AdkRunResult,
    AdkRuntimeUnavailable,
    AdkUsage,
    _event_usage,
    _part_text,
)


class AdkOrchestrator:
    """Execute une chaine de specialistes selon une strategie EXPLICITE.

    Distinction C4/C5 : la designation (C4) decide QUI PARLE ENSUITE
    AVANT le premier appel LLM -- le ``plan`` est une donnee posee par
    l'appelant, jamais un choix du modele ; le handoff (C5, ``sub_agents``
    + ``transfer_to_agent``) est une decision DE L'AGENT au milieu d'un
    tour. Les deux mecaniques cohabitent sans se recouvrir.

    Les specialistes partagent UNE session ADK : chacun voit l'historique
    complet de la chaine (memoire commune intra-chaine), et deux
    orchestrateurs restent isoles l'un de l'autre (contrat C1 --
    l'isolement reste scope par session).
    """

    def __init__(
        self,
        agents: Sequence[BaseAgent] | Mapping[str, BaseAgent],
        *,
        plan: Sequence[str] | None = None,
        app_name: str = APP_NAME,
        user_id: str = "track2-user",
        session_id: str | None = None,
    ) -> None:
        if isinstance(agents, Mapping):
            self._agents: dict[str, BaseAgent] = dict(agents)
        else:
            self._agents = {agent.name: agent for agent in agents}
        if not self._agents:
            raise ValueError("l'orchestrateur exige au moins un specialiste")
        if plan is None:
            plan = tuple(self._agents)
        unknown = [name for name in plan if name not in self._agents]
        if unknown:
            raise ValueError(
                f"le plan designe des specialistes inconnus : {unknown} "
                f"(connus : {sorted(self._agents)})"
            )
        # La strategie sequentielle DECLAREE : qui parle, dans quel ordre,
        # decide avant toute execution -- l'observable de la designation.
        self.plan = tuple(plan)
        self.app_name = app_name
        self.user_id = user_id
        self.session_id = session_id or f"chaine-{uuid4().hex}"
        self.session_service = InMemorySessionService()
        self._started = False

    async def start(self) -> None:
        """Cree la session unique de la chaine (idempotent)."""
        if self._started:
            return
        await self.session_service.create_session(
            app_name=self.app_name,
            user_id=self.user_id,
            session_id=self.session_id,
        )
        self._started = True

    async def run_chain(
        self,
        prompt: str,
        *,
        timeout_seconds: float = 120.0,
    ) -> AdkRunResult:
        """Joue la chaine complete et retourne les preuves cumulees.

        La premiere etape recoit le prompt utilisateur ; chaque etape
        suivante s'enchaine sur l'historique de la session partagee,
        SANS nouveau message -- le specialiste designe prend le relais
        sur ce que ses predecesseurs ont produit.
        """
        if not self._started:
            await self.start()

        response_text = ""
        tool_calls: list[str] = []
        tool_responses: list[str] = []
        usage_turns: list[AdkUsage] = []
        agent_hands: list[str] = []
        event_errors: list[str] = []
        event_count = 0

        for step, name in enumerate(self.plan):
            message = (
                types.Content(role="user", parts=[types.Part(text=prompt)])
                if step == 0
                else None
            )
            step_final = ""

            async def consume_events(agent: BaseAgent, new_message) -> None:
                nonlocal event_count, step_final
                runner = Runner(
                    agent=agent,
                    app_name=self.app_name,
                    session_service=self.session_service,
                )
                try:
                    async for event in runner.run_async(
                        user_id=self.user_id,
                        session_id=self.session_id,
                        new_message=new_message,
                    ):
                        event_count += 1
                        author = getattr(event, "author", None)
                        if author and (not agent_hands or agent_hands[-1] != author):
                            agent_hands.append(author)
                        tool_calls.extend(
                            call.name
                            for call in event.get_function_calls()
                            if call.name
                        )
                        tool_responses.extend(
                            response.name
                            for response in event.get_function_responses()
                            if response.name
                        )
                        usage = _event_usage(event)
                        if usage is not None:
                            usage_turns.append(usage)
                        error_code = getattr(event, "error_code", None)
                        error_message = getattr(event, "error_message", None)
                        if error_code or error_message:
                            event_errors.append(
                                ": ".join(
                                    detail
                                    for detail in (error_code, error_message)
                                    if detail
                                )
                            )
                        if event.is_final_response():
                            step_final = _part_text(event.content)
                finally:
                    await runner.close()

            try:
                await asyncio.wait_for(
                    consume_events(self._agents[name], message),
                    timeout=timeout_seconds,
                )
            except asyncio.TimeoutError as exc:
                raise AdkRuntimeUnavailable(
                    f"RECOVERABLE-LOCAL: etape {name} de la chaine expiree "
                    f"apres {timeout_seconds:g} s"
                ) from exc
            except Exception as exc:
                detail = str(exc).strip()
                suffix = f": {detail}" if detail else ""
                raise AdkRuntimeUnavailable(
                    f"RECOVERABLE-LOCAL: echec du runtime ADK reel a l'etape "
                    f"{name} ({type(exc).__name__}){suffix}"
                ) from exc

            if not step_final:
                detail = f" ({'; '.join(event_errors)})" if event_errors else ""
                raise AdkRuntimeUnavailable(
                    f"RECOVERABLE-LOCAL: l'etape {name} n'a produit aucune "
                    f"reponse LLM finale{detail}"
                )
            response_text = step_final

        return AdkRunResult(
            response_text=response_text,
            event_count=event_count,
            tool_calls=tuple(tool_calls),
            tool_responses=tuple(tool_responses),
            usage_turns=tuple(usage_turns),
            agent_hands=tuple(agent_hands),
        )

    async def history(self) -> list[types.Event]:
        """Les evenements persistes de la chaine, preuve mecanique du partage."""
        session = await self.session_service.get_session(
            app_name=self.app_name,
            user_id=self.user_id,
            session_id=self.session_id,
        )
        return list(session.events) if session else []

    async def __aenter__(self) -> "AdkOrchestrator":
        await self.start()
        return self

    async def __aexit__(self, *exc_info) -> None:
        return None
