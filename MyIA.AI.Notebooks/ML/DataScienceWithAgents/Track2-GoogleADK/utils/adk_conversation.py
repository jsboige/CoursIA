"""Conversation multi-tours persistante au-dessus de Google ADK (contrat C1b, #14058).

Le contrat EPITA de persistance d'etat : l'historique d'un tour doit atteindre
le tour suivant, au sein d'une meme conversation. ADK porte nativement cette
mecanique -- la session est concue pour durer -- mais ``run_agent_turn``
(adk_runtime) instancie un service frais a chaque appel, ce qui annule la
continuite. Ce module est le portage du contrat AU-DESSUS d'ADK : un seul
``InMemorySessionService`` et un seul ``session_id`` partages par tous les
tours d'une conversation. Aucune logique propre : uniquement l'assemblage
durable des primitives publiques d'ADK (Runner, SessionService, session).

Jamais une restauration du moteur SK (#14058) : ADK reste le runtime.
"""

from __future__ import annotations

import asyncio
from uuid import uuid4

from google.adk.agents import BaseAgent
from google.adk.runners import Runner
from google.adk.sessions import InMemorySessionService
from google.genai import types

from utils.adk_runtime import APP_NAME, AdkRunResult, AdkRuntimeUnavailable, _part_text


class ConversationRunner:
    """Execute plusieurs tours d'un agent dans la MEME session ADK.

    La conversation detient un ``InMemorySessionService`` et un ``session_id``
    uniques : chaque tour herite de l'historique des tours precedents, ce qui
    porte le contrat C1b (persistance d'etat entre tours). Le cloisonnement
    reste celui du contrat C1 : deux ``ConversationRunner`` sont deux sessions
    distinctes, isolees l'une de l'autre.
    """

    def __init__(
        self,
        agent: BaseAgent,
        *,
        app_name: str = APP_NAME,
        user_id: str = "track2-user",
        session_id: str | None = None,
    ) -> None:
        self.agent = agent
        self.app_name = app_name
        self.user_id = user_id
        self.session_id = session_id or f"conversation-{uuid4().hex}"
        self.session_service = InMemorySessionService()
        self._runner = Runner(
            agent=agent,
            app_name=app_name,
            session_service=self.session_service,
        )
        self._started = False

    async def start(self) -> None:
        """Cree la session unique de la conversation (idempotent)."""
        if self._started:
            return
        await self.session_service.create_session(
            app_name=self.app_name,
            user_id=self.user_id,
            session_id=self.session_id,
        )
        self._started = True

    async def turn(
        self,
        prompt: str,
        *,
        timeout_seconds: float = 120.0,
    ) -> AdkRunResult:
        """Joue un tour sur la session persistee et retourne ses preuves."""
        if not self._started:
            await self.start()

        message = types.Content(role="user", parts=[types.Part(text=prompt)])
        response_text = ""
        tool_calls: list[str] = []
        tool_responses: list[str] = []
        event_errors: list[str] = []
        event_count = 0

        async def consume_events() -> None:
            nonlocal event_count, response_text
            async for event in self._runner.run_async(
                user_id=self.user_id,
                session_id=self.session_id,
                new_message=message,
            ):
                event_count += 1
                tool_calls.extend(
                    call.name for call in event.get_function_calls() if call.name
                )
                tool_responses.extend(
                    response.name
                    for response in event.get_function_responses()
                    if response.name
                )
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
                    response_text = _part_text(event.content)

        try:
            await asyncio.wait_for(consume_events(), timeout=timeout_seconds)
        except asyncio.TimeoutError as exc:
            raise AdkRuntimeUnavailable(
                f"RECOVERABLE-LOCAL: tour de conversation expire "
                f"apres {timeout_seconds:g} s"
            ) from exc
        except Exception as exc:
            detail = str(exc).strip()
            suffix = f": {detail}" if detail else ""
            raise AdkRuntimeUnavailable(
                f"RECOVERABLE-LOCAL: echec du runtime ADK reel "
                f"({type(exc).__name__}){suffix}"
            ) from exc

        if not response_text:
            detail = f" ({'; '.join(event_errors)})" if event_errors else ""
            raise AdkRuntimeUnavailable(
                "RECOVERABLE-LOCAL: ADK n'a produit aucune reponse LLM finale"
                + detail
            )

        return AdkRunResult(
            response_text=response_text,
            event_count=event_count,
            tool_calls=tuple(tool_calls),
            tool_responses=tuple(tool_responses),
        )

    async def history(self) -> list[types.Event]:
        """Les evenements persistes de la session, preuve mecanique du contrat.

        Apres N tours, la session contient les messages des N tours : c'est
        cette trace qui atteint le LLM au tour suivant.
        """
        session = await self.session_service.get_session(
            app_name=self.app_name,
            user_id=self.user_id,
            session_id=self.session_id,
        )
        return list(session.events) if session else []

    async def close(self) -> None:
        """Ferme le runner (la conversation est terminee)."""
        await self._runner.close()

    async def __aenter__(self) -> "ConversationRunner":
        await self.start()
        return self

    async def __aexit__(self, *exc_info) -> None:
        await self.close()
