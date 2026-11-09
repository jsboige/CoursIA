# _delegating_selection.py — DelegatingSelectionStrategy vendored into CoursIA
#
# Verbatim copy of `DelegatingSelectionStrategy` from
# jsboigeEpita/2025-Epita-Intelligence-Symbolique
# `argumentation_analysis/core/strategies.py` (L134-L246),
# Copyright (c) 2025 jsboigeEpita, MIT License.
# Source commit: ecfd9b9 (2026-10) — ref pinned by issue #18393.
# Verbatim import rationale: see NOTICE-EPITA at the root of this directory.
#
# Deliberate adaptation perimeter (the class body mirrors the upstream logic
# modulo the items listed below — see also NOTICE-EPITA at the root of this
# directory for the verbatim import contract and PR #20338 review for context):
# 1. `record_unresolved_designation` is absent from the vendored state
#    perimeter (#14026) — an unresolved designation is recorded via
#    `state.log_error` instead, preserving the #1751 contract: a log line
#    is not an effect, the trace entry must live in the state.
# 2. `selection_trace` (list of dicts) added: the notebook journal reads
#    who was designated and who spoke, per turn (#18393 verification).
# 3. `next()` also honours `initial_agent` semantics through the default
#    agent fallback (unchanged upstream behaviour).
# 4. The default agent name is `ProjectManagerAgent` here (L51 / L61) where
#    the upstream `strategies.py:134-246` reads `ProjectManager` — the
#    extended form is what the rest of this vendored library already uses
#    (`_runner.py:40`, `_informal_definitions.py:898-902`) and what the
#    notebook pipeline expects to designate; passing the short form would
#    misroute the orchestrator. Mechanical 1-token rename, surface documented
#    in NOTICE-EPITA `## Volet B etape 4 sub-tranche C186g` (forward
#    reference, applied per PR #20338 review).

from __future__ import annotations

import logging
from typing import TYPE_CHECKING, Any, Dict, List

from pydantic import PrivateAttr

from semantic_kernel.agents.strategies.selection.selection_strategy import (
    SelectionStrategy,
)

from argumentation_lib._shared_state import RhetoricalAnalysisState

if TYPE_CHECKING:
    from semantic_kernel.agents.agent import Agent
    from semantic_kernel.contents.chat_message_content import ChatMessageContent

selection_logger = logging.getLogger("argumentation_lib.selection")


class DelegatingSelectionStrategy(SelectionStrategy):
    """Stratégie de sélection qui priorise la désignation explicite via l'état.

    Le PM écrit la désignation dans l'état partagé (méthode
    ``designate_next_agent``, exposée aux agents par le StateManagerPlugin) ;
    la stratégie honore cette désignation au tour suivant. Sans désignation
    valide, le tour revient à l'agent par défaut (le PM).
    """

    _agents_map: Dict[str, "Agent"] = PrivateAttr()
    _default_agent_name: str = PrivateAttr(default="ProjectManagerAgent")
    _analysis_state: "RhetoricalAnalysisState" = PrivateAttr()
    _selection_trace: List[Dict[str, Any]] = PrivateAttr(default_factory=list)
    _instance_id: int
    _logger: logging.Logger

    def __init__(
        self,
        agents: List["Agent"],
        state: "RhetoricalAnalysisState",
        default_agent_name: str = "ProjectManagerAgent",
    ):
        super().__init__()
        if not isinstance(agents, list):
            raise TypeError("'agents' doit être une liste d'agents.")
        for a in agents:
            if not hasattr(a, "name"):
                raise TypeError(
                    f"Chaque agent doit avoir un attribut 'name'. Agent problématique: {a}"
                )
        if not isinstance(state, RhetoricalAnalysisState) or not hasattr(
            state, "consume_next_agent_designation"
        ):
            raise TypeError(
                "Objet 'state' invalide ou sans consume_next_agent_designation "
                "pour DelegatingSelectionStrategy."
            )

        self._agents_map = {agent.name: agent for agent in agents}
        self._analysis_state = state
        self._default_agent_name = default_agent_name
        self._selection_trace = []

        self._instance_id = id(self)
        self._logger = selection_logger

        if self._default_agent_name not in self._agents_map:
            if not self._agents_map:
                raise ValueError("Liste d'agents vide.")
            first_agent_name = list(self._agents_map.keys())[0]
            self._logger.warning(
                f"[{self._instance_id}] Agent défaut '{self._default_agent_name}' "
                f"non trouvé. Fallback -> '{first_agent_name}'."
            )
            self._default_agent_name = first_agent_name

        self._logger.info(
            f"DelegatingSelectionStrategy instance {self._instance_id} créée "
            f"(agents: {list(self._agents_map.keys())}, "
            f"default: '{self._default_agent_name}', "
            f"state_id={id(self._analysis_state)})."
        )

    @property
    def selection_trace(self) -> List[Dict[str, Any]]:
        """Journal des sélections : désignation consommée -> agent sélectionné."""
        return list(self._selection_trace)

    async def next(
        self, agents: List["Agent"], history: List["ChatMessageContent"]
    ) -> "Agent":
        """Sélectionne le prochain agent à parler."""
        self._logger.debug(f"[{self._instance_id}] Appel next()...")

        designated_agent_name = None
        try:
            designated_agent_name = (
                self._analysis_state.consume_next_agent_designation()
            )
            if designated_agent_name:
                self._logger.info(
                    f"[{self._instance_id}] Désignation explicite: "
                    f"'{designated_agent_name}'."
                )
                designated_agent = self._agents_map.get(designated_agent_name)
                if designated_agent:
                    self._logger.info(
                        f" -> Sélection agent désigné: {designated_agent.name}"
                    )
                    self._selection_trace.append(
                        {
                            "designation": designated_agent_name,
                            "selected": designated_agent.name,
                            "path": "delegating",
                        }
                    )
                    return designated_agent
                else:
                    # #1751 : une ligne de log n'est pas un effet. La trace de
                    # la désignation non résolue vit dans l'état (log_error),
                    # pas seulement dans les logs.
                    self._analysis_state.log_error(
                        "DelegatingSelectionStrategy",
                        f"Désignation non résolue: agent '{designated_agent_name}' "
                        f"absent de {[list(self._agents_map.keys())]}",
                    )
                    self._selection_trace.append(
                        {
                            "designation": designated_agent_name,
                            "selected": None,
                            "path": "unresolved",
                        }
                    )
                    self._logger.error(
                        f"[{self._instance_id}] Agent désigné "
                        f"'{designated_agent_name}' INTROUVABLE! "
                        "Poursuite avec fallback."
                    )
        except Exception as e_state_access:
            self._logger.error(
                f"[{self._instance_id}] Erreur accès état pour désignation: "
                f"{e_state_access}. Poursuite avec fallback."
            )

        default_agent_instance = self._agents_map.get(self._default_agent_name)
        if not default_agent_instance:
            self._logger.error(
                f"[{self._instance_id}] ERREUR: Agent défaut "
                f"'{self._default_agent_name}' introuvable! Retourne premier agent."
            )
            available_agents = list(self._agents_map.values())
            if not available_agents:
                raise RuntimeError("Aucun agent disponible.")
            return available_agents[0]

        if not history:
            self._logger.info(
                f" -> Sélection (fallback): Premier tour -> Agent défaut "
                f"({self._default_agent_name})."
            )
        self._selection_trace.append(
            {
                "designation": designated_agent_name,
                "selected": default_agent_instance.name,
                "path": "default",
            }
        )
        return default_agent_instance

    async def reset(self) -> None:
        """Réinitialise la stratégie."""
        self._logger.info(
            f"[{self._instance_id}] Reset DelegatingSelectionStrategy."
        )
        try:
            consumed = self._analysis_state.consume_next_agent_designation()
            if consumed:
                self._logger.debug(
                    f"   Ancienne désignation '{consumed}' effacée."
                )
        except Exception as e:
            self._logger.warning(
                f"   Erreur accès état pendant reset sélection: {e}"
            )
