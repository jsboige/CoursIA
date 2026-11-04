# _guarded_state.py — garde de consignation des verdicts (#22981)
#
# `StateManagerPlugin` est une copie VERBATIM de l'amont EPITA
# (`argumentation_analysis/core/state_manager_plugin.py`) : on ne le modifie
# pas, on l'etend. Cette sous-classe ne change que `log_query_result` : la
# valeur consignee doit etre un verdict EMIS par le solveur
# (`PLReasonerPlugin.pl_query`), pas une phrase libre.
#
# Mesure (#22981) : deux runs independants du carnet
# `Argumentation-08b-Executor-Python.ipynb` ont consigne 2 questions en
# langage naturel et 0 verdict — le carnet rejette ensuite la phase
# (`QUERIES_NOT_MEANINGFUL`). La garde transforme l'echec silencieux en
# refus explicite, et rend la lettre du contrat (« consigner un VERDICT »)
# executeable.

from __future__ import annotations

import logging
from typing import Optional

from semantic_kernel.functions import kernel_function

from argumentation_lib._pl_verdict import VerdictRegistry, registry_for
from argumentation_lib._state_manager_plugin import StateManagerPlugin

logger = logging.getLogger("Orchestration.GuardedStateManager")

REFUSAL = (
    "FUNC_ERROR: raw_result n'est pas un verdict de moteur. Appelez d'abord "
    "`Reasoner-pl_query` (belief_set_id, query) et consignez sa sortie TELLE "
    "QUELLE (ACCEPTED: ... / REJECTED: ...) ; une question en langage "
    "naturel n'est pas un verdict et n'est pas consignee."
)


class GuardedStateManagerPlugin(StateManagerPlugin):
    """`StateManagerPlugin` qui n'accepte que des verdicts de moteur."""

    def __init__(
        self,
        state,
        registry: Optional[VerdictRegistry] = None,
    ) -> None:
        super().__init__(state)
        self._verdict_registry = (
            registry if registry is not None else registry_for(state)
        )

    @kernel_function(
        description=(
            "Enregistre une requête formelle et son résultat brut dans le log "
            "de l'état. Le résultat brut doit être le verdict renvoyé par "
            "`Reasoner-pl_query` (ACCEPTED: ... / REJECTED: ...) : toute autre "
            "valeur est rejetée."
        ),
        name="log_query_result",
    )
    def log_query_result(self, belief_set_id: str, query: str, raw_result: str) -> str:
        """Consigne une requete — verdict moteur obligatoire."""
        if not self._verdict_registry.is_engine_verdict(
            belief_set_id, query, raw_result
        ):
            logger.warning(
                "Consignation refusee : raw_result sans verdict moteur "
                "(belief_set_id=%s, query=%r)",
                belief_set_id,
                query[:80],
            )
            return REFUSAL
        return super().log_query_result(belief_set_id, query, raw_result)
