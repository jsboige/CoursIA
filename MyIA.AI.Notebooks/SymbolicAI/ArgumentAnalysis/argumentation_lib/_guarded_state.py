# _guarded_state.py — garde de consignation des verdicts (#22981)
# + garde de reponse sur tache inexistante (#23726)
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
#
# Extension #23726 (mesure sur le verbatim amont, non modifiable) : l'etat
# vendored `_shared_state.py` traite une reponse sur tache inexistante en
# silence — `mark_task_as_answered` avertit puis `return` (reponse PERDUE,
# et le plugin verbatim renvoyait quand meme « OK: Tache marquee »),
# `add_answer` avertit puis ecrit SOUS LA TACHE FANTOME (pollution). Les
# deux gardes ci-dessous refusent AVANT de deleguer au verbatim : l'agent
# recoit un FUNC_ERROR diagnostiquable (identifiants connus listes), la
# reponse n'est ni perdue sans trace ni ecrite sous une tache fantome.
#
# Extension #28671 (paramètre réservé) : Semantic Kernel injecte lui-même la
# valeur de quatre noms de paramètres — `kernel`, `service`,
# `execution_settings` et `arguments` — et une fonction kernel qui déclare
# l'un d'eux ne reçoit jamais la valeur de la clé. Le verbatim amont nomme
# `arguments` le paramètre de `add_identified_arguments` : l'outil de masse
# enregistrait le snapshot d'état, puis la liste convertie en chaîne, et
# répondait quand même « OK: 2 arguments ajoutés. » La surcharge garde le nom
# de l'outil et donne au paramètre un nom qui n'est pas réservé.

from __future__ import annotations

import logging
from typing import List, Optional

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
    """`StateManagerPlugin` qui n'accepte que des verdicts de moteur.

    Elle corrige aussi le paramètre réservé de l'outil de masse
    `add_identified_arguments` (#28671) : même nom d'outil, paramètre
    `descriptions`.
    """

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

    # -- garde #23726 : reponse sur tache inexistante ---------------------
    def _task_refusal(self, task_id: str, author: str = "") -> str:
        """Refus diagnostiquable : la tache n'existe pas, on liste les siennes."""
        who = f" de '{author}'" if author else ""
        return (
            f"FUNC_ERROR: Tâche '{task_id}' inexistante — réponse{who} refusée. "
            f"Tâches définies : {sorted(self._state.analysis_tasks)}. "
            "Utilisez l'identifiant EXACT fourni dans vos instructions."
        )

    @kernel_function(
        description=(
            "Marque une tâche comme répondue dans l'état. L'identifiant doit "
            "être une tâche EXISTANTE (celle fournie dans vos instructions) : "
            "une tâche inexistante est refusée, la réponse n'est pas perdue en "
            "silence."
        ),
        name="mark_task_as_answered",
    )
    def mark_task_as_answered(self, task_id: str, answer: str) -> str:
        """Consigne une reponse — la tache doit exister (#23726).

        Le verbatim amont (`_shared_state.py`) avertit puis jette la reponse
        en silence, et le plugin verbatim renvoie « OK » quand meme : l'agent
        croyait sa reponse enregistree. La garde refuse AVANT de deleguer.
        """
        if task_id not in self._state.analysis_tasks:
            logger.warning(
                "Reponse refusee : tache inexistante (task_id=%r, connues=%s)",
                task_id,
                sorted(self._state.analysis_tasks),
            )
            return self._task_refusal(task_id)
        return super().mark_task_as_answered(task_id, answer)

    @kernel_function(
        description=(
            "Ajoute une réponse d'agent à une tâche d'analyse spécifique dans "
            "l'état. L'identifiant doit être une tâche EXISTANTE : une tâche "
            "inexistante est refusée (aucune écriture sous une tâche fantôme)."
        ),
        name="add_answer",
    )
    def add_answer(
        self, task_id: str, author_agent: str, answer_text: str, source_ids: List[str]
    ) -> str:
        """Ajoute une reponse — la tache doit exister (#23726).

        Le verbatim amont avertit puis ecrit quand meme la reponse sous la
        tache fantomme. La garde refuse AVANT de deleguer : pas d'ecriture.
        """
        if task_id not in self._state.analysis_tasks:
            logger.warning(
                "Reponse refusee : tache inexistante (task_id=%r, auteur=%r, "
                "connues=%s)",
                task_id,
                author_agent,
                sorted(self._state.analysis_tasks),
            )
            return self._task_refusal(task_id, author_agent)
        return super().add_answer(task_id, author_agent, answer_text, source_ids)

    # -- garde #28671 : paramètre réservé de Semantic Kernel ----------------
    @kernel_function(
        description=(
            "Ajoute une liste d'arguments identifiés à l'état. `descriptions` "
            "est la liste : chaque élément est la formulation d'un argument, "
            "telle que reprise du texte analysé (sous-chaîne ou paraphrase "
            "courte du texte) — jamais un nom de champ de l'état, jamais un "
            "objet, jamais une liste."
        ),
        name="add_identified_arguments",
    )
    def add_identified_arguments(self, descriptions: List[str]) -> str:
        """Ajoute une liste d'arguments — le paramètre ne s'appelle pas `arguments`.

        Dans Semantic Kernel (`kernel_function_from_method.py`,
        `gather_function_parameters`), un paramètre nommé `arguments` reçoit
        l'objet `KernelArguments` entier, jamais la valeur de la clé. Le
        verbatim amont nomme ainsi le sien : l'outil de masse enregistrait le
        snapshot d'état, puis la liste convertie en chaîne. Même nom d'outil,
        autre nom de paramètre.

        La réponse compte les arguments réellement écrits : une formulation
        refusée à l'écriture (une clé d'état, #18395) n'y figure pas.
        """
        self._logger.info(
            "Appel add_identified_arguments (state id: %s) avec %s formulations...",
            id(self._state),
            len(descriptions),
        )
        try:
            avant = len(self._state.identified_arguments)
            self._state.add_identified_arguments(descriptions)
            ecrits = len(self._state.identified_arguments) - avant
        except Exception as e:
            self._logger.error(
                f"Erreur lors de l'ajout de la liste d'arguments: {e}", exc_info=True
            )
            return f"FUNC_ERROR: Erreur ajout liste d'arguments: {e}"
        if ecrits == 0:
            return (
                "FUNC_ERROR: aucune formulation enregistrée. `descriptions` doit "
                "être une liste de chaînes, une par argument, reprises du texte "
                "analysé."
            )
        pluriel = "s" if ecrits > 1 else ""
        return f"OK: {ecrits} argument{pluriel} ajouté{pluriel}."
