# Verbatim copy of `argumentation_analysis/core/state_manager_plugin.py` from
# the 2025-Epita-Intelligence-Symbolique project
# (https://github.com/jsboigeEpita/2025-Epita-Intelligence-Symbolique),
# Copyright (c) 2025 jsboigeEpita, MIT License.
# Source commit: see NOTICE-EPITA at the root of this directory.
#
# Verbatim integrity: file content above this header is byte-for-byte identical
# to the upstream source at the cited commit. No CoursIA modification
# (downstream consumers wrap or extend, never replace the verbatim block).
# core/state_manager_plugin.py
import json
from typing import Dict, List, Any, Optional
import logging
from semantic_kernel.functions import kernel_function

# Importer la classe d'état depuis le même répertoire
from argumentation_lib._shared_state import RhetoricalAnalysisState

# Logger spécifique pour le StateManager
sm_logger = logging.getLogger("Orchestration.StateManager")
if not sm_logger.handlers and not sm_logger.propagate:
    handler = logging.StreamHandler()
    formatter = logging.Formatter(
        "%(asctime)s [%(levelname)s] [%(name)s] %(message)s", datefmt="%H:%M:%S"
    )
    handler.setFormatter(formatter)
    sm_logger.addHandler(handler)
    sm_logger.setLevel(logging.INFO)


class StateManagerPlugin:
    """Plugin Semantic Kernel pour lire et modifier l'état d'analyse partagé."""

    _state: "RhetoricalAnalysisState"  # Référence à l'instance d'état unique
    _logger: logging.Logger

    def __init__(self, state: "RhetoricalAnalysisState"):
        """Initialise le plugin avec une instance d'état."""
        self._state = state
        self._logger = sm_logger
        self._logger.info(
            f"StateManagerPlugin initialisé avec l'instance RhetoricalAnalysisState (id: {id(self._state)})."
        )

    @kernel_function(
        description="Récupère un aperçu (complet ou résumé) de l'état actuel de l'analyse.",
        name="get_current_state_snapshot",
    )
    def get_current_state_snapshot(self, summarize: bool = True) -> str:
        """Retourne l'état actuel sous forme de chaîne JSON."""
        self._logger.info(
            f"Appel get_current_state_snapshot (state id: {id(self._state)}, summarize={summarize})..."
        )
        try:
            snapshot_dict = self._state.get_state_snapshot(summarize=summarize)
            indent = 2 if not summarize else None
            snapshot_json = json.dumps(
                snapshot_dict, indent=indent, ensure_ascii=False, default=str
            )
            self._logger.info(" -> Snapshot de l'état généré avec succès.")
            self._logger.debug(
                f" -> Snapshot (summarize={summarize}): {snapshot_json[:500] + '...' if len(snapshot_json)>500 else snapshot_json}"
            )
            return snapshot_json
        except Exception as e:
            self._logger.error(
                f"Erreur lors de la récupération/sérialisation du snapshot de l'état: {e}",
                exc_info=True,
            )
            return json.dumps(
                {"error": f"Erreur récupération/sérialisation snapshot: {e}"}
            )

    @kernel_function(
        description="Ajoute une nouvelle tâche d'analyse à l'état.",
        name="add_analysis_task",
    )
    def add_analysis_task(self, description: str) -> str:
        """Interface Kernel Function pour ajouter une tâche via l'état."""
        self._logger.info(
            f"Appel add_analysis_task (state id: {id(self._state)}): '{description[:60]}...'"
        )
        try:
            task_id = self._state.add_task(description)
            self._logger.info(f" -> Tâche '{task_id}' ajoutée avec succès via l'état.")
            return task_id
        except Exception as e:
            self._logger.error(
                f"Erreur lors de l'ajout de la tâche '{description[:60]}...': {e}",
                exc_info=True,
            )
            return f"FUNC_ERROR: Erreur ajout tâche: {e}"

    @kernel_function(
        description="Ajoute un argument identifié à l'état.",
        name="add_identified_argument",
    )
    def add_identified_argument(self, description: str) -> str:
        """Interface Kernel Function pour ajouter un argument via l'état."""
        self._logger.info(
            f"Appel add_identified_argument (state id: {id(self._state)}): '{description[:60]}...'"
        )
        try:
            arg_id = self._state.add_argument(description)
            self._logger.info(f" -> Argument '{arg_id}' ajouté avec succès via l'état.")
            return arg_id
        except Exception as e:
            self._logger.error(
                f"Erreur lors de l'ajout de l'argument '{description[:60]}...': {e}",
                exc_info=True,
            )
            return f"FUNC_ERROR: Erreur ajout argument: {e}"

    @kernel_function(
        description="Ajoute une liste d'arguments identifiés à l'état.",
        name="add_identified_arguments",
    )
    def add_identified_arguments(self, arguments: List[str]) -> str:
        """Interface Kernel Function pour ajouter une liste d'arguments via l'état."""
        self._logger.info(
            f"Appel add_identified_arguments (state id: {id(self._state)}) avec {len(arguments)} arguments..."
        )
        try:
            self._state.add_identified_arguments(arguments)
            self._logger.info(
                f" -> {len(arguments)} arguments ajoutés avec succès via l'état."
            )
            return f"OK: {len(arguments)} arguments ajoutés."
        except Exception as e:
            self._logger.error(
                f"Erreur lors de l'ajout de la liste d'arguments: {e}", exc_info=True
            )
            return f"FUNC_ERROR: Erreur ajout liste d'arguments: {e}"

    @kernel_function(
        description="Ajoute une liste de sophismes identifiés à l'état.",
        name="add_identified_fallacies",
    )
    def add_identified_fallacies(self, fallacies: List[Dict[str, str]]) -> str:
        """Interface Kernel Function pour ajouter une liste de sophismes via l'état."""
        self._logger.info(
            f"Appel add_identified_fallacies (state id: {id(self._state)}) avec {len(fallacies)} sophismes..."
        )
        try:
            self._state.add_identified_fallacies(fallacies)
            self._logger.info(
                f" -> {len(fallacies)} sophismes ajoutés avec succès via l'état."
            )
            return f"OK: {len(fallacies)} sophismes ajoutés."
        except Exception as e:
            self._logger.error(
                f"Erreur lors de l'ajout de la liste de sophismes: {e}", exc_info=True
            )
            return f"FUNC_ERROR: Erreur ajout liste de sophismes: {e}"

    @kernel_function(
        description="Marque une tâche comme répondue dans l'état.",
        name="mark_task_as_answered",
    )
    def mark_task_as_answered(self, task_id: str, answer: str) -> str:
        """Interface Kernel Function pour marquer une tâche comme terminée."""
        self._logger.info(
            f"Appel mark_task_as_answered (state id: {id(self._state)}): TaskID='{task_id}'"
        )
        try:
            self._state.mark_task_as_answered(task_id, answer)
            self._logger.info(
                f" -> Tâche '{task_id}' marquée comme répondue avec succès."
            )
            return f"OK: Tâche {task_id} marquée comme répondue."
        except Exception as e:
            self._logger.error(
                f"Erreur lors du marquage de la tâche '{task_id}' comme répondue: {e}",
                exc_info=True,
            )
            return f"FUNC_ERROR: Erreur marquage tâche {task_id}: {e}"

    @kernel_function(
        description="Ajoute un sophisme identifié à l'état.",
        name="add_identified_fallacy",
    )
    def add_identified_fallacy(
        self,
        fallacy_type: str,
        justification: str,
        target_argument_id: Optional[str] = None,
        family: str = "",
    ) -> str:
        """Interface Kernel Function pour ajouter un sophisme via l'état."""
        self._logger.info(
            f"Appel add_identified_fallacy (state id: {id(self._state)}): Type='{fallacy_type}', Target='{target_argument_id or 'None'}'..."
        )
        try:
            fallacy_id = self._state.add_fallacy(
                fallacy_type, justification, target_argument_id, family=family
            )
            self._logger.info(
                f" -> Sophisme '{fallacy_id}' ajouté avec succès via l'état."
            )
            return fallacy_id
        except Exception as e:
            self._logger.error(
                f"Erreur lors de l'ajout du sophisme (Type: {fallacy_type}): {e}",
                exc_info=True,
            )
            return f"FUNC_ERROR: Erreur ajout sophisme: {e}"

    @kernel_function(
        description="Ajoute un belief set formel (ex: Propositional) à l'état.",
        name="add_belief_set",
    )
    def add_belief_set(self, logic_type: str, content: str) -> str:
        """Interface Kernel Function pour ajouter un belief set via l'état. Valide le type logique."""
        self._logger.info(
            f"Appel add_belief_set (state id: {id(self._state)}): Type='{logic_type}'..."
        )
        valid_logic_types = {
            "propositional": "Propositional",
            "pl": "Propositional",
            "fol": "FOL",
            "first_order": "FOL",
        }
        normalized_logic_type = logic_type.strip().lower()

        if normalized_logic_type not in valid_logic_types:
            error_msg = f"Type logique '{logic_type}' non supporté. Types valides (insensible casse): {list(valid_logic_types.keys())}"
            self._logger.error(error_msg)
            return f"FUNC_ERROR: {error_msg}"

        validated_logic_type = valid_logic_types[normalized_logic_type]
        try:
            bs_id = self._state.add_belief_set(validated_logic_type, content)
            self._logger.info(
                f" -> Belief Set '{bs_id}' ajouté avec succès via l'état (Type: {validated_logic_type})."
            )
            return bs_id
        except Exception as e:
            self._logger.error(
                f"Erreur interne lors de l'ajout du Belief Set (Type: {validated_logic_type}): {e}",
                exc_info=True,
            )
            return f"FUNC_ERROR: Erreur interne ajout Belief Set: {e}"

    @kernel_function(
        description="Enregistre une requête formelle et son résultat brut dans le log de l'état.",
        name="log_query_result",
    )
    def log_query_result(self, belief_set_id: str, query: str, raw_result: str) -> str:
        """Interface Kernel Function pour logger une requête via l'état."""
        self._logger.info(
            f"Appel log_query_result (state id: {id(self._state)}): BS_ID='{belief_set_id}', Query='{query[:60]}...'"
        )
        try:
            log_id = self._state.log_query(belief_set_id, query, raw_result)
            self._logger.info(f" -> Requête '{log_id}' loggée avec succès via l'état.")
            return log_id
        except Exception as e:
            self._logger.error(
                f"Erreur lors du logging de la requête (BS_ID: {belief_set_id}): {e}",
                exc_info=True,
            )
            return f"FUNC_ERROR: Erreur logging requête: {e}"

    @kernel_function(
        description=(
            "Enregistre une traduction NL → logique formelle dans l'état. "
            "Paramètres: original_text, formula, logic_type (propositional/fol), "
            "is_valid, variables (JSON), confidence (0-1)."
        ),
        name="add_nl_to_logic_translation",
    )
    def add_nl_to_logic_translation(
        self,
        original_text: str,
        formula: str,
        logic_type: str,
        is_valid: str = "true",
        variables: str = "{}",
        confidence: str = "0.7",
    ) -> str:
        """Interface Kernel Function pour enregistrer une traduction NL→logique."""
        self._logger.info(
            f"Appel add_nl_to_logic_translation: logic_type='{logic_type}', valid='{is_valid}'"
        )
        try:
            import json as _json

            parsed_vars = (
                _json.loads(variables) if isinstance(variables, str) else variables
            )
            tr_id = self._state.add_nl_to_logic_translation(
                original_text=original_text[:200],
                formula=formula,
                logic_type=logic_type,
                is_valid=is_valid.lower() in ("true", "1", "yes"),
                variables=parsed_vars,
                confidence=float(confidence),
            )
            self._logger.info(f" -> Traduction '{tr_id}' enregistrée via l'état.")
            return tr_id
        except Exception as e:
            self._logger.error(
                f"Erreur lors de l'ajout traduction NL→logique: {e}", exc_info=True
            )
            return f"FUNC_ERROR: Erreur ajout traduction: {e}"

    @kernel_function(
        description="Ajoute une réponse d'un agent à une tâche d'analyse spécifique dans l'état.",
        name="add_answer",
    )
    def add_answer(
        self, task_id: str, author_agent: str, answer_text: str, source_ids: List[str]
    ) -> str:
        """Interface Kernel Function pour ajouter une réponse via l'état."""
        self._logger.info(
            f"Appel add_answer (state id: {id(self._state)}): TaskID='{task_id}', Author='{author_agent}'..."
        )
        try:
            self._state.add_answer(task_id, author_agent, answer_text, source_ids)
            self._logger.info(
                f" -> Réponse pour tâche '{task_id}' ajoutée avec succès via l'état."
            )
            return f"OK: Réponse pour {task_id} ajoutée."
        except Exception as e:
            self._logger.error(
                f"Erreur lors de l'ajout de la réponse pour la tâche '{task_id}': {e}",
                exc_info=True,
            )
            return f"FUNC_ERROR: Erreur ajout réponse pour {task_id}: {e}"

    @kernel_function(
        description="Enregistre la conclusion finale de l'analyse dans l'état.",
        name="set_final_conclusion",
    )
    def set_final_conclusion(self, conclusion: str) -> str:
        """Interface Kernel Function pour enregistrer la conclusion via l'état."""
        self._logger.info(
            f"Appel set_final_conclusion (state id: {id(self._state)}): '{conclusion[:60]}...'"
        )
        try:
            self._state.set_conclusion(conclusion)
            self._logger.info(
                f" -> Conclusion finale enregistrée avec succès via l'état."
            )
            return "OK: Conclusion finale enregistrée."
        except Exception as e:
            self._logger.error(
                f"Erreur lors de l'enregistrement de la conclusion finale: {e}",
                exc_info=True,
            )
            return f"FUNC_ERROR: Erreur enregistrement conclusion: {e}"

    @kernel_function(
        description="Désigne quel agent doit parler au prochain tour. Utiliser le nom EXACT de l'agent.",
        name="designate_next_agent",
    )
    def designate_next_agent(self, agent_name: str) -> str:
        """Interface Kernel Function pour désigner le prochain agent via l'état."""
        self._logger.info(
            f"Appel designate_next_agent (state id: {id(self._state)}): Prochain = '{agent_name}'"
        )
        try:
            self._state.designate_next_agent(agent_name)
            self._logger.info(
                f" -> Agent '{agent_name}' désigné avec succès via l'état."
            )
            return f"OK. Agent '{agent_name}' désigné pour le prochain tour."
        except Exception as e:
            self._logger.error(
                f"Erreur lors de la désignation de l'agent '{agent_name}': {e}",
                exc_info=True,
            )
            return f"FUNC_ERROR: Erreur désignation agent {agent_name}: {e}"

    # =========================================================================
    # JTMS Hub Integration (#214)
    # =========================================================================

    @kernel_function(
        description="Create a JTMS belief with extended metadata (agent_source, confidence).",
        name="jtms_create_belief",
    )
    def jtms_create_belief(
        self,
        belief_name: str,
        agent_source: str = "unknown",
        confidence: float = 0.5,
        context: Optional[str] = None,
    ) -> str:
        """Create an ExtendedBelief in the JTMS session via StateManagerPlugin (#214)."""
        self._logger.info(
            f"Appel jtms_create_belief: '{belief_name}', source={agent_source}, conf={confidence}"
        )
        try:
            # Import here to avoid circular dependency
            raise ImportError("JTMS not available in CoursIA pedagogical mode")  # JTMS shim
            import json

            # Get or create JTMS session from state
            if not hasattr(self._state, "_jtms_session"):
                self._state._jtms_session = JTMSSession(
                    session_id="shared_jtms", owner_agent="state_manager_plugin"
                )

            session = self._state._jtms_session

            # Parse context if JSON string
            context_dict = {}
            if context:
                try:
                    context_dict = json.loads(context)
                except (json.JSONDecodeError, TypeError):
                    context_dict = {"raw": context}

            # Create extended belief
            ext_belief = session.add_belief(
                belief_name,
                agent_source=agent_source,
                context=context_dict,
                confidence=confidence,
            )

            # Sync to state.jtms_beliefs dict so enrichment summary sees it (#562)
            if hasattr(self._state, "add_jtms_belief"):
                justification_names = []
                self._state.add_jtms_belief(
                    name=belief_name,
                    valid=True,
                    justifications=justification_names,
                )

            self._logger.info(
                f" -> Belief '{belief_name}' created with ExtendedBelief metadata"
            )
            return f"OK: Belief '{belief_name}' created by {agent_source}"

        except Exception as e:
            self._logger.error(
                f"Error creating JTMS belief '{belief_name}': {e}", exc_info=True
            )
            return f"FUNC_ERROR: Error creating belief: {e}"

    @kernel_function(
        description="Add a JTMS justification between beliefs (IN-list and OUT-list).",
        name="jtms_add_justification",
    )
    def jtms_add_justification(
        self,
        in_list: List[str],
        out_list: List[str],
        conclusion: str,
        agent_source: str = "unknown",
    ) -> str:
        """Add a justification with ExtendedBelief tracking via StateManagerPlugin (#214)."""
        self._logger.info(
            f"Appel jtms_add_justification: IN={len(in_list)}, OUT={len(out_list)}, conclusion={conclusion}"
        )
        try:
            raise ImportError("JTMS not available in CoursIA pedagogical mode")  # JTMS shim

            # Get or create JTMS session
            if not hasattr(self._state, "_jtms_session"):
                self._state._jtms_session = JTMSSession(
                    session_id="shared_jtms", owner_agent="state_manager_plugin"
                )

            session = self._state._jtms_session

            # Add justification with agent source tracking
            session.add_justification(
                in_list, out_list, conclusion, agent_source=agent_source
            )

            self._logger.info(
                f" -> Justification for '{conclusion}' added by {agent_source}"
            )
            return f"OK: Justification for '{conclusion}' added by {agent_source}"

        except Exception as e:
            self._logger.error(f"Error adding JTMS justification: {e}", exc_info=True)
            return f"FUNC_ERROR: Error adding justification: {e}"

    @kernel_function(
        description="Query JTMS beliefs with ExtendedBelief metadata (agent_source, confidence, history).",
        name="jtms_query_beliefs",
    )
    def jtms_query_beliefs(self, agent_filter: Optional[str] = None) -> str:
        """Query JTMS beliefs with ExtendedBelief metadata via StateManagerPlugin (#214)."""
        self._logger.info(f"Appel jtms_query_beliefs: filter={agent_filter}")
        try:
            raise ImportError("JTMS not available in CoursIA pedagogical mode")  # JTMS shim
            import json

            # Get JTMS session
            if not hasattr(self._state, "_jtms_session"):
                return "FUNC_ERROR: No JTMS session initialized. Call jtms_create_belief first."

            session = self._state._jtms_session

            # Build query results with ExtendedBelief metadata
            results = []
            for name, ext_belief in session.extended_beliefs.items():
                # Apply filter if specified
                if agent_filter and ext_belief.agent_source != agent_filter:
                    continue

                belief_data = {
                    "name": name,
                    "valid": ext_belief.valid,
                    "agent_source": ext_belief.agent_source,
                    "confidence": ext_belief.confidence,
                    "context": ext_belief.context,
                    "creation_timestamp": ext_belief.creation_timestamp.isoformat(),
                    "modification_count": len(ext_belief.modification_history),
                    "justification_count": len(ext_belief.justifications),
                }
                results.append(belief_data)

            self._logger.info(f" -> Found {len(results)} beliefs matching filter")
            return json.dumps(results, ensure_ascii=False, indent=2)

        except Exception as e:
            self._logger.error(f"Error querying JTMS beliefs: {e}", exc_info=True)
            return f"FUNC_ERROR: Error querying beliefs: {e}"

    @kernel_function(
        description="Check JTMS session consistency and return conflict report.",
        name="jtms_check_consistency",
    )
    def jtms_check_consistency(self) -> str:
        """Check JTMS consistency and return conflict report via StateManagerPlugin (#214)."""
        self._logger.info("Appel jtms_check_consistency")
        try:
            raise ImportError("JTMS not available in CoursIA pedagogical mode")  # JTMS shim
            import json

            # Get JTMS session
            if not hasattr(self._state, "_jtms_session"):
                return "FUNC_ERROR: No JTMS session initialized."

            session = self._state._jtms_session

            # Check consistency
            consistency_result = session.check_consistency()

            result = {
                "is_consistent": consistency_result.get("is_consistent", True),
                "conflicts_detected": consistency_result.get("conflicts", []),
                "total_beliefs": len(session.extended_beliefs),
                "consistency_checks": session.consistency_checks,
                "session_version": session.version,
            }

            self._logger.info(f" -> Consistency check: {result['is_consistent']}")
            return json.dumps(result, ensure_ascii=False, indent=2)

        except Exception as e:
            self._logger.error(f"Error checking JTMS consistency: {e}", exc_info=True)
            return f"FUNC_ERROR: Error checking consistency: {e}"

    @kernel_function(
        description=(
            "Retract a JTMS belief by setting its validity to False and propagating. "
            "Use this when a fallacy is detected on an argument — the belief and all "
            "beliefs that depend solely on it will be marked as defeated. "
            "Parameters: belief_name (str), reason (str, e.g. 'fallacy: appeal to authority')."
        ),
        name="jtms_retract_belief",
    )
    def jtms_retract_belief(self, belief_name: str, reason: str = "") -> str:
        """Retract a JTMS belief, propagating to dependent beliefs (#287).

        This is the core TMS retraction mechanism: when a fallacy is detected
        on argument N, calling jtms_retract_belief('arg_N', 'fallacy: ...') will:
        1. Set the belief's truth value to None (unknown/defeated)
        2. Propagate: all beliefs justified solely by arg_N become OUT
        3. Record the retraction in the belief's modification history
        """
        self._logger.info(
            f"Appel jtms_retract_belief: '{belief_name}', reason='{reason[:60]}'"
        )
        try:
            raise ImportError("JTMS not available in CoursIA pedagogical mode")  # JTMS shim

            if not hasattr(self._state, "_jtms_session"):
                return "FUNC_ERROR: No JTMS session initialized. Call jtms_create_belief first."

            session = self._state._jtms_session

            # Check belief exists
            if belief_name not in session.extended_beliefs:
                # Try partial match (agents may use slightly different names)
                candidates = [
                    name
                    for name in session.extended_beliefs
                    if belief_name.lower() in name.lower()
                    or name.lower() in belief_name.lower()
                ]
                if candidates:
                    belief_name = candidates[0]
                    self._logger.info(f" -> Partial match: using '{belief_name}'")
                else:
                    return (
                        f"FUNC_ERROR: Belief '{belief_name}' not found in JTMS session."
                    )

            ext_belief = session.extended_beliefs[belief_name]

            # Record retraction in history
            was_valid = ext_belief.valid

            # Use core JTMS set_belief_validity to propagate
            session.jtms.set_belief_validity(belief_name, None)

            # Record retraction in extended belief via modification history
            import datetime as _dt

            ext_belief.record_modification(
                "retract",
                {
                    "reason": reason,
                    "timestamp": _dt.datetime.now().isoformat(),
                },
            )
            ext_belief.context["retracted"] = True
            ext_belief.context["retraction_reason"] = reason

            # Sync retraction to state.jtms_beliefs dict so enrichment sees it (#562)
            if hasattr(self._state, "jtms_beliefs"):
                for bid, bdata in self._state.jtms_beliefs.items():
                    if bdata.get("name") == belief_name:
                        bdata["valid"] = False
                        bdata["retracted"] = True
                        bdata["retraction_reason"] = reason
                        break

            # Count affected beliefs (beliefs that lost their justification)
            affected = []
            for name, b in session.extended_beliefs.items():
                if name != belief_name and not b.valid:
                    # Check if this belief was justified by the retracted one
                    for j in b.justifications:
                        if belief_name in j.get("in_list", []):
                            affected.append(name)

            result = {
                "retracted_belief": belief_name,
                "was_valid": was_valid,
                "reason": reason,
                "affected_beliefs": affected,
                "affected_count": len(affected),
            }

            self._logger.info(
                f" -> Belief '{belief_name}' retracted. {len(affected)} dependent beliefs affected."
            )
            import json

            return json.dumps(result, ensure_ascii=False, indent=2)

        except Exception as e:
            self._logger.error(
                f"Error retracting belief '{belief_name}': {e}", exc_info=True
            )
            return f"FUNC_ERROR: Error retracting belief: {e}"

    # =========================================================================
    # Phase result writers — @kernel_function wrappers for add_* methods (#469)
    # =========================================================================

    @kernel_function(
        description="Add an extract (text segment identified during extraction).",
        name="add_extract",
    )
    def add_extract(self, name: str, content: str) -> str:
        try:
            ext_id = self._state.add_extract(name, content)
            return ext_id
        except Exception as e:
            return f"FUNC_ERROR: {e}"

    @kernel_function(
        description="Add a counter-argument result. Params: original_arg, counter_content, strategy, score (0-1), target_arg_id (optional).",
        name="add_counter_argument",
    )
    def add_counter_argument(
        self,
        original_arg: str,
        counter_content: str,
        strategy: str,
        score: str = "0.5",
        target_arg_id: str = "",
    ) -> str:
        try:
            ca_id = self._state.add_counter_argument(
                original_arg,
                counter_content,
                strategy,
                float(score),
                target_arg_id=target_arg_id or None,
            )
            return ca_id
        except Exception as e:
            return f"FUNC_ERROR: {e}"

    @kernel_function(
        description="Add quality scores for an argument. Params: arg_id, scores_json (virtue→float), overall (0-1).",
        name="add_quality_score",
    )
    def add_quality_score(
        self, arg_id: str, scores_json: str, overall: str = "0.5"
    ) -> str:
        try:
            scores = json.loads(scores_json) if isinstance(scores_json, str) else scores_json
            self._state.add_quality_score(arg_id, scores, float(overall))
            return f"OK: Quality scores added for {arg_id}"
        except Exception as e:
            return f"FUNC_ERROR: {e}"

    @kernel_function(
        description="Add a Dung argumentation framework. Params: name, arguments_json (list), attacks_json (list of pairs), extensions_json (optional).",
        name="add_dung_framework",
    )
    def add_dung_framework(
        self,
        name: str,
        arguments_json: str,
        attacks_json: str,
        extensions_json: str = "{}",
    ) -> str:
        try:
            arguments = json.loads(arguments_json)
            attacks = json.loads(attacks_json)
            extensions = json.loads(extensions_json) if extensions_json != "{}" else None
            df_id = self._state.add_dung_framework(name, arguments, attacks, extensions)
            return df_id
        except Exception as e:
            return f"FUNC_ERROR: {e}"

    @kernel_function(
        description="Add a governance/voting decision. Params: method (copeland/borda/...), winner, scores_json.",
        name="add_governance_decision",
    )
    def add_governance_decision(
        self, method: str, winner: str, scores_json: str
    ) -> str:
        try:
            scores = json.loads(scores_json)
            gd_id = self._state.add_governance_decision(method, winner, scores)
            return gd_id
        except Exception as e:
            return f"FUNC_ERROR: {e}"

    @kernel_function(
        description="Add a debate transcript. Params: topic, exchanges_json (list of {speaker, content}), winner (optional).",
        name="add_debate_transcript",
    )
    def add_debate_transcript(
        self, topic: str, exchanges_json: str, winner: str = ""
    ) -> str:
        try:
            exchanges = json.loads(exchanges_json)
            dt_id = self._state.add_debate_transcript(
                topic, exchanges, winner if winner else None
            )
            return dt_id
        except Exception as e:
            return f"FUNC_ERROR: {e}"

    @kernel_function(
        description="Add a ranking semantics result. Params: method, arguments_json (list), comparisons_json (list).",
        name="add_ranking_result",
    )
    def add_ranking_result(
        self, method: str, arguments_json: str, comparisons_json: str
    ) -> str:
        try:
            arguments = json.loads(arguments_json)
            comparisons = json.loads(comparisons_json)
            rk_id = self._state.add_ranking_result(method, arguments, comparisons)
            return rk_id
        except Exception as e:
            return f"FUNC_ERROR: {e}"

    @kernel_function(
        description="Add an ASPIC+ analysis result. Params: reasoner_type, extensions_json, statistics_json.",
        name="add_aspic_result",
    )
    def add_aspic_result(
        self, reasoner_type: str, extensions_json: str, statistics_json: str
    ) -> str:
        try:
            extensions = json.loads(extensions_json)
            statistics = json.loads(statistics_json)
            as_id = self._state.add_aspic_result(reasoner_type, extensions, statistics)
            return as_id
        except Exception as e:
            return f"FUNC_ERROR: {e}"

    @kernel_function(
        description="Add a belief revision result. Params: method, original_json (list), revised_json (list).",
        name="add_belief_revision_result",
    )
    def add_belief_revision_result(
        self, method: str, original_json: str, revised_json: str
    ) -> str:
        try:
            original = json.loads(original_json)
            revised = json.loads(revised_json)
            br_id = self._state.add_belief_revision_result(method, original, revised)
            return br_id
        except Exception as e:
            return f"FUNC_ERROR: {e}"

    @kernel_function(
        description="Add a neural fallacy detection score. Params: text_segment, label, confidence (0-1).",
        name="add_neural_fallacy_score",
    )
    def add_neural_fallacy_score(
        self, text_segment: str, label: str, confidence: str = "0.5"
    ) -> str:
        try:
            nf_id = self._state.add_neural_fallacy_score(
                text_segment, label, float(confidence)
            )
            return nf_id
        except Exception as e:
            return f"FUNC_ERROR: {e}"

    @kernel_function(
        description="Set the workflow execution results. Params: workflow_name, results_json.",
        name="set_workflow_results",
    )
    def set_workflow_results(self, workflow_name: str, results_json: str) -> str:
        try:
            results = json.loads(results_json)
            self._state.set_workflow_results(workflow_name, results)
            return f"OK: Workflow results set for {workflow_name}"
        except Exception as e:
            return f"FUNC_ERROR: {e}"
