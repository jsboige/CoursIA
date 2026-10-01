# Verbatim copy of `argumentation_analysis/core/shared_state.py` from
# the 2025-Epita-Intelligence-Symbolique project
# (https://github.com/jsboigeEpita/2025-Epita-Intelligence-Symbolique),
# Copyright (c) 2025 jsboigeEpita, MIT License.
# Source commit: bfff7542 (2026-09-29) "fix(env): one provider of libiomp5md.dll
# in the gate solve, torch loads in CI (#2856) (#2861)".
# Verbatim import rationale: see NOTICE-EPITA at the root of this directory.
#
# Verbatim integrity: file content below this header is byte-for-byte identical
# to the upstream source at the cited commit, minus the deliberate perimeter
# documented below (no other CoursIA modification -- downstream consumers wrap
# or extend, never replace the verbatim block).
# Note: the upstream copy is **partial** (See NOTICE-EPITA, section "Partial
# copies" + issue #14026): the designation machinery + structured-arg surface
# are deliberately absent (EPIC #4960 perimeter, not a drift):
# DesignationRecord, record_designation, _designation_fingerprint,
# _designation_delta_summary, backfill_last_designation_for, record_cap_breach,
# record_designation_unresolved, record_unresolved_designation,
# set_source_metadata, add_structured_arg_status.
# Re-vendored 2026-09-29 a8025f60 -> bfff7542 (audit #18478): the retained
# perimeter had evolved upstream (13 symbols, incl. the #1942 quality-unit
# contract); drift note in NOTICE-EPITA.
import json
from dataclasses import dataclass, field, asdict
from typing import Dict, List, Any, Optional, cast
import logging

# Logger spécifique pour l'état
state_logger = logging.getLogger("RhetoricalAnalysisState")
# Assurer qu'un handler de base est présent si non configuré globalement tôt
if not state_logger.handlers and not state_logger.propagate:
    handler = logging.StreamHandler()
    formatter = logging.Formatter(
        "%(asctime)s [%(levelname)s] [%(name)s] %(message)s", datefmt="%H:%M:%S"
    )
    handler.setFormatter(formatter)
    state_logger.addHandler(handler)
    state_logger.setLevel(logging.INFO)


@dataclass
class ArgumentProfile:
    """Aggregated view of all analysis data for a single argument."""

    arg_id: str
    description: str
    fallacies: List[Dict[str, Any]] = field(default_factory=list)
    quality_score: Optional[Dict[str, Any]] = None
    counter_arguments: List[Dict[str, Any]] = field(default_factory=list)
    jtms_beliefs: List[Dict[str, Any]] = field(default_factory=list)
    formal_results: List[Dict[str, Any]] = field(default_factory=list)


# CoursIA-only divergence (documented in NOTICE-EPITA, drift note for
# _shared_state.py, audit #18478): upstream get_weak_arguments imports
# quality_fraction from argumentation_analysis.plugins.narrative_synthesis_plugin
# (bfff7542 l.277) -- a module outside the vendoring perimeter. The function is
# inlined VERBATIM from that source; same definition, one place.
def quality_fraction(entry: Any) -> Optional[float]:
    """Normalize a STORED quality entry to the [0, 1] reader scale (#1942).

    ``overall`` is the SUM of per-virtue [0, 1] scores over the EVALUATED
    virtues -- not a 0-1 average, not a note sur 10 (three unit contracts
    disagreed on this before #1942: the evaluator sums, two LLM-facing
    descriptions said 0-1). The denominator is ``len(scores)``: post-#1923
    the tri-state machinery leaves inapplicable virtues absent, so the
    ceiling varies by input unit ({2, 6, 8} measured on real texts). Same
    semantics as the trace-side ``_quality_fraction`` of #1907 -- the share
    of the reachable ceiling that held; ``None`` = unmeasured, never 0.
    """
    if not isinstance(entry, dict):
        return None
    overall = entry.get("overall")
    scores = entry.get("scores")
    if (
        not isinstance(overall, (int, float))
        or not isinstance(scores, dict)
        or not scores
    ):
        return None
    return float(overall) / len(scores)

def count_designation_turns(trace: Any) -> int:
    """Number of genuine PM designations in a deliberation trace (#1765).

    A :class:`DesignationRecord` carries **no** ``record_type`` (it is the
    ``asdict`` of the dataclass); every non-designation entry declares one.
    Counting by allow-list — "a designation is a record with no marker" —
    instead of by exclusion list ("everything that is not a ``cap_breach``")
    is what keeps this number honest when a marker type is added.

    #1765: this is the single definition. #1751 flipped the orchestrator's
    copy to the allow-list and left the state snapshot's copy on the exclusion
    list, so the same field name reported two different numbers — and the
    inflated one was the one handed to the agents (``get_current_state_snapshot``
    defaults to ``summarize=True``). One name, one calculation, two callers.
    """
    return sum(
        1 for r in trace or [] if isinstance(r, dict) and r.get("record_type") is None
    )


class RhetoricalAnalysisState:
    """Représente l'état partagé d'une analyse rhétorique collaborative."""

    # ... (Le code complet de la classe RhetoricalAnalysisState tel que fourni dans la réponse précédente va ici) ...
    # Structure des données de l'état (pour référence)
    raw_text: str
    analysis_tasks: Dict[str, str]  # {task_id: description}
    identified_arguments: Dict[str, str]  # {arg_id: description}
    identified_fallacies: Dict[
        str, Dict[str, str]
    ]  # {fallacy_id: {type:..., justification:..., target_argument_id?:...}}
    belief_sets: Dict[
        str, Dict[str, Any]
    ]  # {bs_id: {logic_type:..., content:..., propositions?:[...]}}
    query_log: List[
        Dict[str, str]
    ]  # [{log_id:..., belief_set_id:..., query:..., raw_result:...}]
    answers: Dict[
        str, Dict[str, Any]
    ]  # {task_id: {author_agent:..., answer_text:..., source_ids:[...]}}
    final_conclusion: Optional[str]
    _next_agent_designated: Optional[
        str
    ]  # Nom de l'agent désigné pour le prochain tour

    def __init__(self, initial_text: str):
        """Initialise un état vide avec le texte brut."""
        self.raw_text = initial_text
        self.analysis_tasks = {}
        self.identified_arguments = {}
        self.identified_fallacies = {}
        self.belief_sets = {}
        self.query_log = []
        self.answers = {}
        self.extracts: List[Dict[str, Any]] = []
        self.errors: List[Dict[str, Any]] = []
        self.final_conclusion = None
        self._next_agent_designated = None
        # #1737: dernière sélection de fenêtre de lecture par site —
        # {site: {"status": ..., "offset": ..., "window": ...}}. Écrit par
        # reading_window.selected_text, lu par le rapport (build_narrative).
        self.reading_window_status: Dict[str, Dict[str, Any]] = {}
        state_logger.debug(
            f"Nouvelle instance RhetoricalAnalysisState créée (id: {id(self)}) avec texte (longueur: {len(initial_text)})."
        )

    def record_reading_window(self, site: str, selection: Any) -> None:
        """#1737 — enregistre la sélection de fenêtre d'un site de lecture.

        Le statut tri-état (selected / no_punctuated_span_found / empty_input
        / short_input) doit rester visible jusqu'au rapport : un statut que
        personne ne relit est la forme #1019.
        """
        self.reading_window_status[site] = {
            "status": getattr(selection, "status", str(selection)),
            "offset": getattr(selection, "offset", 0),
            "window": getattr(selection, "window", 0),
        }

    def _generate_id(self, prefix: str, current_dict_or_list: Any) -> str:
        """Génère un ID simple basé sur la taille actuelle."""
        index = 0
        try:
            if isinstance(current_dict_or_list, (dict, list)):
                index = len(current_dict_or_list)
            else:
                index = 0
                state_logger.warning(
                    f"_generate_id: Type inattendu '{type(current_dict_or_list)}' pour prefix '{prefix}'. Index sera 0."
                )
        except Exception as e:
            state_logger.error(
                f"Erreur dans _generate_id pour prefix '{prefix}': {e}", exc_info=True
            )
            index = 999
        safe_index = min(index, 9999)
        return f"{prefix}_{safe_index + 1}"

    def add_task(self, description: str) -> str:
        """Ajoute une tâche d'analyse et retourne son ID."""
        task_id = self._generate_id("task", self.analysis_tasks)
        self.analysis_tasks[task_id] = description
        state_logger.info(f"Tâche ajoutée: {task_id} - '{description[:60]}...'")
        state_logger.debug(f"État tasks après ajout {task_id}: {self.analysis_tasks}")
        return task_id

    def add_argument(self, description: str) -> str:
        """Ajoute un argument identifié et retourne son ID."""
        arg_id = self._generate_id("arg", self.identified_arguments)
        self.identified_arguments[arg_id] = description
        state_logger.info(f"Argument ajouté: {arg_id} - '{description[:60]}...'")
        state_logger.debug(
            f"État arguments après ajout {arg_id}: {self.identified_arguments}"
        )
        return arg_id

    def add_fallacy(
        self,
        fallacy_type: str,
        justification: str,
        target_arg_id: Optional[str] = None,
        family: str = "",
        taxonomy_path: str = "",
    ) -> str:
        """Ajoute un sophisme identifié et retourne son ID."""
        fallacy_id = self._generate_id("fallacy", self.identified_fallacies)
        entry = {"type": fallacy_type, "justification": justification}
        if family:
            entry["family"] = family
        if taxonomy_path:
            entry["taxonomy_path"] = taxonomy_path
        log_target_info = ""
        if target_arg_id:
            if target_arg_id not in self.identified_arguments:
                state_logger.warning(
                    f"ID argument cible '{target_arg_id}' pour sophisme '{fallacy_id}' non trouvé dans les arguments identifiés ({list(self.identified_arguments.keys())})."
                )
            entry["target_argument_id"] = target_arg_id
            log_target_info = f" (cible: {target_arg_id})"
        self.identified_fallacies[fallacy_id] = entry
        state_logger.info(
            f"Sophisme ajouté: {fallacy_id} - Type: {fallacy_type}{log_target_info}"
        )
        state_logger.debug(
            f"État fallacies après ajout {fallacy_id}: {self.identified_fallacies}"
        )
        return fallacy_id

    def add_belief_set(
        self,
        logic_type: str,
        content: str,
        propositions: Optional[List[str]] = None,
    ) -> str:
        """Ajoute un belief set formel et retourne son ID.

        ``propositions`` (PL) est conservé quand il est fourni : l'agent
        propositionnel n'interroge que des propositions déclarées, donc un
        belief set reconstruit sans elles ne donne aucune requête (#2643).
        """
        normalized_type = logic_type.strip().lower().replace(" ", "_")
        bs_id = self._generate_id(f"{normalized_type}_bs", self.belief_sets)
        entry: Dict[str, Any] = {"logic_type": logic_type, "content": content}
        if propositions is not None:
            entry["propositions"] = list(propositions)
        self.belief_sets[bs_id] = entry
        state_logger.info(f"Belief Set ajouté: {bs_id} - Type: {logic_type}")
        state_logger.debug(f"État belief_sets après ajout {bs_id}: {self.belief_sets}")
        return bs_id

    def log_query(self, belief_set_id: str, query: str, raw_result: str) -> str:
        """Enregistre une requête formelle et son résultat brut."""
        log_id = self._generate_id("qlog", self.query_log)
        if belief_set_id not in self.belief_sets:
            state_logger.warning(
                f"ID Belief Set '{belief_set_id}' pour query log '{log_id}' non trouvé dans les belief sets ({list(self.belief_sets.keys())})."
            )
        log_entry = {
            "log_id": log_id,
            "belief_set_id": belief_set_id,
            "query": query,
            "raw_result": raw_result,
        }
        self.query_log.append(log_entry)
        state_logger.info(
            f"Requête loggée: {log_id} (sur BS: {belief_set_id}, Query: '{query[:60]}...')"
        )
        state_logger.debug(
            f"État query_log après ajout {log_id} (taille: {len(self.query_log)}): {self.query_log}"
        )
        return log_id

    def add_answer(
        self, task_id: str, author_agent: str, answer_text: str, source_ids: List[str]
    ) -> None:
        """Ajoute la réponse d'un agent à une tâche spécifiques."""
        if task_id not in self.analysis_tasks:
            state_logger.warning(
                f"ID Tâche '{task_id}' pour réponse de '{author_agent}' non trouvé dans les tâches définies ({list(self.analysis_tasks.keys())})."
            )
        self.answers[task_id] = {
            "author_agent": author_agent,
            "answer_text": answer_text,
            "source_ids": source_ids,
        }
        state_logger.info(
            f"Réponse ajoutée pour tâche '{task_id}' par agent '{author_agent}'."
        )
        state_logger.debug(
            f"État answers après ajout réponse pour {task_id}: {self.answers}"
        )

    def set_conclusion(self, conclusion: str) -> None:
        """Enregistre la conclusion finale de l'analyse."""
        self.final_conclusion = conclusion
        state_logger.info(f"Conclusion finale enregistrée : '{conclusion[:60]}...'")
        state_logger.debug(
            f"État final_conclusion après enregistrement: {self.final_conclusion is not None}"
        )

    def add_identified_arguments(self, arguments: List[str]) -> None:
        """Ajoute une liste d'arguments identifiés."""
        state_logger.info(f"Ajout de {len(arguments)} arguments identifiés...")
        for arg_desc in arguments:
            self.add_argument(arg_desc)

    def add_identified_fallacies(self, fallacies: List[Dict[str, str]]) -> None:
        """Ajoute une liste de sophismes identifiés."""
        state_logger.info(f"Ajout de {len(fallacies)} sophismes identifiés...")
        for fallacy_data in fallacies:
            self.add_fallacy(
                fallacy_type=fallacy_data.get("nom", "Type Inconnu"),
                justification=fallacy_data.get(
                    "explication", "Justification manquante"
                ),
                family=fallacy_data.get("famille", ""),
                taxonomy_path=fallacy_data.get("taxonomy_path", ""),
            )

    def mark_task_as_answered(
        self, task_id: str, answer: str, author: str = "Unknown"
    ) -> None:
        """Marque une tâche comme terminée en lui ajoutant une réponse."""
        if task_id not in self.analysis_tasks:
            state_logger.warning(
                f"Tentative de marquer comme répondue une tâche inexistante: '{task_id}'"
            )
            return
        self.answers[task_id] = {"answer_text": answer, "author_agent": author}
        state_logger.info(f"Tâche '{task_id}' marquée comme répondue.")

    def get_last_task_id(self) -> Optional[str]:
        """Retourne l'ID de la dernière tâche non répondue."""
        defined_tasks = set(self.analysis_tasks.keys())
        answered_tasks = set(self.answers.keys())
        unanswered_tasks = list(defined_tasks - answered_tasks)
        if not unanswered_tasks:
            return None
        # On pourrait avoir une logique plus complexe, mais pour l'instant on prend la dernière créée
        return unanswered_tasks[-1]

    def designate_next_agent(self, agent_name: str) -> None:
        """Désigne l'agent qui doit parler au prochain tour."""
        self._next_agent_designated = agent_name
        state_logger.info(f"Prochain agent désigné: '{agent_name}'")
        state_logger.debug(
            f"État _next_agent_designated après désignation: '{self._next_agent_designated}'"
        )

    def add_extract(self, name: str, content: str) -> str:
        """Ajoute un extrait de texte et retourne son ID."""
        if not hasattr(self, "extracts"):
            self.extracts = []
        extract_id = self._generate_id("extract", self.extracts)
        extract = {"id": extract_id, "name": name, "content": content}
        self.extracts.append(extract)
        state_logger.info(f"Extrait ajouté: {extract_id} - '{name}'")
        state_logger.debug(f"État extracts après ajout {extract_id}: {self.extracts}")
        return extract_id

    def log_error(self, agent_name: str, message: str) -> str:
        """Enregistre une erreur et retourne son ID."""
        if not hasattr(self, "errors"):
            self.errors = []
        error_id = self._generate_id("error", self.errors)
        error = {
            "id": error_id,
            "agent_name": agent_name,
            "message": message,
            "timestamp": None,
        }
        self.errors.append(error)
        state_logger.warning(
            f"Erreur enregistrée: {error_id} - Agent: {agent_name} - '{message}'"
        )
        state_logger.debug(f"État errors après ajout {error_id}: {self.errors}")
        return error_id

    def consume_next_agent_designation(self) -> Optional[str]:
        """Récupère le nom de l'agent désigné et réinitialise la désignation."""
        agent_name = self._next_agent_designated
        self._next_agent_designated = None
        if agent_name:
            state_logger.info(f"Désignation pour '{agent_name}' consommée.")
        return agent_name

    def reset_state(self) -> None:
        """Réinitialise l'état à son état initial (vide sauf texte brut)."""
        state_logger.info(">>> Réinitialisation de l'état d'analyse...")
        initial_text = self.raw_text
        self.__init__(initial_text)  # type: ignore[misc]
        assert not self.analysis_tasks, "Reset analysis_tasks failed"
        assert not self.identified_arguments, "Reset identified_arguments failed"
        assert not self.identified_fallacies, "Reset identified_fallacies failed"
        assert not self.belief_sets, "Reset belief_sets failed"
        assert not self.query_log, "Reset query_log failed"
        assert not self.answers, "Reset answers failed"
        assert self.final_conclusion is None, "Reset final_conclusion failed"
        assert (
            self._next_agent_designated is None
        ), "Reset _next_agent_designated failed"
        # Réinitialiser les attributs extracts et errors s'ils existent
        if hasattr(self, "extracts"):
            self.extracts = []
        if hasattr(self, "errors"):
            self.errors = []
        state_logger.info("<<< Réinitialisation de l'état terminée et vérifiée.")

    def get_state_snapshot(self, summarize: bool = False) -> Dict[str, Any]:
        """Retourne un dictionnaire représentant l'état actuel (complet ou résumé)."""
        if summarize:
            # Assurer que le texte est tronqué dans le résumé
            truncated_text = (
                self.raw_text[:50] + "..." if len(self.raw_text) > 50 else self.raw_text
            )
            return {
                "raw_text": (
                    self.raw_text[:150] + "..."
                    if len(self.raw_text) > 150
                    else self.raw_text
                ),
                "raw_text_snippet": (
                    self.raw_text[:150] + "..."
                    if len(self.raw_text) > 150
                    else self.raw_text
                ),
                "task_count": len(self.analysis_tasks),
                "tasks_defined": list(self.analysis_tasks.keys()),
                "argument_count": len(self.identified_arguments),
                "fallacy_count": len(self.identified_fallacies),
                "belief_set_count": len(self.belief_sets),
                "query_log_count": len(self.query_log),
                "answer_count": len(self.answers),
                "extract_count": len(getattr(self, "extracts", [])),
                "error_count": len(getattr(self, "errors", [])),
                "tasks_answered": list(self.answers.keys()),
                "conclusion_present": self.final_conclusion is not None,
                "next_agent_designated": self._next_agent_designated,
                # CONV-C #1334: deliberation trace (count only in the summary;
                # full records via the non-summarized snapshot / direct field).
                # #1765: allow-list, via the single definition. This snapshot is
                # what ``get_current_state_snapshot`` hands the agents, so an
                # exclusion list here made the PM read its own absorbed
                # designations (#1751 markers) as conduction turns it had spent.
                "deliberation_turn_count": count_designation_turns(
                    getattr(self, "deliberation_trace", [])
                ),
            }
        else:
            return cast(Dict[str, Any], json.loads(self.to_json(indent=None)))

    def to_json(self, indent: Optional[int] = 2) -> str:
        """Sérialise l'état actuel en chaîne JSON."""
        state_dict = {
            k: v
            for k, v in self.__dict__.items()
            if not callable(v) and not k.startswith("_logger")
        }
        try:
            return json.dumps(
                state_dict, indent=indent, ensure_ascii=False, default=str
            )
        except TypeError as e:
            state_logger.error(f"Erreur de sérialisation JSON de l'état: {e}")
            safe_dict = {k: repr(v) for k, v in state_dict.items()}
            return json.dumps(
                {
                    "error": f"JSON serialization failed: {e}",
                    "safe_state_repr": safe_dict,
                },
                indent=indent,
            )

    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> "RhetoricalAnalysisState":
        """Crée une instance d'état à partir d'un dictionnaire."""
        state = cls(data.get("raw_text", ""))
        state.analysis_tasks = data.get("analysis_tasks", {})
        state.identified_arguments = data.get("identified_arguments", {})
        state.identified_fallacies = data.get("identified_fallacies", {})
        state.belief_sets = data.get("belief_sets", {})
        state.query_log = data.get("query_log", [])
        state.answers = data.get("answers", {})
        state.extracts = data.get("extracts", [])
        state.errors = data.get("errors", [])
        state.final_conclusion = data.get("final_conclusion", None)
        state._next_agent_designated = data.get("_next_agent_designated", None)
        state_logger.debug(
            f"Instance RhetoricalAnalysisState créée depuis dict (id: {id(state)})."
        )
        return state


class UnifiedAnalysisState(RhetoricalAnalysisState):
    """Extended state encompassing all integrated student project dimensions.

    Adds fields for counter-arguments, argument quality, JTMS beliefs,
    Dung frameworks, governance decisions, debate transcripts, transcription
    segments, semantic index references, and neural fallacy scores.
    """

    def __init__(self, initial_text: str):
        super().__init__(initial_text)
        # Counter-argument generation (2.3.3)
        self.counter_arguments: List[Dict[str, Any]] = []
        # Argument quality evaluation (2.3.5)
        self.argument_quality_scores: Dict[str, Dict[str, Any]] = {}
        # JTMS belief network (1.4.1)
        self.jtms_beliefs: Dict[str, Dict[str, Any]] = {}
        # JTMS retraction cascade chains (#350)
        self.jtms_retraction_chain: List[Dict[str, Any]] = []
        # Dung abstract argumentation frameworks (abs_arg_dung)
        self.dung_frameworks: Dict[str, Dict[str, Any]] = {}
        # Governance decisions and votes (2.1.6)
        self.governance_decisions: List[Dict[str, Any]] = []
        # Debate transcripts (1.2.7)
        self.debate_transcripts: List[Dict[str, Any]] = []
        # Speech transcription segments (speech-to-text)
        self.transcription_segments: List[Dict[str, Any]] = []
        # Semantic index references (Arg_Semantic_Index)
        self.semantic_index_refs: List[Dict[str, Any]] = []
        # Neural fallacy detection scores (2.3.2 CamemBERT)
        self.neural_fallacy_scores: List[Dict[str, Any]] = []
        # Track A: Tweety handler results (#55-#62)
        self.ranking_results: List[Dict[str, Any]] = []
        self.aspic_results: List[Dict[str, Any]] = []
        self.belief_revision_results: List[Dict[str, Any]] = []
        self.dialogue_results: List[Dict[str, Any]] = []
        self.probabilistic_results: List[Dict[str, Any]] = []
        self.bipolar_results: List[Dict[str, Any]] = []
        # Structured-argumentation honest-absent status (FP-17 #1236). The
        # formalisms ASPIC+/ABA/SETAF/weighted/bipolar require a text→structured
        # translator (defeasible rules, assumptions+contraries, collective
        # attacks, weights, support-relations) that is NOT wired — the
        # translation-gap diagnosed in FP-4 (#1201). On real corpora they run on
        # auto-shaped synthetic input, so an empty extension list means "never
        # genuinely fed structured input", NOT "evaluated, found nothing". This
        # map records that distinction per capability so the snapshot/report can
        # surface it instead of a silent [] (#1019). Keyed by capability name.
        self.structured_arg_status: Dict[str, Dict[str, Any]] = {}
        # Logic agent analysis results (#71 formal verification)
        self.fol_analysis_results: List[Dict[str, Any]] = []
        self.fol_signature: List[str] = []  # Pre-declared sorts/types (#348)
        self.propositional_analysis_results: List[Dict[str, Any]] = []
        self.modal_analysis_results: List[Dict[str, Any]] = []
        self.formal_synthesis_reports: List[Dict[str, Any]] = []
        # NL-to-formal-logic translations (#173)
        self.nl_to_logic_translations: List[Dict[str, Any]] = []
        # ATMS multi-context analysis (#349)
        self.atms_contexts: List[Dict[str, Any]] = []
        # Workflow execution results
        self.workflow_results: Dict[str, Any] = {}
        # Narrative synthesis (#351)
        self.narrative_synthesis: str = ""
        # Restitution Acte II — dialectical narrative by argumentative movement
        # (Epic #1134 / R3 #1137). LLM-conducted, woven per spec §4. Consumed by
        # the R6 renderer to populate RestitutionActs.act2_narrative. Empty until
        # the act2_narrative phase runs; the renderer reports the gap honestly.
        self.act2_narrative: str = ""
        # Restitution Acte I — mise en situation (framing): genre, enjeux,
        # spectre attendu (derived from taxonomy common_contexts), game-theoretic
        # read. Epic #1134 / R2 #1136. LLM-conducted, produced BEFORE the
        # microscope (the only act that may anticipate, spec §1.1). Consumed by
        # the R6 renderer to populate RestitutionActs.act1_framing. Empty until
        # the act1_framing phase runs; the renderer reports the gap honestly.
        self.act1_framing: str = ""
        # Restitution Acte III — actionable conclusion: gated verdict + balanced
        # appréciations + que-faire (contrer / points faibles à viser / what-next
        # game-theoretic). Epic #1134 / R4 #1138. LLM-conducted, gated on G1–G4
        # (#1008 §3) + the verdict band (coverage-adapted from #1008 §2).
        # Consumed by the R6 renderer to populate RestitutionActs.act3_conclusion.
        # Empty until the act3_conclusion phase runs; the renderer reports the gap
        # honestly.
        self.act3_conclusion: str = ""
        # #1914 — the interpretive question Acte I closes on (extracted from
        # the narrative's marker line). Written by the act1 lanes, READ by
        # build_act3_evidence so the conclusion's response beat answers the
        # question the framing actually posed. Empty when Acte I posed none
        # (no LLM / no marker line) — honest absence, never fabricated.
        self.interpretive_question: str = ""
        # #1608 — per-act degradation motifs (the *why* an act ran degraded:
        # readability-gate band, virtuous-mode shift, etc.). The acts return
        # ``degraded`` as a dict of motifs (``ActNResult.degraded``); the act
        # invokers surface it as ``output["degraded_reasons"]`` and the act
        # state writers persist it here, keyed by capability. Surfacing the
        # motifs in the state (rather than letting them die in the return
        # value) lets the renderer attribute a degraded act to its true cause
        # — fail-loud, not fail-hard (#1019). Anti-pendule: only populated
        # when an act genuinely recorded motifs; an act that succeeded stays
        # empty (never marked degraded by default).
        self.restitution_acts_degraded: Dict[str, Dict[str, str]] = {}
        # PP #715: source-level metadata for qualitative synthesis
        self.source_metadata: Dict[str, str] = {}
        # Epic #1258 / Track 1 #1259 — déanonymisation du pipeline de travail.
        # True (default for CLI/local) = the working state carries REAL source
        # metadata (speaker, arena, stakes); prompt builders DROP the opaque-ID
        # directives so the readable restitution names the real speaker/arena.
        # False restores the opaque-ID discipline verbatim (the git/dashboard/API
        # export paths run opaque; the export BOUNDARY guard is Track 3
        # sanitize_state, NOT this flag). Threaded via state because the build_*
        # prompt builders cannot see ``context`` (#1259).
        self.deanonymized: bool = True
        # PL 2-pass pipeline: shared atom inventory (#547)
        self.atomic_propositions: Dict[str, List[str]] = {}
        # FOL 2-pass pipeline: shared signature per source (#544)
        self.fol_shared_signature: Dict[str, Dict[str, Any]] = {}
        # Track TT #723: stakes & stakeholders extraction
        self.stakes_and_stakeholders: Dict[str, Any] = {
            "stakes": [],
            "stakeholders": [],
            "rhetorical_register": "",
            "discursive_arena": "",
        }
        # Track UU #724: specialist commentary + analysis trace
        self.analysis_trace: List[Dict[str, Any]] = []
        # AI Shield results — adversarial protection (#841)
        self.ai_shield_results: List[Dict[str, Any]] = []
        # Local LLM results — offline LLM analysis (#834)
        self.local_llm_results: List[Dict[str, Any]] = []
        # RA-4 #1049: Strategic NL journaling bridge
        self.strategic_objectives: List[Dict[str, Any]] = []
        self.strategic_decisions_log: List[Dict[str, Any]] = []
        # CONV-C #1334: deliberation trace of the conversational PM. Each
        # DesignationRecord (agent designated + motivation + trigger + state
        # fingerprint before/after + delta) is the shared material of (1) the
        # CONV-A/C metrics (non-round-robin conduction), (2) the #708 anti-
        # runaway audit, (3) CONV-D Act II. Appended by record_designation();
        # the PM writes a record BEFORE designating (fingerprint_before), and
        # the conversational _run_phase backfills fingerprint_after/delta when
        # the designated agent returns. Stored as plain dicts (via asdict) so
        # the trace serializes with the rest of __dict__ (to_json); the
        # DesignationRecord dataclass is the typed constructor. One spine, no
        # second state object.
        self.deliberation_trace: List[Dict[str, Any]] = []

    def add_trace_entry(
        self,
        phase: str,
        agent: str,
        reacts_to: List[str],
        summary: str,
        anchor: Optional[Dict[str, int]] = None,
        move: Optional[str] = None,
    ) -> None:
        """Record a specialist commentary entry (Track UU #724).

        #2295 — optional ``anchor``/``move`` carry the argumentative sequence:
        ``anchor`` is ``{"offset": int, "length": int}`` in the source text
        (same shape spirit as the #1737 reading-window primitive; the entry
        speaks FROM a measured span, never a fabricated offset 0), and
        ``move`` is one of ``TRACE_MOVE_VOCABULARY``. Both absent on legacy
        entries — the 17 existing writers are untouched.
        """
        summary = summary[:280]
        import time as _time

        if move is not None and move not in self.TRACE_MOVE_VOCABULARY:
            raise ValueError(
                f"add_trace_entry: move '{move}' hors vocabulaire fermé "
                f"{self.TRACE_MOVE_VOCABULARY} (#2295)"
            )
        if anchor is not None:
            if (
                not isinstance(anchor, dict)
                or not isinstance(anchor.get("offset"), int)
                or not isinstance(anchor.get("length"), int)
                or anchor["offset"] < 0
                # #2315 rebase: a zero-length anchor designates nothing —
                # the span must be non-empty (main accepted >= 0).
                or anchor["length"] <= 0
                or isinstance(anchor.get("offset"), bool)
                or isinstance(anchor.get("length"), bool)
            ):
                raise ValueError(
                    f"add_trace_entry: anchor invalide {anchor!r} — attendu "
                    "{'offset': int >= 0, 'length': int > 0} (#2295)"
                )
        # Dict[str, Any]: the entry mixes str leaves, a List[str] (reacts_to)
        # and the optional int dict (anchor) — the trace container is already
        # List[Dict[str, Any]] (line 611).
        entry: Dict[str, Any] = {
            "phase": phase,
            "agent": agent,
            "reacts_to": reacts_to,
            "summary": summary,
            "timestamp": _time.strftime("%Y-%m-%dT%H:%M:%SZ", _time.gmtime()),
        }
        if anchor is not None:
            entry["anchor"] = {"offset": anchor["offset"], "length": anchor["length"]}
        if move is not None:
            entry["move"] = move
        self.analysis_trace.append(entry)
        state_logger.info(
            f"Trace: [{agent}] ({phase}, reacts_to={reacts_to}) → {summary[:60]}..."
        )

    def add_counter_argument(
        self,
        original_arg: str,
        counter_content: str,
        strategy: str,
        score: float,
        target_arg_id: Optional[str] = None,
        validation: Optional[Dict[str, Any]] = None,
    ) -> str:
        """Add a counter-argument result.

        G6 (#1180): ``validation`` carries the populated ``ValidationResult``
        verdict (is_valid_attack / original_survives / counter_succeeds /
        logical_consistency / formal_representation) so the restitution report
        (Acte II/III) can cite counter-argument *validity*, not just existence.
        Stored only when non-empty (honest — never fabricated).
        """
        ca_id = self._generate_id("ca", self.counter_arguments)
        entry = {
            "id": ca_id,
            "original_argument": original_arg,
            "counter_content": counter_content,
            "strategy": strategy,
            "score": score,
        }
        if target_arg_id:
            entry["target_arg_id"] = target_arg_id
        if validation:
            entry["validation"] = validation
        self.counter_arguments.append(entry)
        state_logger.info(f"Counter-argument added: {ca_id} (strategy: {strategy})")
        return ca_id

    def add_quality_score(
        self,
        arg_id: str,
        scores: Dict[str, float],
        overall: float,
        llm_assessment: Optional[str] = None,
        resolved_arg_id: Optional[str] = None,
    ) -> None:
        """Add quality evaluation scores for an argument.

        Args:
            arg_id: Argument identifier (from LLM or pipeline).
            scores: Per-virtue scores dict.
            overall: Sum of the per-virtue [0, 1] scores over the EVALUATED
                virtues (#1942) — not a 0-1 average and not a note sur 10;
                readers normalize by dividing by ``len(scores)``.
            llm_assessment: Optional LLM-generated qualitative narrative (#290).
            resolved_arg_id: If provided, store under this canonical arg_id instead.
        """
        store_id = resolved_arg_id if resolved_arg_id else arg_id
        entry: Dict[str, Any] = {
            "scores": scores,
            "overall": overall,
        }
        if llm_assessment:
            entry["llm_assessment"] = llm_assessment
        self.argument_quality_scores[store_id] = entry
        state_logger.info(f"Quality score added for {store_id}: {overall:.2f}")

    def add_jtms_belief(
        self, name: str, valid: Optional[bool], justifications: List[str]
    ) -> str:
        """Add a JTMS belief to the network."""
        belief_id = self._generate_id("jtms", self.jtms_beliefs)
        self.jtms_beliefs[belief_id] = {
            "name": name,
            "valid": valid,
            "justifications": justifications,
        }
        state_logger.info(f"JTMS belief added: {belief_id} ({name}, valid={valid})")
        return belief_id

    def add_dung_framework(
        self,
        name: str,
        arguments: List[str],
        attacks: List[List[str]],
        extensions: Optional[Dict[str, List[str]]] = None,
    ) -> str:
        """Add a Dung argumentation framework."""
        df_id = self._generate_id("dung", self.dung_frameworks)
        self.dung_frameworks[df_id] = {
            "name": name,
            "arguments": arguments,
            "attacks": attacks,
            "extensions": extensions or {},
        }
        state_logger.info(
            f"Dung framework added: {df_id} ({len(arguments)} args, {len(attacks)} attacks)"
        )
        return df_id

    def add_governance_decision(
        self,
        method: str,
        winner: str,
        scores: Dict[str, float],
        extraction_method: Optional[str] = None,
    ) -> str:
        """Add a governance voting decision.

        Track E #1281 — ``extraction_method`` carries the honest origin signal
        (``"llm"`` | ``"heuristic"`` | ``None``) so the restitution can frame
        the verdict correctly: an LLM-produced assessment is NOT a genuine
        multi-agent deliberation, and must not be dressed as procedural
        legitimacy. ``None`` preserves backward compat for callers that don't
        supply it (the restitution then falls back to its prior framing).
        """
        gd_id = self._generate_id("gov", self.governance_decisions)
        entry = {
            "id": gd_id,
            "method": method,
            "winner": winner,
            "scores": scores,
        }
        if extraction_method:
            entry["extraction_method"] = extraction_method
        self.governance_decisions.append(entry)
        state_logger.info(f"Governance decision added: {gd_id} ({method}: {winner})")
        return gd_id

    def add_debate_transcript(
        self, topic: str, exchanges: List[Dict[str, str]], winner: Optional[str] = None
    ) -> str:
        """Add a debate transcript."""
        dt_id = self._generate_id("debate", self.debate_transcripts)
        entry = {
            "id": dt_id,
            "topic": topic,
            "exchanges": exchanges,
            "winner": winner,
        }
        self.debate_transcripts.append(entry)
        state_logger.info(f"Debate transcript added: {dt_id} (topic: {topic[:50]})")
        return dt_id

    def add_neural_fallacy_score(
        self,
        text_segment: str,
        label: str,
        confidence: float,
        detector: str = "camembert",
    ) -> str:
        """Add a neural fallacy detection score."""
        nf_id = self._generate_id("nf", self.neural_fallacy_scores)
        entry = {
            "id": nf_id,
            "text_segment": text_segment,
            "label": label,
            "confidence": confidence,
            "detector": detector,
        }
        self.neural_fallacy_scores.append(entry)
        state_logger.info(
            f"Neural fallacy score added: {nf_id} ({label}: {confidence:.2f})"
        )
        return nf_id

    def add_transcription_segment(
        self,
        start_time: float,
        end_time: float,
        text: str,
        speaker: Optional[str] = None,
    ) -> str:
        """Add a speech transcription segment."""
        ts_id = self._generate_id("ts", self.transcription_segments)
        entry = {
            "id": ts_id,
            "start_time": start_time,
            "end_time": end_time,
            "text": text,
            "speaker": speaker,
        }
        self.transcription_segments.append(entry)
        state_logger.info(
            f"Transcription segment added: {ts_id} ({start_time:.1f}s-{end_time:.1f}s)"
        )
        return ts_id

    def add_semantic_index_ref(
        self,
        query: str,
        document_id: str,
        score: float,
        snippet: Optional[str] = None,
    ) -> str:
        """Add a semantic index search reference."""
        si_id = self._generate_id("si", self.semantic_index_refs)
        entry = {
            "id": si_id,
            "query": query,
            "document_id": document_id,
            "score": score,
            "snippet": snippet,
        }
        self.semantic_index_refs.append(entry)
        state_logger.info(
            f"Semantic index ref added: {si_id} (doc: {document_id}, score: {score:.2f})"
        )
        return si_id

    def add_ranking_result(
        self, method: str, arguments: List[str], comparisons: List[Dict[str, Any]]
    ) -> str:
        """Add a ranking semantics result."""
        rk_id = self._generate_id("rank", self.ranking_results)
        entry = {
            "id": rk_id,
            "method": method,
            "arguments": arguments,
            "comparisons": comparisons,
        }
        self.ranking_results.append(entry)
        state_logger.info(f"Ranking result added: {rk_id} (method: {method})")
        return rk_id

    def add_aspic_result(
        self,
        reasoner_type: str,
        extensions: List[Any],
        statistics: Dict[str, Any],
        attacks: Optional[List[Dict[str, Any]]] = None,
    ) -> str:
        """Add an ASPIC+ analysis result.

        #1649 (#1678 #1679): ``attacks`` carries the qualified attack list
        produced by ``ASPICHandler.analyze_aspic_framework`` — a list of dicts
        shaped ``{attacker_rule, attacker_premises, target, scope}`` with
        ``scope`` in ``{undercut, rebut, undermine, unresolved}``. The field
        is the singular contribution of ASPIC+ (#1649): without it the
        projection is a Dung copy and the axis loses its only reason to
        exist. ``attacks`` defaults to ``None`` so all 3-arg callers
        (SK plugin wrappers, tests, fixtures) stay backward compatible;
        ``None`` is serialized as the empty list so readers never see the
        distinction. The Semantic Kernel plugin wrappers
        (``state_manager_plugin.py``, ``phase_scoped_state.py``) keep the
        3-arg signature by design — the LLM does not write attacks, the
        writer does, post-handler.
        """
        as_id = self._generate_id("aspic", self.aspic_results)
        entry = {
            "id": as_id,
            "reasoner_type": reasoner_type,
            "extensions": extensions,
            "statistics": statistics,
            "attacks": list(attacks) if attacks is not None else [],
        }
        self.aspic_results.append(entry)
        state_logger.info(f"ASPIC+ result added: {as_id} (reasoner: {reasoner_type})")
        return as_id

    def add_belief_revision_result(
        self,
        method: str,
        original: List[str],
        revised: List[str],
        minimal_retraction: Optional[Dict[str, Any]] = None,
    ) -> str:
        """Add a belief revision result.

        ``minimal_retraction`` (#1646) carries the axis's singular structural
        insight — the smallest set of beliefs whose removal restores consistency
        (a minimum correction subset), as ``{cardinality, options, ...}``. It is
        computed JVM-free by ``_invoke_belief_revision`` (mirroring the bipolar
        insight wiring, #1645), so it is populated even on the honest-degraded
        path. ``None`` means "not computed" (callers that pre-date the insight,
        or an honest degrade of the insight itself); the reader names it only when
        the cardinality is >= 1.
        """
        br_id = self._generate_id("brevision", self.belief_revision_results)
        entry: Dict[str, Any] = {
            "id": br_id,
            "method": method,
            "original": original,
            "revised": revised,
        }
        if minimal_retraction is not None:
            entry["minimal_retraction"] = minimal_retraction
        self.belief_revision_results.append(entry)
        state_logger.info(f"Belief revision result added: {br_id} (method: {method})")
        return br_id

    def add_dialogue_result(
        self, topic: str, outcome: str, trace: List[Dict[str, Any]]
    ) -> str:
        """Add a dialogue protocol result."""
        dl_id = self._generate_id("dialogue", self.dialogue_results)
        entry = {
            "id": dl_id,
            "topic": topic,
            "outcome": outcome,
            "trace": trace,
        }
        self.dialogue_results.append(entry)
        state_logger.info(
            f"Dialogue result added: {dl_id} (topic: {topic[:50]}, outcome: {outcome})"
        )
        return dl_id

    def add_probabilistic_result(
        self, arguments: List[str], acceptance_probs: Dict[str, float]
    ) -> str:
        """Add a probabilistic argumentation result."""
        pr_id = self._generate_id("prob", self.probabilistic_results)
        entry = {
            "id": pr_id,
            "arguments": arguments,
            "acceptance_probabilities": acceptance_probs,
        }
        self.probabilistic_results.append(entry)
        state_logger.info(
            f"Probabilistic result added: {pr_id} ({len(arguments)} args)"
        )
        return pr_id

    def add_bipolar_result(
        self,
        framework_type: str,
        arguments: List[str],
        supports: List[List[str]],
        support_cycles: Optional[List[List[str]]] = None,
        articulation_points: Optional[List[Dict[str, Any]]] = None,
    ) -> str:
        """Add a bipolar argumentation framework result.

        ``support_cycles`` (#1645) carries the axis's distinctive structural
        insight — groups of arguments locked in a mutual-support cycle (circular
        authority). ``articulation_points`` (#1645 PR2) carries the second
        insight — arguments that are the sole support of at least one other.
        Both are computed JVM-free over the ``supports`` edges, so they are
        populated even on the honest-degraded path. Default to empty lists so
        callers that pre-date the insight store an honest "none detected".
        """
        bp_id = self._generate_id("bipolar", self.bipolar_results)
        entry = {
            "id": bp_id,
            "framework_type": framework_type,
            "arguments": arguments,
            "supports": supports,
            "support_cycles": support_cycles or [],
            "articulation_points": articulation_points or [],
        }
        self.bipolar_results.append(entry)
        state_logger.info(f"Bipolar result added: {bp_id} (type: {framework_type})")
        return bp_id

    def add_fol_analysis_result(
        self,
        formulas: List[str],
        consistent: bool,
        inferences: List[str],
        confidence: float = 0.0,
        arg_id: Optional[str] = None,
        message: Optional[str] = None,
    ) -> str:
        """Add a first-order logic analysis result.

        #1278 (Track B): ``message`` is an optional provenance field (mirrors the
        PL sibling's ``message``). It carries the honest status — e.g.
        ``unavailable:no-translation`` / ``unavailable:parse-fail`` — so downstream
        consumers (restitution, measurement matrix) can confirm the entry is a
        real solver decision OR an explicit degradation, never a silent
        "trivially consistent sur vide" (#1019).
        """
        fol_id = self._generate_id("fol", self.fol_analysis_results)
        entry = {
            "id": fol_id,
            "formulas": formulas,
            "consistent": consistent,
            "inferences": inferences,
            "confidence": confidence,
        }
        if arg_id:
            entry["arg_id"] = arg_id
        if message:
            entry["message"] = message
        self.fol_analysis_results.append(entry)
        state_logger.info(f"FOL analysis added: {fol_id} (consistent={consistent})")
        return fol_id

    def add_propositional_analysis_result(
        self,
        formulas: List[str],
        satisfiable: bool,
        model: Optional[Dict[str, bool]] = None,
        arg_id: Optional[str] = None,
        axiom_count: Optional[int] = None,
        query_count: Optional[int] = None,
        message: Optional[str] = None,
    ) -> str:
        """Add a propositional logic analysis result.

        #1208 (FP-10): the real PySAT verdict (satisfiable + genuine model)
        is persisted here. ``axiom_count``/``query_count``/``message`` are
        optional provenance fields so downstream consumers (restitution, the
        measurement matrix) can confirm the entry carries a real solver
        decision, not a hollow counter.
        """
        pl_id = self._generate_id("pl", self.propositional_analysis_results)
        entry: Dict[str, Any] = {
            "id": pl_id,
            "formulas": formulas,
            "satisfiable": satisfiable,
            "model": model or {},
        }
        if arg_id:
            entry["arg_id"] = arg_id
        if axiom_count is not None:
            entry["axiom_count"] = axiom_count
        if query_count is not None:
            entry["query_count"] = query_count
        if message:
            entry["message"] = message
        self.propositional_analysis_results.append(entry)
        state_logger.info(f"PL analysis added: {pl_id} (satisfiable={satisfiable})")
        return pl_id

    def add_modal_analysis_result(
        self,
        formulas: List[str],
        valid: bool,
        modalities: List[str],
        message: Optional[str] = None,
    ) -> str:
        """Add a modal logic analysis result.

        #1279 (Track C): ``message`` is an optional provenance field (mirrors the
        FOL/PL siblings). It carries the honest status — e.g.
        ``unavailable:no-translation`` / ``unavailable:no-solver`` (OOM) — so
        downstream consumers can confirm the entry is a real solver decision OR
        an explicit degradation, never a silent None (#1019).
        """
        ml_id = self._generate_id("modal", self.modal_analysis_results)
        entry = {
            "id": ml_id,
            "formulas": formulas,
            "valid": valid,
            "modalities": modalities,
        }
        if message:
            entry["message"] = message
        self.modal_analysis_results.append(entry)
        state_logger.info(f"Modal analysis added: {ml_id} (valid={valid})")
        return ml_id

    def add_formal_synthesis_report(
        self,
        summary: str,
        phase_results: Dict[str, Any],
        overall_validity: float,
    ) -> str:
        """Add a formal synthesis report aggregating all logic analyses."""
        fs_id = self._generate_id("fsyn", self.formal_synthesis_reports)
        entry = {
            "id": fs_id,
            "summary": summary,
            "phase_results": phase_results,
            "overall_validity": overall_validity,
        }
        self.formal_synthesis_reports.append(entry)
        state_logger.info(
            f"Formal synthesis added: {fs_id} (validity={overall_validity:.2f})"
        )
        return fs_id

    def add_nl_to_logic_translation(
        self,
        original_text: str,
        formula: str,
        logic_type: str,
        is_valid: bool,
        variables: Optional[Dict[str, str]] = None,
        confidence: float = 0.0,
        arg_id: Optional[str] = None,
    ) -> str:
        """Add a NL-to-formal-logic translation result (#173)."""
        tr_id = self._generate_id("nll", self.nl_to_logic_translations)
        entry = {
            "id": tr_id,
            "original_text": original_text[:200],
            "formula": formula,
            "logic_type": logic_type,
            "is_valid": is_valid,
            "variables": variables or {},
            "confidence": confidence,
        }
        if arg_id:
            entry["arg_id"] = arg_id
        self.nl_to_logic_translations.append(entry)
        state_logger.info(
            f"NL→logic translation added: {tr_id} ({logic_type}, valid={is_valid})"
        )
        return tr_id

    def set_workflow_results(self, workflow_name: str, results: Dict[str, Any]) -> None:
        """Store workflow execution results."""
        self.workflow_results[workflow_name] = results
        state_logger.info(f"Workflow results stored for '{workflow_name}'")

    # ---- Cross-referencing query methods (#302) ----

    def get_argument_profile(self, arg_id: str) -> ArgumentProfile:
        """Build an aggregated ArgumentProfile for a single argument.

        Scans fallacies, quality scores, counter-arguments, JTMS beliefs,
        and formal analysis results to gather everything related to *arg_id*.
        """
        description = self.identified_arguments.get(arg_id, "")
        profile = ArgumentProfile(arg_id=arg_id, description=description)

        # Fallacies targeting this argument
        for _fid, fdata in self.identified_fallacies.items():
            if fdata.get("target_argument_id") == arg_id:
                profile.fallacies.append(fdata)

        # Quality score (keyed by arg_id)
        if arg_id in self.argument_quality_scores:
            profile.quality_score = self.argument_quality_scores[arg_id]

        # Counter-arguments — prefer ID-based matching, fall back to text
        arg_desc = description
        for ca in self.counter_arguments:
            if ca.get("target_arg_id") == arg_id:
                profile.counter_arguments.append(ca)
                continue
            if not arg_desc:
                continue
            original = ca.get("original_argument", "")
            match_prefix = arg_desc[:60]
            if original and (
                original == arg_desc
                or original[:60] == match_prefix
                or match_prefix in original
                or original in arg_desc
            ):
                profile.counter_arguments.append(ca)

        # JTMS beliefs referencing this argument (by name containing arg_id or description prefix)
        for _bid, bdata in self.jtms_beliefs.items():
            belief_name = bdata.get("name", "")
            if arg_id in belief_name or (arg_desc and arg_desc[:40] in belief_name):
                profile.jtms_beliefs.append(bdata)

        # Formal results — PL/FOL/NL-to-logic matched by arg_id or text
        for pl in self.propositional_analysis_results:
            if pl.get("arg_id") == arg_id:
                profile.formal_results.append(pl)
        for fol in self.fol_analysis_results:
            if fol.get("arg_id") == arg_id:
                profile.formal_results.append(fol)
        for tr in self.nl_to_logic_translations:
            if tr.get("arg_id") == arg_id:
                profile.formal_results.append(tr)
                continue
            if not arg_desc:
                continue
            orig = tr.get("original_text", "")
            match_prefix = arg_desc[:60]
            if orig and (match_prefix in orig or orig in arg_desc):
                profile.formal_results.append(tr)

        return profile

    def get_weak_arguments(self, threshold: float = 0.5) -> List[ArgumentProfile]:
        """Return ArgumentProfiles whose quality FRACTION is below ``threshold``.

        The fraction is ``overall / len(scores)`` -- the share of the applicable
        maximum that held -- per the single unit contract declared on
        :meth:`add_quality_score` (#1942). ``threshold`` is therefore a fraction
        in [0, 1]: ``0.5`` is the weak bar. It is **not** a note sur 10.

        Arguments carrying no usable quality entry are *unmeasured*, not weak,
        and are never returned: a missing measurement is not a zero (#1019),
        which is also why ``quality_fraction`` returns ``None`` rather than 0.

        Args:
            threshold: Fraction bar in [0, 1]. Defaults to the weak bar 0.5.

        Returns:
            ArgumentProfiles whose measured fraction is strictly below
            ``threshold``, in ``identified_arguments`` order.

        Raises:
            ValueError: if ``threshold`` exceeds 1.0. A share of an attainable
                maximum cannot exceed 1, so such a call was written against the
                pre-#1942 note-sur-10 contract; normalising it silently would
                return *every* scored argument. Fail loud instead (#1951).
        """
        if threshold > 1.0:
            raise ValueError(
                f"get_weak_arguments(threshold={threshold}) is not a fraction: "
                "since #1942 quality 'overall' is the SUM of per-virtue [0, 1] "
                "scores and readers divide by len(scores), so the comparison "
                "scale is [0, 1], not a note sur 10. Divide the pre-#1942 "
                "threshold by 10 (5.0 -> 0.5, the weak bar)."
            )
        weak = []
        for arg_id in self.identified_arguments:
            fraction = quality_fraction(self.argument_quality_scores.get(arg_id))
            if fraction is not None and fraction < threshold:
                weak.append(self.get_argument_profile(arg_id))
        return weak

    def get_fallacious_arguments(self) -> List[ArgumentProfile]:
        """Return ArgumentProfiles for arguments targeted by at least one fallacy."""
        targeted_ids: set[str] = set()
        for _fid, fdata in self.identified_fallacies.items():
            tid = fdata.get("target_argument_id")
            if tid and tid in self.identified_arguments:
                targeted_ids.add(tid)
        return [self.get_argument_profile(aid) for aid in sorted(targeted_ids)]

    def get_enrichment_summary(self) -> Dict[str, Any]:
        """Return a summary of cross-referencing coverage across all arguments."""
        total = len(self.identified_arguments)

        # Collect sets of arg_ids that have each enrichment
        with_fallacy: set[str] = set()
        for _fid, fdata in self.identified_fallacies.items():
            tid = fdata.get("target_argument_id")
            if tid and tid in self.identified_arguments:
                with_fallacy.add(tid)

        with_quality = set(self.argument_quality_scores.keys()) & set(
            self.identified_arguments.keys()
        )

        # Counter-arguments: prefer ID-based matching, fall back to text matching
        with_counter: set[str] = set()
        for ca in self.counter_arguments:
            tid = ca.get("target_arg_id")
            if tid and tid in self.identified_arguments:
                with_counter.add(tid)
                continue
            original = ca.get("original_argument", "")
            if not original:
                continue
            for arg_id, desc in self.identified_arguments.items():
                if arg_id in with_counter or not desc:
                    continue
                match_prefix = desc[:60]
                if (
                    original == desc
                    or original[:60] == match_prefix
                    or match_prefix in original
                    or original in desc
                ):
                    with_counter.add(arg_id)
                    break

        # Formal verification: check PL, FOL, and NL-to-logic translations
        with_formal: set[str] = set()
        # PL results with arg_id
        for pl in self.propositional_analysis_results:
            aid = pl.get("arg_id")
            if aid and aid in self.identified_arguments:
                with_formal.add(aid)
        # FOL results with arg_id
        for fol in self.fol_analysis_results:
            aid = fol.get("arg_id")
            if aid and aid in self.identified_arguments:
                with_formal.add(aid)
        # NL-to-logic translations: prefer arg_id, fall back to text match
        for tr in self.nl_to_logic_translations:
            aid = tr.get("arg_id")
            if aid and aid in self.identified_arguments:
                with_formal.add(aid)
                continue
            orig = tr.get("original_text", "")
            if not orig:
                continue
            for arg_id, desc in self.identified_arguments.items():
                if arg_id in with_formal or not desc:
                    continue
                match_prefix = desc[:60]
                if match_prefix in orig or orig in desc:
                    with_formal.add(arg_id)
                    break

        # JTMS beliefs
        with_jtms: set[str] = set()
        for arg_id, desc in self.identified_arguments.items():
            for _bid, bdata in self.jtms_beliefs.items():
                belief_name = bdata.get("name", "")
                if arg_id in belief_name or (desc and desc[:40] in belief_name):
                    with_jtms.add(arg_id)
                    break

        # Build gaps list
        gaps: List[str] = []
        for arg_id in sorted(self.identified_arguments.keys()):
            if arg_id not in with_quality:
                gaps.append(f"{arg_id} has no quality score")
            if arg_id not in with_formal:
                gaps.append(f"{arg_id} has no formal verification")

        return {
            "total_arguments": total,
            "with_fallacy_analysis": len(with_fallacy),
            "with_quality_score": len(with_quality),
            "with_counter_argument": len(with_counter),
            "with_formal_verification": len(with_formal),
            "with_jtms_belief": len(with_jtms),
            "gaps": gaps,
        }

    def get_state_snapshot(self, summarize: bool = False) -> Dict[str, Any]:
        """Extended snapshot including all unified dimensions."""
        base = super().get_state_snapshot(summarize=summarize)
        if summarize:
            base.update(
                {
                    "counter_argument_count": len(self.counter_arguments),
                    "quality_scores_count": len(self.argument_quality_scores),
                    "jtms_belief_count": len(self.jtms_beliefs),
                    "dung_framework_count": len(self.dung_frameworks),
                    "governance_decision_count": len(self.governance_decisions),
                    "debate_transcript_count": len(self.debate_transcripts),
                    "transcription_segment_count": len(self.transcription_segments),
                    "semantic_index_ref_count": len(self.semantic_index_refs),
                    "neural_fallacy_score_count": len(self.neural_fallacy_scores),
                    "ranking_result_count": len(self.ranking_results),
                    "aspic_result_count": len(self.aspic_results),
                    "belief_revision_result_count": len(self.belief_revision_results),
                    "dialogue_result_count": len(self.dialogue_results),
                    "probabilistic_result_count": len(self.probabilistic_results),
                    "bipolar_result_count": len(self.bipolar_results),
                    # FP-17 (#1236): surface the FULL honest-absent map even in
                    # the summarized snapshot — a count would re-hide the very
                    # distinction (absent_no_translator vs evaluated) this field
                    # exists to expose (#1019). The map is small (≤5 entries).
                    "structured_arg_status": dict(self.structured_arg_status),
                    "fol_analysis_count": len(self.fol_analysis_results),
                    "propositional_analysis_count": len(
                        self.propositional_analysis_results
                    ),
                    # #1208 (FP-10): expose the real PL entries (verdict +
                    # genuine PySAT model + counts) in the summarized snapshot
                    # too, not just the counter. The state IS the contract;
                    # a count alone hides whether the verdict is real or a
                    # fabricated placeholder. This list is already in the
                    # state object — surfacing it subtracts the masking, it
                    # does not add a counterweight.
                    "propositional_analysis_results": list(
                        self.propositional_analysis_results
                    ),
                    "modal_analysis_count": len(self.modal_analysis_results),
                    "formal_synthesis_count": len(self.formal_synthesis_reports),
                    "workflow_results_count": len(self.workflow_results),
                    "atomic_propositions_count": sum(
                        len(v) for v in self.atomic_propositions.values()
                    ),
                    "fol_shared_signature_sources": list(
                        self.fol_shared_signature.keys()
                    ),
                    "strategic_objective_count": len(self.strategic_objectives),
                    "strategic_decision_count": len(self.strategic_decisions_log),
                }
            )
        else:
            base.update(
                {
                    "counter_arguments": self.counter_arguments,
                    "argument_quality_scores": self.argument_quality_scores,
                    "jtms_beliefs": self.jtms_beliefs,
                    "dung_frameworks": self.dung_frameworks,
                    "governance_decisions": self.governance_decisions,
                    "debate_transcripts": self.debate_transcripts,
                    "transcription_segments": self.transcription_segments,
                    "semantic_index_refs": self.semantic_index_refs,
                    "neural_fallacy_scores": self.neural_fallacy_scores,
                    "ranking_results": self.ranking_results,
                    "aspic_results": self.aspic_results,
                    "belief_revision_results": self.belief_revision_results,
                    "dialogue_results": self.dialogue_results,
                    "probabilistic_results": self.probabilistic_results,
                    "bipolar_results": self.bipolar_results,
                    "structured_arg_status": self.structured_arg_status,
                    "fol_analysis_results": self.fol_analysis_results,
                    "propositional_analysis_results": self.propositional_analysis_results,
                    "modal_analysis_results": self.modal_analysis_results,
                    "formal_synthesis_reports": self.formal_synthesis_reports,
                    "workflow_results": self.workflow_results,
                    "atomic_propositions": self.atomic_propositions,
                    "fol_shared_signature": self.fol_shared_signature,
                    "strategic_objectives": self.strategic_objectives,
                    "strategic_decisions_log": self.strategic_decisions_log,
                }
            )
        return base


# Optionnel : Ajouter un log à la fin du fichier pour confirmer le chargement du module
module_logger = logging.getLogger(__name__)
module_logger.debug("Module core.shared_state chargé.")

# Créer un alias SharedState pour maintenir la compatibilité avec le code existant
SharedState = RhetoricalAnalysisState


