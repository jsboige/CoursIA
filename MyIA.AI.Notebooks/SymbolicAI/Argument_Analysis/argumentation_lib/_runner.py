# _runner.py — simplified argumentation analysis runner for CoursIA notebooks
#
# Replaces EPITA's `analysis_runner_v2.py` (which has stale factory calls,
# environment_manager side effects, and config/settings.py dependencies).
#
# This runner:
# - Uses RhetoricalAnalysisState + StateManagerPlugin (vendored)
# - Instantiates agents directly via SK ChatCompletionAgent (bypasses factory)
# - Runs a 3-phase pipeline: Informal → Formal → Synthesis
# - Zero secrets, zero model names, zero env reads
#
# The LLM kernel is INJECTED by the notebook at runtime.

from __future__ import annotations

import json
import logging
import sys
from typing import Any, Dict, List, Optional

from semantic_kernel import Kernel
from semantic_kernel.agents.chat_completion.chat_completion_agent import (
    ChatCompletionAgent,
)
from semantic_kernel.agents.group_chat.agent_group_chat import AgentGroupChat
from semantic_kernel.contents.chat_message_content import ChatMessageContent
from semantic_kernel.contents.utils.author_role import AuthorRole
from semantic_kernel.contents.chat_history import ChatHistory
from semantic_kernel.functions.kernel_arguments import KernelArguments

from argumentation_lib._shared_state import RhetoricalAnalysisState
from argumentation_lib._guarded_state import GuardedStateManagerPlugin
from argumentation_lib._pl_reasoner import PLReasonerPlugin
from argumentation_lib._state_manager_plugin import StateManagerPlugin
from argumentation_lib._llm_settings import apply_reasoning_none_for_function_tools
from argumentation_lib._verdict import (
    count_substantive_arguments,
    count_substantive_fallacies,
    phantom_target_fallacy_ids,
    state_key_argument_ids,
)

_logger = logging.getLogger("argumentation_lib.runner")

# ---------------------------------------------------------------------------
# Prompts — vendored from EPITA agents/core/pm/prompts.py
# ---------------------------------------------------------------------------

PROMPT_DEFINE_TASKS = """[Contexte]
Vous êtes le ProjectManagerAgent, un orchestrateur logique et précis.
Votre unique but est de déterminer la prochaine action dans une analyse
rhétorique, en suivant une séquence stricte.

[Séquence d'Analyse Idéale]
1. Identifier les arguments dans le texte (Agent: InformalAgent)
2. Analyser les sophismes dans le texte (Agent: InformalAgent)
3. Traduire le texte en logique propositionnelle (Agent: LogicAgent)
4. Exécuter des requêtes logiques (Agent: LogicAgent)
5. Rédiger la conclusion (Agent: PM, vous-même)

Règle de routage (elle PRIME sur la séquence idéale) : ne passez à
l'analyse formelle (étapes 3-4) QUE SI l'analyse informelle a déjà détecté
au moins un sophisme dans l'état, OU si le texte contient une inférence
conditionnelle à vérifier (« si ... alors ... »). Si aucun de ces deux
signaux n'est présent, sautez les étapes 3-4 : désignez-vous
(ProjectManagerAgent) et rédigez directement la conclusion. C'est votre
décision de routage : elle dépend du contenu, pas d'une séquence figée.

[État Actuel]
{{$analysis_state}}

[Instructions]
Trouvez la première étape non complétée.
Les tâches d'analyse sont OUVERTES par le runner (champ `tasks_defined`
de l'état) : ne créez PAS de tâche concurrente et n'inventEZ JAMAIS
d'identifiant de tâche — un identifiant inexistant fait PERDRE la réponse
de l'agent (#23726). Votre rôle est le ROUTAGE.
Répondez AU FORMAT JSON:
{
  "task_description": "Description de la tâche",
  "assigned_agent": "InformalAgent|LogicAgent|PM"
}
Puis APPELEZ la fonction kernel `StateManager-designate_next_agent`
avec le nom de l'agent choisi (votre propre nom : "ProjectManagerAgent").
La désignation écrite dans l'état détermine qui parle au prochain tour.
Si toutes les étapes sont complétées, désignez-vous et rédigez la
conclusion finale.
"""

PROMPT_INFORMAL_ANALYSIS = """Vous êtes un agent spécialisé dans l'analyse informelle d'argumentation.

Votre rôle:
1. Identifier les arguments principaux du texte
2. Détecter les sophismes (ad hominem, straw man, appel à l'autorité, etc.)
3. Évaluer la cohérence des arguments

[État Actuel]
{{$analysis_state}}

Répondez en utilisant les fonctions kernel disponibles pour:
- Ajouter les arguments identifiés
- Ajouter les sophismes détectés
- Marquer la tâche comme répondue : appelez
  `StateManager-mark_task_as_answered` avec l'identifiant EXACT de la
  tâche en cours (écrit dans le bloc « Tâche en cours » de vos
  instructions) et un résumé de votre travail. Un identifiant inventé
  est REJETÉ SANS EFFET : votre travail serait alors perdu (#23726).

Contrat d'appel OBLIGATOIRE : pour CHAQUE argument identifié, appelez
`StateManager-add_identified_argument` avec la phrase complète de l'argument
comme description (jamais un nom de champ comme "analysis_state"). Répondre
en prose sans appeler les fonctions kernel = tâche non accomplie.
"""

PROMPT_LOGIC_ANALYSIS = """Vous êtes un agent spécialisé dans l'analyse logique formelle.

Votre rôle:
1. Traduire les arguments en formules logiques propositionnelles
2. Créer des ensembles de croyances (belief sets)
3. Exécuter des requêtes logiques pour vérifier la cohérence

[État Actuel]
{{$analysis_state}}

Répondez en utilisant les fonctions kernel disponibles pour:
- Ajouter des belief sets
- Logger les résultats de requêtes
- Marquer la tâche comme répondue : appelez
  `StateManager-mark_task_as_answered` avec l'identifiant EXACT de la
  tâche en cours (écrit dans le bloc « Tâche en cours » de vos
  instructions) et un résumé de votre travail. Un identifiant inventé
  est REJETÉ SANS EFFET : votre travail serait alors perdu (#23726).

Contrat d'appel OBLIGATOIRE (l'ordre compte) :
1. `StateManager-add_belief_set` (logic_type="propositional") avec le contenu :
   UNE formule propositionnelle par ligne, syntaxe `!` (non), `&&` (et),
   `||` (ou), `=>` (implique), `<=>` (équivalent), parenthèses pour la
   priorité ; les atomes sont des identifiants (lettres, chiffres, `_`).
   Le parseur du solveur REFUSE `->` : écrivez `=>`.
2. `Reasoner-pl_query` (belief_set_id = identifiant renvoyé par
   add_belief_set, query = la formule à vérifier) : c'est le SEUL moyen
   d'obtenir un verdict. Le solveur propositionnel répond
   `ACCEPTED: ...` ou `REJECTED: ...`.
3. `StateManager-log_query_result` (belief_set_id, query, raw_result) avec
   raw_result = la sortie de `Reasoner-pl_query` COPIÉE TELLE QUELLE.
   Tout autre contenu (une question en langage naturel, une reformulation)
   est REFUSÉ par l'outil.

Vous désignez ce qui mérite d'être vérifié ; le solveur décide. Ne jugez
jamais vous-même une formule. Le texte source figure dans la conversation :
encodez directement depuis lui, même si l'état ne recense pas encore
d'arguments. Répondre en prose sans appel kernel = tâche non accomplie.
"""

PROMPT_SYNTHESIS = """Vous êtes l'agent de synthèse.

Votre rôle:
- Synthétiser tous les résultats de l'analyse
- Rédiger une conclusion finale structurée
- Identifier les points forts et faiblesses de l'argumentation

[État Actuel]
{{$analysis_state}}

Rédigez une conclusion finale complète.
"""

# Reprise ciblée de la phase déficitaire (#18776, branche « ou » de la
# demande) : la phase informelle porte deux livrables (arguments, sophismes)
# qui se disputent le même budget de tours. Ces prompts ne portent QU'UN
# livrable chacun — c'est le mécanisme qui sépare le budget des deux phases
# « arguments » et « sophismes » de l'issue.

PROMPT_RESUMPTION_ARGUMENTS = """Vous êtes l'agent de reprise ciblée pour l'identification d'arguments.

Contexte : la phase informelle principale a tourné, mais les arguments
enregistrés dans l'état ne sont pas substantifs — ils ne reprennent pas les
phrases du texte source (intitulés trop courts, clés d'état, ou reformulations
sans recouvrement avec le texte).

Votre unique tâche : identifier les arguments principaux du texte.
N'identifiez PAS de sophismes ici — une autre reprise s'en charge.

[État Actuel]
{{$analysis_state}}

Contrat d'appel OBLIGATOIRE : pour CHAQUE argument identifié, appelez
`StateManager-add_identified_argument` avec comme description une phrase
COMPLÈTE reprise MOT POUR MOT du texte source (jamais un résumé, jamais
une clé d'état, jamais un intitulé court). Un argument valide est une
phrase qui figure dans le texte. Répondre en prose sans appeler la
fonction kernel = tâche non accomplie.
"""

PROMPT_RESUMPTION_FALLACIES = """Vous êtes l'agent de reprise ciblée pour la détection de sophismes.

Contexte : la phase informelle principale a tourné, mais les sophismes
enregistrés dans l'état ne sont pas substantifs — type manquant ou générique,
justification vide, ou cible absente.

Votre unique tâche : détecter les sophismes du texte.
N'identifiez PAS de nouveaux arguments ici — ils sont déjà dans l'état.

[État Actuel]
{{$analysis_state}}

Contrat d'appel OBLIGATOIRE : appelez `StateManager-add_identified_fallacies`
avec une liste de dictionnaires, chacun portant les clés `type` (le nom du
sophisme, ex. « Appel à l'autorité », « Faux dilemme »), `justification`
(pourquoi ce passage précis est un sophisme, au moins une phrase complète)
et `target` (l'identifiant de l'argument visé, ex. « arg_1 »). Répondre en
prose sans appeler la fonction kernel = tâche non accomplie.
"""


# ---------------------------------------------------------------------------
# Contrat tâche / réponse (#23726)
# ---------------------------------------------------------------------------
#
# L'amont EPITA fait créer les tâches par le PM (`add_analysis_task`) et
# clôt par l'agent qui a fait le travail, avec l'identifiant EXACT de la
# tâche. Notre port a une structure de phases DÉTERMINISTE (informel →
# formel → synthèse) : c'est donc le runner qui ouvre la tâche de phase et
# qui en donne l'identifiant exact à l'agent qui la travaille.
#
# Pourquoi c'était un défaut mesuré, pas une préférence de style : sans
# tâche ouverte, `analysis_tasks` restait VIDE, l'agent n'avait aucun
# identifiant à fournir et n'inventait qu'un nom de rôle ; or
# `mark_task_as_answered` REFUSE un identifiant inconnu en silence
# (_shared_state.py : garde `task_id not in self.analysis_tasks` → warning
# + `return`) — la réponse de l'agent était donc PERDUE, sans trace et sans
# erreur rapportée (#23726).

PHASE_TASK_DESCRIPTIONS = {
    "informal": "Identifier les arguments principaux et les sophismes du texte",
    "formal": (
        "Encoder les arguments en logique propositionnelle et consigner les "
        "verdicts du solveur"
    ),
    "conversation": (
        "Analyser rhétoriquement le texte : arguments, sophismes, encodage "
        "formel et conclusion"
    ),
}


def _task_instructions(task_id: str, role: str) -> str:
    """Bloc d'instructions nommant l'identifiant EXACT de la tâche en cours.

    L'identifiant est écrit LITTÉRALEMENT dans les instructions de l'agent :
    la snapshot d'état portée par `{{$analysis_state}}` est figée à la
    construction de l'agent (cf `_state_arguments`), l'agent ne peut donc
    pas y lire une tâche créée pendant la phase.
    """
    return f"""

[Tâche en cours — identifiant exact : {task_id}]
Vous TRAVAILLEZ sur la tâche `{task_id}` ({role}).
À la fin de votre travail, appelez la fonction kernel
`StateManager-mark_task_as_answered` avec cet identifiant EXACT
(`task_id="{task_id}"`) et un résumé de votre travail.
Tout autre identifiant (nom de rôle, « task », identifiant inventé) est
REJETÉ SANS EFFET : votre travail serait alors perdu (#23726).
"""


# ---------------------------------------------------------------------------
# Agent builders — direct instantiation, no factory needed
# ---------------------------------------------------------------------------


def _iteration_cap(max_iterations: int):
    """Stratégie de terminaison explicite portant le budget d'une phase.

    Sans elle, ``AgentGroupChat`` tourne sous ``DefaultTerminationStrategy``
    dont ``maximum_iterations`` vaut **5** par défaut : chaque phase affichait
    un plafond de 10-15 tours mais s'arrêtait systématiquement à 5 — les
    budgets ``max_informal_turns`` / ``max_formal_turns`` (#18785) n'avaient
    aucune prise mécanique (mesure #18776 : 20/20 runs réels arrêtés à
    5 tours par phase sous des plafonds de 10 et 15). Passer la stratégie
    explicite est ce qui rend ces budgets réels.

    Le repli sans stratégie est réservé au stub de test déclaré
    (``semantic_kernel._coursia_mock``, posé par ``tests/test_runner.py``),
    même discipline que ``create_logic_agent`` : hors de ce cas,
    l'``ImportError`` est propagée — une installation SK cassée ne doit pas
    produire un run au plafond silencieusement écrasé.
    """
    try:
        from semantic_kernel.agents.strategies.termination.default_termination_strategy import (
            DefaultTerminationStrategy,
        )

        return DefaultTerminationStrategy(maximum_iterations=max_iterations)
    except ImportError:
        sk_module = sys.modules.get("semantic_kernel")
        if not getattr(sk_module, "_coursia_mock", False):
            raise
        return None


def _resolve_service(kernel: Kernel, llm_service_id: str):
    """Return the chat-completion service registered under ``llm_service_id``.

    Semantic Kernel >= 1.30 dropped the ``service_id=`` keyword of
    ``ChatCompletionAgent`` (renamed ``service=``, expecting an instance) —
    the vendored builder was pinned to SK 1.x ≤ 1.29 and never exercised
    until this repair. Resolve the instance the Executor registered as
    ``global_llm_service``.
    """
    return kernel.get_service(llm_service_id)


def _state_arguments(
    state: RhetoricalAnalysisState,
    execution_settings: Optional[Dict[str, Any]] = None,
) -> KernelArguments:
    """Render the state snapshot for the prompts' ``{{$analysis_state}}`` token.

    ``AgentGroupChat.invoke`` (SK 1.44) ne transporte pas de KernelArguments :
    le token des prompts vendangés restait non résolu. Les agents portent la
    snapshot à leur construction (état de début de phase).

    ``execution_settings`` (#20135) : sans elles, ``AIServiceSelector`` fabrique
    des réglages par défaut (``reasoning_effort`` absent) et la famille 5.6
    refuse les outils de fonction sur ``/v1/chat/completions`` (400).
    """
    return KernelArguments(
        settings=execution_settings,
        analysis_state=json.dumps(
            state.get_state_snapshot(summarize=True), ensure_ascii=False
        ),
    )


def _execution_settings_for(kernel: Kernel, llm_service_id: str) -> Dict[str, Any]:
    """Réglages d'exécution des agents, indexés par identifiant de service.

    Le helper partagé force ``reasoning_effort="none"`` pour les modèles qui
    l'exigent (famille 5.6) et laisse les autres inchangés. Un service qui
    n'expose pas ``get_prompt_execution_settings_class`` (doublon de test,
    service hors connecteur SK) ne reçoit aucun réglage explicite : les agents
    retombent alors sur les réglages par défaut, comme avant ce helper.
    """
    service = _resolve_service(kernel, llm_service_id)
    factory = getattr(service, "get_prompt_execution_settings_class", None)
    if factory is None:
        return {}
    # get_prompt_execution_settings_class rend la CLASSE, pas une instance :
    # le second appel construit l'instance attendue par from_prompt_execution_settings.
    settings = factory()()
    return {
        llm_service_id: apply_reasoning_none_for_function_tools(
            settings, getattr(service, "ai_model_id", None)
        )
    }


def _state_manager_plugin(state: RhetoricalAnalysisState) -> StateManagerPlugin:
    """Plugin d'état de l'analyse — version GARDEE (#22981).

    `StateManagerPlugin` est une copie verbatim de l'amont EPITA : on
    l'étend au lieu de la modifier. La sous-classe garde change une seule
    chose : `log_query_result` n'accepte plus que les verdicts RÉELLEMENT
    émis par le solveur (`PLReasonerPlugin`). Le registre des verdicts est
    propre à l'état (`registry_for`), donc le plugin d'état et le solveur
    partagent le même registre sans paramétrage supplémentaire.
    """
    return GuardedStateManagerPlugin(state)


def _ensure_reasoner_plugin(kernel: Kernel, state: RhetoricalAnalysisState) -> None:
    """Expose le solveur propositionnel aux agents (plugin `Reasoner`).

    Sans ce plugin, aucun outil ne produit de verdict : l'agent ne pouvait
    que consigner une question en langage naturel, que le carnet rejette
    ensuite (`QUERIES_NOT_MEANINGFUL`, #22981).
    """
    if "Reasoner" in [p.name for p in kernel.plugins.values()]:
        return
    kernel.add_plugin(PLReasonerPlugin(state), plugin_name="Reasoner")


def create_pm_agent(
    kernel: Kernel,
    llm_service_id: str,
    state: RhetoricalAnalysisState,
) -> ChatCompletionAgent:
    """Create the Project Manager agent."""
    smp = _state_manager_plugin(state)
    kernel.add_plugin(smp, plugin_name="StateManager")

    agent = ChatCompletionAgent(
        kernel=kernel,
        name="ProjectManagerAgent",
        instructions=PROMPT_DEFINE_TASKS,
        service=_resolve_service(kernel, llm_service_id),
        arguments=_state_arguments(
            state, _execution_settings_for(kernel, llm_service_id)
        ),
    )
    _logger.info("PM agent created with StateManagerPlugin.")
    return agent


def create_informal_agent(
    kernel: Kernel,
    llm_service_id: str,
    state: RhetoricalAnalysisState,
    task_id: Optional[str] = None,
) -> ChatCompletionAgent:
    """Create the Informal Analysis agent.

    ``task_id`` (#23726) : identifiant EXACT de la tâche de phase que l'agent
    doit clôturer. Absent (appel hors runner), les instructions restent celles
    du prompt vendangé — le contrat historique est préservé.
    """
    # StateManagerPlugin already added by PM — reuse it
    if "StateManager" not in [p.name for p in kernel.plugins.values()]:
        smp = _state_manager_plugin(state)
        kernel.add_plugin(smp, plugin_name="StateManager")

    instructions = PROMPT_INFORMAL_ANALYSIS
    if task_id:
        instructions += _task_instructions(task_id, "analyse informelle")

    agent = ChatCompletionAgent(
        kernel=kernel,
        name="InformalAgent",
        instructions=instructions,
        service=_resolve_service(kernel, llm_service_id),
        arguments=_state_arguments(
            state, _execution_settings_for(kernel, llm_service_id)
        ),
    )
    _logger.info("Informal agent created.")
    return agent


def create_logic_agent(
    kernel: Kernel,
    llm_service_id: str,
    state: RhetoricalAnalysisState,
    task_id: Optional[str] = None,
) -> ChatCompletionAgent:
    """Create the Logic Analysis agent.

    ``FunctionChoiceBehavior.Required`` force l'emission d'un appel d'outil :
    sans lui, le modele mesure repond en prose sans jamais tenter
    ``add_belief_set`` -- meme avec un contrat d'appel explicite dans le
    prompt (issue #18395, diagnostic instrumente : commentaire 6305563691 ;
    le relais honore ``required`` de facon non deterministe run a run).

    Le repli sans ``function_choice_behavior`` est **reserve au stub de test**,
    qui se declare explicitement par ``semantic_kernel._coursia_mock`` (pose
    par ``tests/test_runner.py``). Hors de ce cas, l'``ImportError`` est
    propagee : une installation de ``semantic_kernel`` cassee ou incompatible
    perdrait sinon *silencieusement* le levier decisif, et le carnet
    produirait un run degrade d'apparence normale (revue ai-01 du 21/10,
    head ``0e020ac12c``).
    """
    try:
        from semantic_kernel.connectors.ai.function_choice_behavior import (
            FunctionChoiceBehavior,
        )

        fcb = FunctionChoiceBehavior.Required(auto_invoke=True)
    except ImportError:
        # Aucun second import ici : `sys.modules` porte deja le paquet en
        # cours d'evaluation. Absent (paquet reellement introuvable) =>
        # getattr(None, ...) vaut False => propagation, comportement voulu.
        sk_module = sys.modules.get("semantic_kernel")
        if not getattr(sk_module, "_coursia_mock", False):
            raise
        fcb = None

    if "StateManager" not in [p.name for p in kernel.plugins.values()]:
        smp = _state_manager_plugin(state)
        kernel.add_plugin(smp, plugin_name="StateManager")

    # Le solveur propositionnel doit etre exposed AVANT la creation de
    # l'agent : l'agent doit pouvoir DECOUVRIR l'outil `Reasoner-pl_query`
    # dans la liste de ses fonctions (#22981).
    _ensure_reasoner_plugin(kernel, state)

    logic_instructions = PROMPT_LOGIC_ANALYSIS
    if task_id:
        logic_instructions += _task_instructions(task_id, "analyse formelle")

    agent_kwargs = dict(
        kernel=kernel,
        name="LogicAgent",
        instructions=logic_instructions,
        service=_resolve_service(kernel, llm_service_id),
        arguments=_state_arguments(
            state, _execution_settings_for(kernel, llm_service_id)
        ),
    )
    if fcb is not None:
        agent_kwargs["function_choice_behavior"] = fcb
    agent = ChatCompletionAgent(**agent_kwargs)
    _logger.info("Logic agent created.")
    return agent


# ---------------------------------------------------------------------------
# Pipeline runner
# ---------------------------------------------------------------------------

class AnalysisRunner:
    """Simplified 3-phase argumentation analysis runner.

    Phases:
        1. Informal: identify arguments and fallacies
        2. Formal: translate to logic, run queries
        3. Synthesis: write conclusion

    Usage in notebooks::

        from argumentation_lib import AnalysisRunner, RhetoricalAnalysisState

        state = RhetoricalAnalysisState(text)
        runner = AnalysisRunner(kernel, "my-llm-service", state)
        result = await runner.run()
    """

    def __init__(
        self,
        kernel: Kernel,
        llm_service_id: str,
        state: RhetoricalAnalysisState,
        max_turns: int = 20,
        max_informal_turns: int | None = None,
        max_formal_turns: int | None = None,
        targeted_resumption: bool = False,
        max_resumption_argument_turns: int = 4,
        max_resumption_fallacy_turns: int = 4,
        resumption_max_rounds: int = 2,
        min_substantive_arguments: int = 2,
        min_substantive_fallacies: int = 2,
    ):
        self.kernel = kernel
        self.llm_service_id = llm_service_id
        self.state = state
        self.max_turns = max_turns
        # Per-phase budget (#18776) : when None, fall back to max_turns // 2
        # (legacy behaviour, preserves existing tests/contracts).
        self.max_informal_turns = (
            max_informal_turns if max_informal_turns is not None
            else max_turns // 2
        )
        self.max_formal_turns = (
            max_formal_turns if max_formal_turns is not None
            else max_turns // 2
        )
        # Reprise ciblée de la phase déficitaire (#18776, branche « ou »).
        # Désactivée par défaut : le comportement historique (3 phases,
        # rien entre elles) reste celui des appelants qui n'optent pas.
        # Les seuils de substance sont évalués par les prédicats de
        # ``_verdict`` (source unique, mêmes seuils que le carnet et la
        # mesure) — le runner ne redéfinit pas ce qu'est un argument
        # substantif.
        self.targeted_resumption = targeted_resumption
        self.max_resumption_argument_turns = max_resumption_argument_turns
        self.max_resumption_fallacy_turns = max_resumption_fallacy_turns
        self.resumption_max_rounds = resumption_max_rounds
        self.min_substantive_arguments = min_substantive_arguments
        self.min_substantive_fallacies = min_substantive_fallacies

        # Register StateManagerPlugin on kernel
        if "StateManager" not in [p.name for p in kernel.plugins.values()]:
            self._smp = _state_manager_plugin(state)
            kernel.add_plugin(self._smp, plugin_name="StateManager")
        else:
            self._smp = None

        # Le solveur propositionnel est expose des la construction du runner :
        # c'est le SEUL chemin d'obtention d'un verdict de moteur (#22981).
        _ensure_reasoner_plugin(kernel, state)

    # ------------------------------------------------------------------
    # Contrat tâche / réponse (#23726)
    # ------------------------------------------------------------------
    def _open_phase_task(self, phase: str) -> str:
        """Ouvre la tâche de la phase et retourne son identifiant (#23726).

        La tâche est créée par le runner, pas par le PM : la structure de
        phases de ce port est déterministe, et une tâche créée par le LLM
        n'offre aucune garantie d'identifiant exploitable par l'agent qui
        doit la clôturer.
        """
        description = PHASE_TASK_DESCRIPTIONS[phase]
        task_id = self.state.add_task(description)
        _logger.info(f"Tâche de phase ouverte ({phase}) : {task_id}")
        return task_id

    def _close_phase_task(self, phase: str, task_id: str, agent_name: str) -> bool:
        """Vérifie la clôture de la tâche ; une non-clôture est ENREGISTRÉE.

        Le contrat veut qu'une réponse d'agent soit attachée à une tâche.
        Sans vérification, une non-clôture est INDÉTECTABLE : le travail de
        la phase disparaît sans trace — c'est exactement le mode de panne
        que #23726 documente. La non-clôture est donc consignée dans
        `state.errors` (visible dans l'état, donc dans le rapport), jamais
        absorbée en silence.
        """
        if task_id in self.state.answers:
            return True
        message = (
            f"Tâche {task_id} ({phase}) non close : l'agent n'a pas appelé "
            "mark_task_as_answered avec cet identifiant, son travail n'est "
            "rattaché à aucune réponse."
        )
        _logger.warning(message)
        self.state.log_error(agent_name, message)
        return False

    async def run(self) -> Dict[str, Any]:
        """Execute the full 3-phase analysis pipeline."""
        _logger.info("Starting 3-phase argumentation analysis...")
        _logger.info(f"  Text length: {len(self.state.raw_text)} chars")
        _logger.info(f"  Max turns: {self.max_turns}")

        results = {
            "phases": [],
            "state_snapshot": None,
            "conclusion": None,
        }

        # Phase 1: Informal analysis
        _logger.info("=== Phase 1: Informal Analysis ===")
        informal_task_id = self._open_phase_task("informal")
        informal = create_informal_agent(
            self.kernel, self.llm_service_id, self.state, task_id=informal_task_id
        )
        pm = create_pm_agent(self.kernel, self.llm_service_id, self.state)

        phase1_history = ChatHistory()
        phase1_history.add_message(
            ChatMessageContent(
                role=AuthorRole.USER,
                content=f"Analysez le texte suivant:\\n\\n{self.state.raw_text}",
            )
        )

        # SK 1.44 : ChatHistoryChannel.invoke lit messages[-1] et lève
        # IndexError sur un canal vide — chaque phase doit amorcer une
        # history USER (le texte à analyser), sinon aucune n'a lieu.
        # La stratégie de terminaison explicite porte le budget de la
        # phase (#18776) : sans elle, le défaut SK (5 itérations) écrase
        # silencieusement max_informal_turns.
        group_chat = AgentGroupChat(
            agents=[pm, informal],
            chat_history=phase1_history,
            termination_strategy=_iteration_cap(self.max_informal_turns),
        )

        try:
            turn_count = 0
            async for response in group_chat.invoke():
                turn_count += 1
                _logger.info(f"  Turn {turn_count}: {response.name} responded")
                if turn_count >= self.max_informal_turns:
                    break
            results["phases"].append({
                "name": "informal",
                "turns": turn_count,
                "status": "completed",
                "task_id": informal_task_id,
                "task_closed": self._close_phase_task(
                    "informal", informal_task_id, "InformalAgent"
                ),
            })
        except Exception as e:
            _logger.error(f"Phase 1 error: {e}")
            results["phases"].append({
                "name": "informal",
                "status": "error",
                "error": str(e),
                "task_id": informal_task_id,
                "task_closed": False,
            })

        # Reprise ciblée de la phase déficitaire (#18776, branche « ou » de
        # la demande) : la phase informelle porte DEUX livrables (arguments,
        # sophismes) qui se disputent le même budget de tours ; selon le run,
        # l'un des deux sort vide ou purement formel, et c'est ce qui fait
        # basculer la forme du verdict. La reprise évalue chaque livrable
        # avec les seuils de substance du carnet (_verdict, source unique)
        # et relance UNIQUEMENT le livrable déficitaire, avec son propre
        # budget de tours — les budgets « arguments » et « sophismes » sont
        # ainsi séparés, comme le demande l'issue.
        if self.targeted_resumption:
            await self._run_targeted_resumption(results)

        # Phase 2: Formal analysis (logic)
        _logger.info("=== Phase 2: Formal Analysis ===")
        formal_task_id = self._open_phase_task("formal")
        logic = create_logic_agent(
            self.kernel, self.llm_service_id, self.state, task_id=formal_task_id
        )

        # Le PM réutilisé tel quel entre phases garde ses instructions
        # statiques de la phase 1 : il désigne 'InformalAgent' (absent de
        # ce chat) et re-crée des tâches d'identification d'arguments au
        # lieu d'exiger l'encodage formel (mesuré issue #18395). Un PM
        # dédié porte le contexte de la phase courante.
        pm_formal = create_pm_agent(
            self.kernel, self.llm_service_id, self.state
        )
        pm_formal.instructions = PROMPT_DEFINE_TASKS + """

[Phase courante : Analyse FORMELLE]
Les agents disponibles sont UNIQUEMENT ProjectManagerAgent et LogicAgent :
désignez toujours 'LogicAgent'. La tâche de cette phase : encoder les
arguments en belief sets propositionnels (StateManager-add_belief_set),
faire décider le solveur (Reasoner-pl_query) et consigner le verdict
renvoyé par le solveur (StateManager-log_query_result, raw_result = sortie
du solveur copiée telle quelle). Un verdict inventé par l'agent est refusé
par l'outil.
N'ajoutez PAS de tâche d'identification d'arguments : c'est le travail de
la phase 1, déjà passée.
"""

        phase2_history = ChatHistory()
        phase2_history.add_message(
            ChatMessageContent(
                role=AuthorRole.USER,
                content=(
                    "Poursuivez l'analyse : traduisez en logique propositionnelle "
                    f"les arguments identifiés.\n\n{self.state.raw_text}"
                ),
            )
        )

        try:
            group_chat2 = AgentGroupChat(
                agents=[pm_formal, logic],
                chat_history=phase2_history,
                termination_strategy=_iteration_cap(self.max_formal_turns),
            )
            turn_count = 0
            async for response in group_chat2.invoke():
                turn_count += 1
                _logger.info(f"  Turn {turn_count}: {response.name} responded")
                if turn_count >= self.max_formal_turns:
                    break
            results["phases"].append({
                "name": "formal",
                "turns": turn_count,
                "status": "completed",
                "task_id": formal_task_id,
                "task_closed": self._close_phase_task(
                    "formal", formal_task_id, "LogicAgent"
                ),
            })
        except Exception as e:
            _logger.error(f"Phase 2 error: {e}")
            results["phases"].append({
                "name": "formal",
                "status": "error",
                "error": str(e),
                "task_id": formal_task_id,
                "task_closed": False,
            })

        # Phase 3: Synthesis
        _logger.info("=== Phase 3: Synthesis ===")
        synthesis_agent = ChatCompletionAgent(
            kernel=self.kernel,
            name="SynthesisAgent",
            instructions=PROMPT_SYNTHESIS,
            service=_resolve_service(self.kernel, self.llm_service_id),
            arguments=_state_arguments(
                self.state, _execution_settings_for(self.kernel, self.llm_service_id)
            ),
        )

        phase3_history = ChatHistory()
        phase3_history.add_message(
            ChatMessageContent(
                role=AuthorRole.USER,
                content=(
                    "Rédigez la synthèse finale de l'analyse argumentative en "
                    f"vous appuyant sur l'état courant.\n\n{self.state.raw_text}"
                ),
            )
        )

        try:
            group_chat3 = AgentGroupChat(
                agents=[pm, synthesis_agent],
                chat_history=phase3_history,
                termination_strategy=_iteration_cap(3),
            )
            turn_count = 0
            async for response in group_chat3.invoke():
                turn_count += 1
                _logger.info(f"  Turn {turn_count}: {response.name} responded")
                if turn_count >= 3:
                    break
            results["phases"].append({
                "name": "synthesis",
                "turns": turn_count,
                "status": "completed",
            })
        except Exception as e:
            _logger.error(f"Phase 3 error: {e}")
            results["phases"].append({
                "name": "synthesis",
                "status": "error",
                "error": str(e),
            })

        # Final state snapshot
        results["state_snapshot"] = self.state.get_state_snapshot(summarize=True)
        if self.state.final_conclusion:
            results["conclusion"] = self.state.final_conclusion

        _logger.info("Analysis complete.")
        return results

    # ------------------------------------------------------------------
    # Reprise ciblée de la phase déficitaire (#18776)
    # ------------------------------------------------------------------

    async def _run_targeted_resumption(self, results: Dict[str, Any]) -> None:
        """Relance uniquement le livrable déficitaire de la phase informelle.

        Un « livrable » est un des deux produits de la phase informelle :
        les arguments substantifs et les sophismes substantifs (au sens des
        prédicats de ``_verdict`` — mêmes seuils que le carnet 08b et que la
        mesure ``budget_variance_study``). Jusqu'à ``resumption_max_rounds``
        rounds : on nettoie les entrées empoisonnées, on évalue les deux
        livrables, on relance chaque livrable sous son seuil, puis on
        ré-évalue au round suivant. Sortie dès que les deux seuils sont
        tenus — la reprise ne consomme rien sur un run qui n'en a pas
        besoin.

        Nettoyage (#18395, contrat du validateur du carnet) : une clé d'état
        en guise d'argument (check 1b) ou un sophisme dont la cible n'existe
        pas (check 2b) invalident la forme du verdict **quoi qu'on ajoute**
        ensuite — aucun remplissage additif ne peut les éliminer. La reprise
        les retire donc d'abord, de façon déterministe (aucun LLM), avant de
        remplir : ajouter ne suffit pas, il faut aussi purger.
        """
        for round_idx in range(1, self.resumption_max_rounds + 1):
            pruned = self._prune_poisoned_entries()
            if pruned["state_key_arguments"] or pruned["phantom_target_fallacies"]:
                results["phases"].append({
                    "name": "resumption_hygiene",
                    "round": round_idx,
                    "status": "completed",
                    **pruned,
                })
            n_args = count_substantive_arguments(self.state)
            n_fallacies = count_substantive_fallacies(self.state)
            deficits: List[tuple] = []
            if n_args < self.min_substantive_arguments:
                deficits.append(("arguments", n_args))
            if n_fallacies < self.min_substantive_fallacies:
                deficits.append(("fallacies", n_fallacies))
            if not deficits:
                _logger.info(
                    f"Reprise ciblée round {round_idx}: aucun déficit "
                    f"({n_args} args substantifs, {n_fallacies} sophismes substantifs)."
                )
                break
            _logger.info(
                f"=== Reprise ciblée round {round_idx}: déficits="
                f"{[(d, n) for d, n in deficits]} ==="
            )
            for deficit, current_count in deficits:
                entry = await self._run_resumption_chat(
                    deficit, round_idx, current_count
                )
                # Le remplissage peut lui-même introduire des cibles
                # fantômes : on purge à nouveau, et on le rapporte.
                post_pruned = self._prune_poisoned_entries()
                if post_pruned["state_key_arguments"] or post_pruned["phantom_target_fallacies"]:
                    entry["pruned_after"] = post_pruned
                results["phases"].append(entry)

    def _prune_poisoned_entries(self) -> Dict[str, List[str]]:
        """Retire les entrées que le validateur du carnet invalide à coup sûr.

        Déterministe (aucun appel LLM) : clés d'état en guise d'arguments et
        sophismes à cible inexistante. Retourne les identifiants retirés.
        """
        pruned_state_keys = state_key_argument_ids(self.state)
        for arg_id in pruned_state_keys:
            self.state.identified_arguments.pop(arg_id, None)
        pruned_phantoms = phantom_target_fallacy_ids(self.state)
        for f_id in pruned_phantoms:
            self.state.identified_fallacies.pop(f_id, None)
        if pruned_state_keys or pruned_phantoms:
            _logger.info(
                f"Reprise ciblée: nettoyage de {len(pruned_state_keys)} "
                f"clé(s) d'état et {len(pruned_phantoms)} cible(s) fantôme(s)."
            )
        return {
            "state_key_arguments": pruned_state_keys,
            "phantom_target_fallacies": pruned_phantoms,
        }

    def _resumption_agent(self, deficit: str) -> ChatCompletionAgent:
        """Agent focalisé portant le prompt de reprise d'UN livrable."""
        instructions = (
            PROMPT_RESUMPTION_ARGUMENTS
            if deficit == "arguments"
            else PROMPT_RESUMPTION_FALLACIES
        )
        return ChatCompletionAgent(
            kernel=self.kernel,
            name=f"Resumption{deficit.capitalize()}Agent",
            instructions=instructions,
            service=_resolve_service(self.kernel, self.llm_service_id),
            arguments=_state_arguments(
                self.state,
                _execution_settings_for(self.kernel, self.llm_service_id),
            ),
        )

    def _resumption_ask(
        self, deficit: str, round_idx: int, current_count: int
    ) -> str:
        """Message USER du chat de reprise : le déficit mesuré + le texte."""
        if deficit == "arguments":
            current_listing = json.dumps(
                dict(list(self.state.identified_arguments.items())[:8]),
                ensure_ascii=False,
            )
            return (
                f"Reprise ciblée (round {round_idx}) : l'état contient "
                f"{len(self.state.identified_arguments)} arguments dont "
                f"{current_count} substantifs "
                f"(objectif : au moins {self.min_substantive_arguments}). "
                f"Descriptions actuelles : {current_listing}\n\n"
                "Ajoutez les arguments manquants du texte suivant, chaque "
                "description reprenant une phrase COMPLÈTE du texte, mot "
                f"pour mot :\n\n{self.state.raw_text}"
            )
        current_listing = json.dumps(
            {
                fid: {
                    "type": fdata.get("type"),
                    "target": fdata.get("target_argument_id"),
                }
                for fid, fdata in list(self.state.identified_fallacies.items())[:8]
            },
            ensure_ascii=False,
        )
        return (
            f"Reprise ciblée (round {round_idx}) : l'état contient "
            f"{len(self.state.identified_fallacies)} sophismes dont "
            f"{current_count} substantifs "
            f"(objectif : au moins {self.min_substantive_fallacies}). "
            f"Entrées actuelles : {current_listing}\n"
            f"Identifiants d'arguments ciblables : "
            f"{list(self.state.identified_arguments.keys())}\n\n"
            "Détectez les sophismes du texte suivant (type + justification "
            f"+ cible) :\n\n{self.state.raw_text}"
        )

    async def _run_resumption_chat(
        self, deficit: str, round_idx: int, current_count: int
    ) -> Dict[str, Any]:
        """Un chat de reprise focalisé, borné par son propre budget."""
        cap = (
            self.max_resumption_argument_turns
            if deficit == "arguments"
            else self.max_resumption_fallacy_turns
        )
        agent = self._resumption_agent(deficit)
        ask = self._resumption_ask(deficit, round_idx, current_count)

        history = ChatHistory()
        history.add_message(
            ChatMessageContent(role=AuthorRole.USER, content=ask)
        )

        entry: Dict[str, Any] = {
            "name": f"resumption_{deficit}",
            "round": round_idx,
            "substantive_before": current_count,
        }
        try:
            group_chat = AgentGroupChat(
                agents=[agent],
                chat_history=history,
                termination_strategy=_iteration_cap(cap),
            )
            turn_count = 0
            async for response in group_chat.invoke():
                turn_count += 1
                _logger.info(
                    f"  Reprise {deficit} turn {turn_count}: {response.name} responded"
                )
                if turn_count >= cap:
                    break
            after = (
                count_substantive_arguments(self.state)
                if deficit == "arguments"
                else count_substantive_fallacies(self.state)
            )
            entry.update({
                "turns": turn_count,
                "status": "completed",
                "substantive_after": after,
                "budget_turns": cap,
            })
        except Exception as e:
            _logger.error(f"Reprise {deficit} error: {e}")
            entry.update({"status": "error", "error": str(e)})
        return entry

    async def run_conversational(self, max_turns: int = 6) -> Dict[str, Any]:
        """Orchestration conversationnelle réelle : UN seul AgentGroupChat
        (PM + Informal + Logic) dont la sélection passe par
        ``DelegatingSelectionStrategy`` — le PM désigne le prochain agent
        dans l'état partagé, la stratégie honore cette désignation.

        Contrairement à ``run()`` (3 phases fixes, routage par séquence),
        la séquence d'agents émerge des désignations du PM : deux textes
        différents peuvent produire deux séquences différentes (#18393).

        ``max_turns`` bas par design (plafond affiché, coût borné).
        """
        from argumentation_lib._delegating_selection import (
            DelegatingSelectionStrategy,
        )

        _logger.info("Starting conversational orchestration...")
        # #23726 : une tâche porte la conversation ; son identifiant exact
        # est donné aux deux agents qui peuvent la clôturer.
        conversation_task_id = self._open_phase_task("conversation")
        pm = create_pm_agent(self.kernel, self.llm_service_id, self.state)
        informal = create_informal_agent(
            self.kernel,
            self.llm_service_id,
            self.state,
            task_id=conversation_task_id,
        )
        logic = create_logic_agent(
            self.kernel, self.llm_service_id, self.state, task_id=conversation_task_id
        )
        agents = [pm, informal, logic]

        strategy = DelegatingSelectionStrategy(
            agents=agents,
            state=self.state,
            default_agent_name="ProjectManagerAgent",
        )

        history = ChatHistory()
        history.add_message(
            ChatMessageContent(
                role=AuthorRole.USER,
                content=(
                    "Analysez le texte suivant. Le PM orchestre : après chaque "
                    "tour il désigne le prochain agent via "
                    "StateManager-designate_next_agent.\n\n"
                    f"{self.state.raw_text}"
                ),
            )
        )

        group_chat = AgentGroupChat(
            agents=agents,
            selection_strategy=strategy,
            chat_history=history,
        )

        journal: List[Dict[str, Any]] = []
        turn_count = 0
        async for response in group_chat.invoke():
            turn_count += 1
            content = str(response.content or "").strip()
            journal.append(
                {
                    "turn": turn_count,
                    "speaker": response.name,
                    "excerpt": content[:200],
                }
            )
            _logger.info(
                f"  Turn {turn_count}/{max_turns}: {response.name} responded"
            )
            if turn_count >= max_turns:
                break

        return {
            "turns": turn_count,
            "max_turns": max_turns,
            "journal": journal,
            "sequence": [entry["speaker"] for entry in journal],
            "selection_trace": strategy.selection_trace,
            "task_id": conversation_task_id,
            "task_closed": self._close_phase_task(
                "conversation", conversation_task_id, "conversation"
            ),
            "state_snapshot": self.state.get_state_snapshot(summarize=True),
            "conclusion": self.state.final_conclusion,
        }

    def run_sync(self) -> Dict[str, Any]:
        """Synchronous wrapper for run()."""
        import asyncio
        try:
            loop = asyncio.get_running_loop()
        except RuntimeError:
            loop = None

        if loop and loop.is_running():
            import concurrent.futures
            with concurrent.futures.ThreadPoolExecutor() as pool:
                future = pool.submit(asyncio.run, self.run())
                return future.result(timeout=300)
        else:
            return asyncio.run(self.run())
