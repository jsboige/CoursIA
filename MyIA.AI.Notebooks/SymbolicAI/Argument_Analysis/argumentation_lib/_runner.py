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
from typing import Any, Dict, List, Optional

from semantic_kernel import Kernel
from semantic_kernel.agents.chat_completion.chat_completion_agent import (
    ChatCompletionAgent,
)
from semantic_kernel.agents.group_chat.agent_group_chat import AgentGroupChat
from semantic_kernel.contents.chat_message_content import ChatMessageContent
from semantic_kernel.contents.utils.author_role import AuthorRole
from semantic_kernel.contents.chat_history import ChatHistory

from argumentation_lib._shared_state import RhetoricalAnalysisState
from argumentation_lib._state_manager_plugin import StateManagerPlugin

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

[État Actuel]
{{$analysis_state}}

[Instructions]
Trouvez la première étape non complétée.
Répondez AU FORMAT JSON:
{
  "task_description": "Description de la tâche",
  "assigned_agent": "InformalAgent|LogicAgent|PM"
}
Si toutes les étapes sont complétées, rédigez la conclusion finale.
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
- Marquer la tâche comme répondue
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
- Marquer la tâche comme répondue
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


# ---------------------------------------------------------------------------
# Agent builders — direct instantiation, no factory needed
# ---------------------------------------------------------------------------

def create_pm_agent(
    kernel: Kernel,
    llm_service_id: str,
    state: RhetoricalAnalysisState,
) -> ChatCompletionAgent:
    """Create the Project Manager agent."""
    smp = StateManagerPlugin(state)
    kernel.add_plugin(smp, plugin_name="StateManager")

    agent = ChatCompletionAgent(
        kernel=kernel,
        name="ProjectManagerAgent",
        instructions=PROMPT_DEFINE_TASKS,
        service_id=llm_service_id,
    )
    _logger.info("PM agent created with StateManagerPlugin.")
    return agent


def create_informal_agent(
    kernel: Kernel,
    llm_service_id: str,
    state: RhetoricalAnalysisState,
) -> ChatCompletionAgent:
    """Create the Informal Analysis agent."""
    # StateManagerPlugin already added by PM — reuse it
    if "StateManager" not in [p.name for p in kernel.plugins.values()]:
        smp = StateManagerPlugin(state)
        kernel.add_plugin(smp, plugin_name="StateManager")

    agent = ChatCompletionAgent(
        kernel=kernel,
        name="InformalAgent",
        instructions=PROMPT_INFORMAL_ANALYSIS,
        service_id=llm_service_id,
    )
    _logger.info("Informal agent created.")
    return agent


def create_logic_agent(
    kernel: Kernel,
    llm_service_id: str,
    state: RhetoricalAnalysisState,
) -> ChatCompletionAgent:
    """Create the Logic Analysis agent."""
    if "StateManager" not in [p.name for p in kernel.plugins.values()]:
        smp = StateManagerPlugin(state)
        kernel.add_plugin(smp, plugin_name="StateManager")

    agent = ChatCompletionAgent(
        kernel=kernel,
        name="LogicAgent",
        instructions=PROMPT_LOGIC_ANALYSIS,
        service_id=llm_service_id,
    )
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
    ):
        self.kernel = kernel
        self.llm_service_id = llm_service_id
        self.state = state
        self.max_turns = max_turns

        # Register StateManagerPlugin on kernel
        if "StateManager" not in [p.name for p in kernel.plugins.values()]:
            self._smp = StateManagerPlugin(state)
            kernel.add_plugin(self._smp, plugin_name="StateManager")
        else:
            self._smp = None

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
        informal = create_informal_agent(
            self.kernel, self.llm_service_id, self.state
        )
        pm = create_pm_agent(self.kernel, self.llm_service_id, self.state)

        phase1_history = ChatHistory()
        phase1_history.add_message(
            ChatMessageContent(
                role=AuthorRole.USER,
                content=f"Analysez le texte suivant:\\n\\n{self.state.raw_text}",
            )
        )

        group_chat = AgentGroupChat(
            agents=[pm, informal],
        )

        try:
            turn_count = 0
            async for response in group_chat.invoke():
                turn_count += 1
                _logger.info(f"  Turn {turn_count}: {response.name} responded")
                if turn_count >= self.max_turns // 2:
                    break
            results["phases"].append({
                "name": "informal",
                "turns": turn_count,
                "status": "completed",
            })
        except Exception as e:
            _logger.error(f"Phase 1 error: {e}")
            results["phases"].append({
                "name": "informal",
                "status": "error",
                "error": str(e),
            })

        # Phase 2: Formal analysis (logic)
        _logger.info("=== Phase 2: Formal Analysis ===")
        logic = create_logic_agent(
            self.kernel, self.llm_service_id, self.state
        )

        try:
            group_chat2 = AgentGroupChat(
                agents=[pm, logic],
            )
            turn_count = 0
            async for response in group_chat2.invoke():
                turn_count += 1
                _logger.info(f"  Turn {turn_count}: {response.name} responded")
                if turn_count >= self.max_turns // 2:
                    break
            results["phases"].append({
                "name": "formal",
                "turns": turn_count,
                "status": "completed",
            })
        except Exception as e:
            _logger.error(f"Phase 2 error: {e}")
            results["phases"].append({
                "name": "formal",
                "status": "error",
                "error": str(e),
            })

        # Phase 3: Synthesis
        _logger.info("=== Phase 3: Synthesis ===")
        synthesis_agent = ChatCompletionAgent(
            kernel=self.kernel,
            name="SynthesisAgent",
            instructions=PROMPT_SYNTHESIS,
            service_id=self.llm_service_id,
        )

        try:
            group_chat3 = AgentGroupChat(
                agents=[pm, synthesis_agent],
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
