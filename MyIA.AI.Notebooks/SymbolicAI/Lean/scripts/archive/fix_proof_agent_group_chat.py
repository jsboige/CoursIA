#!/usr/bin/env python3
"""
Fix Lean-9 notebook ProofAgentGroupChat with improved state tracking.
Version 3: Better proof detection logic.
"""

import json
import sys

NOTEBOOK_PATH = "d:/dev/CoursIA/MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-9-SK-Multi-Agents.ipynb"

# New ProofAgentGroupChat class with improved state tracking
NEW_PROOF_AGENT_GROUP_CHAT = '''class ProofAgentGroupChat:
    """
    Orchestre les agents pour la preuve de theoremes.
    Supporte mode simulation (SimpleAgent) et mode SK (ChatCompletionAgent).
    """

    def __init__(self, agents: Dict[str, Any], state: ProofState, use_sk: bool = True):
        self.agents = agents
        self.state = state
        self.use_sk = use_sk and SK_AVAILABLE
        self.history = []
        self._proof_tactics_found = []  # Track tactics found across iterations

    def run(self, initial_message: str, verbose: bool = True) -> str:
        """Execute la conversation multi-agents."""
        if self.use_sk:
            # Mode Semantic Kernel - utilise async
            import asyncio
            import nest_asyncio
            nest_asyncio.apply()
            try:
                loop = asyncio.get_event_loop()
                return loop.run_until_complete(self._run_sk(initial_message, verbose))
            except RuntimeError:
                return asyncio.run(self._run_sk(initial_message, verbose))
        else:
            # Mode simulation - sync
            return self._run_fallback(initial_message, verbose)

    async def _run_sk(self, initial_message: str, verbose: bool = True) -> str:
        """Execution avec Semantic Kernel ChatCompletionAgent."""
        from semantic_kernel.contents.chat_history import ChatHistory
        from semantic_kernel.contents.chat_message_content import ChatMessageContent
        from semantic_kernel.contents.utils.author_role import AuthorRole

        if verbose:
            print("=" * 60)
            print(f"Session MULTI-AGENTS (SK): {initial_message[:80]}...")
            print("=" * 60)

        # Creer l'historique de chat partage entre les agents
        chat_history = ChatHistory()
        chat_history.add_user_message(initial_message)

        current_message = initial_message
        agent_order = ["SearchAgent", "TacticAgent", "VerifierAgent", "CriticAgent", "CoordinatorAgent"]

        for i in range(self.state.max_iterations):
            self.state.iteration = i + 1
            self.state.increment_iteration()

            # Determiner l'agent a utiliser
            designated = self.state.consume_next_agent_designation()
            if designated and designated in self.agents:
                agent_name = designated
            else:
                agent_name = agent_order[i % len(agent_order)]

            agent = self.agents.get(agent_name)
            if not agent:
                continue

            if verbose:
                print(f"\\n[Tour {self.state.iteration_count}] {agent_name}")

            # Invoquer l'agent SK de maniere asynchrone
            try:
                response_text = ""

                # ChatCompletionAgent.invoke() prend un ChatHistory et retourne un AsyncIterable
                async for response in agent.invoke(chat_history):
                    if hasattr(response, 'content') and response.content:
                        response_text += str(response.content)
                    elif hasattr(response, 'items'):
                        # Si c'est un ChatMessageContent avec items
                        for item in response.items:
                            if hasattr(item, 'text'):
                                response_text += item.text

                if not response_text:
                    response_text = f"[{agent_name}] Pas de reponse"

                # Ajouter la reponse a l'historique
                chat_history.add_assistant_message(response_text)

                # Ajouter le prochain message utilisateur (contexte pour le prochain agent)
                if i < self.state.max_iterations - 1:
                    next_context = f"Continue la preuve. Reponse precedente de {agent_name}: {response_text[:200]}"
                    chat_history.add_user_message(next_context)

                # Mettre a jour l'etat selon la reponse
                self._update_state_from_response(agent_name, response_text)

            except Exception as e:
                import traceback
                response_text = f"Erreur agent {agent_name}: {str(e)}"
                if verbose:
                    print(f"  [ERROR] {e}")
                    traceback.print_exc()

            self.history.append({
                "iteration": self.state.iteration_count,
                "agent": agent_name,
                "response": response_text[:200] if response_text else "",
            })

            if verbose:
                display_response = response_text[:200] + "..." if len(response_text) > 200 else response_text
                print(f"  Response: {display_response}")

            if self.state.proof_complete:
                if verbose:
                    print(f"\\n[LOG] Preuve trouvee!")
                break

            current_message = response_text

        if verbose:
            print("\\n" + "=" * 60)
            print(f"Session terminee apres {self.state.iteration_count} iterations.")
            print("=" * 60)

        return self.state.final_proof or "Preuve non trouvee"

    def _update_state_from_response(self, agent_name: str, response: str):
        """Met a jour l'etat partage en fonction de la reponse de l'agent."""
        import re
        response_lower = response.lower()

        # Detection des lemmes decouverts
        if "lemma:" in response_lower or "found:" in response_lower or "nat." in response_lower:
            lemma_matches = re.findall(r'(Nat\\.\\w+|Eq\\.\\w+|List\\.\\w+)', response)
            for lemma in lemma_matches:
                if lemma not in self.state.discovered_lemmas:
                    self.state.discovered_lemmas.append(lemma)

        # Detection des tactiques - track across iterations
        proof_patterns = [
            (r'simp\\s*\\[[^\\]]*\\]', 'simp'),
            (r'\\brfl\\b', 'rfl'),
            (r'exact\\s+\\w+', 'exact'),
            (r'\\bring\\b', 'ring'),
            (r'\\bomega\\b', 'omega'),
            (r'\\blinarith\\b', 'linarith'),
            (r'\\bdecide\\b', 'decide'),
        ]

        for pattern, tactic_name in proof_patterns:
            if re.search(pattern, response, re.IGNORECASE):
                if tactic_name not in self._proof_tactics_found:
                    self._proof_tactics_found.append(tactic_name)
                    self.state.tactics_history.append(response[:100])

        # Detection de preuve complete - multiple signals
        proof_complete_signals = [
            "proof complete",
            "qed",
            "verified",
            "goals accomplished",
            "proof found",
            "la preuve est terminee",
            "la preuve est cloturee",
            "preuve reussie",
        ]

        if any(signal in response_lower for signal in proof_complete_signals):
            # If we have found tactics earlier, mark as complete
            if self._proof_tactics_found:
                self.state.phase = ProofPhase.COMPLETE
                if not self.state.final_proof:
                    self.state.final_proof = self._proof_tactics_found[0]
        elif ":= by" in response and self._proof_tactics_found:
            # Lean-style proof block detected with tactics
            self.state.phase = ProofPhase.COMPLETE
            if not self.state.final_proof:
                self.state.final_proof = self._proof_tactics_found[0]

        # Alternative: detect complete proof in code block
        code_block_match = re.search(r'```lean\\n(.*?)```', response, re.DOTALL)
        if code_block_match:
            code_content = code_block_match.group(1)
            if ":= by" in code_content or ":= rfl" in code_content:
                # Check for proof tactics in the code block
                for pattern, tactic_name in proof_patterns:
                    if re.search(pattern, code_content, re.IGNORECASE):
                        self.state.phase = ProofPhase.COMPLETE
                        self.state.final_proof = code_content.strip()[:200]
                        break

        # Detection de delegation
        delegate_patterns = [
            (r'@TacticAgent|delegate.*TacticAgent', 'TacticAgent'),
            (r'@VerifierAgent|delegate.*VerifierAgent', 'VerifierAgent'),
            (r'@CriticAgent|delegate.*CriticAgent', 'CriticAgent'),
            (r'@CoordinatorAgent|delegate.*CoordinatorAgent', 'CoordinatorAgent'),
            (r'@SearchAgent|delegate.*SearchAgent', 'SearchAgent'),
        ]
        for pattern, target in delegate_patterns:
            if re.search(pattern, response, re.IGNORECASE):
                self.state.designate_next_agent(target)
                break

    def _run_fallback(self, initial_message: str, verbose: bool = True) -> str:
        """Execution sans Semantic Kernel (mode simulation)."""
        if verbose:
            print("=" * 60)
            print(f"Session MULTI-AGENTS: {initial_message[:80]}...")
            print("=" * 60)

        current_message = initial_message
        agent_order = ["SearchAgent", "TacticAgent", "VerifierAgent", "CriticAgent", "CoordinatorAgent"]

        for i in range(self.state.max_iterations):
            self.state.iteration = i + 1

            designated = self.state.consume_next_agent_designation()
            if designated and designated in self.agents:
                agent_name = designated
            else:
                agent_name = agent_order[i % len(agent_order)]

            agent = self.agents.get(agent_name)
            if not agent:
                continue

            if verbose:
                print(f"\\n[Tour {self.state.iteration_count}] {agent_name}")

            response = agent.invoke(current_message, self.state)

            self.history.append({
                "iteration": self.state.iteration_count,
                "agent": agent_name,
                "response": response[:200] if response else "",
            })

            if verbose:
                print(f"  Response: {response[:200]}..." if len(response) > 200 else f"  Response: {response}")

            if self.state.proof_complete:
                if verbose:
                    print(f"\\n[LOG] Preuve trouvee!")
                break

            current_message = response

        if verbose:
            print("\\n" + "=" * 60)
            print(f"Session terminee apres {self.state.iteration_count} iterations.")
            print("=" * 60)

        return self.state.final_proof or "Preuve non trouvee"


# Test rapide
print("ProofAgentGroupChat defini (mode SK + simulation)")'''


def main():
    print(f"Loading notebook: {NOTEBOOK_PATH}")

    with open(NOTEBOOK_PATH, 'r', encoding='utf-8') as f:
        notebook = json.load(f)

    # Find the cell with ProofAgentGroupChat class
    target_cell_idx = None
    for idx, cell in enumerate(notebook['cells']):
        if cell['cell_type'] == 'code':
            source = ''.join(cell['source'])
            if 'class ProofAgentGroupChat:' in source and '_run_fallback' in source:
                target_cell_idx = idx
                break

    if target_cell_idx is None:
        print("ERROR: Could not find ProofAgentGroupChat cell")
        sys.exit(1)

    print(f"Found ProofAgentGroupChat at cell {target_cell_idx}")

    # Replace the cell source
    new_source_lines = NEW_PROOF_AGENT_GROUP_CHAT.split('\n')
    new_source = [line + '\n' for line in new_source_lines[:-1]] + [new_source_lines[-1]]

    notebook['cells'][target_cell_idx]['source'] = new_source
    notebook['cells'][target_cell_idx]['outputs'] = [
        {
            "name": "stdout",
            "output_type": "stream",
            "text": ["ProofAgentGroupChat defini (mode SK + simulation)\n"]
        }
    ]

    # Save
    with open(NOTEBOOK_PATH, 'w', encoding='utf-8') as f:
        json.dump(notebook, f, indent=1, ensure_ascii=False)

    print(f"Updated ProofAgentGroupChat with improved state tracking")
    print("Changes:")
    print("  - Track proof tactics across iterations")
    print("  - Better proof completion detection")
    print("  - Detect proofs in Lean code blocks")
    print("  - Multiple completion signal patterns")


if __name__ == "__main__":
    main()
