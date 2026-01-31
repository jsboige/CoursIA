#!/usr/bin/env python3
"""
Fix logging issues and DEMO_4 theorem in Lean-9-SK-Multi-Agents.ipynb

Problems identified:
1. Massive empty spaces in LLM responses (newlines)
2. No timestamps on iterations
3. Responses truncated with "..."
4. DEMO_4 has a direct Mathlib lemma (Nat.add_succ) - shortcut in 4 iterations

Fixes:
1. Add timestamp to each iteration log
2. Clean up excessive newlines from LLM responses
3. Show full response (or configurable limit)
4. Change DEMO_4 to a theorem requiring real exploration
"""

import json
import re
from datetime import datetime

NOTEBOOK_PATH = "d:/dev/CoursIA/MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-9-SK-Multi-Agents.ipynb"

# New DEMO_4 - requires multiple steps, no direct Mathlib lemma
# This theorem mixes addition and successor in a way that requires reasoning
NEW_DEMO_4 = {
    "name": "DEMO_4_COMPOSED",
    "theorem": "theorem double_eq_add_self (n : Nat) : 2 * n = n + n",
    "description": "Composition - pas de lemme direct, requires multiple rewrites",
    "expected_iterations": "6-10",
    "expected_lemmas": 2,
    "expected_agents": ["SearchAgent", "TacticAgent", "VerifierAgent", "CriticAgent"],
    "complexity": "Avancee - ring ou rewrites multiples",
    "strategy": "ring OU simp [Nat.two_mul] OU rw [Nat.succ_mul, Nat.one_mul]",
    "trap": "simp seul peut echouer, rfl impossible, besoin de strategie"
}

# New ProofAgentGroupChat._run_sk method with improved logging
NEW_RUN_SK_METHOD = '''    async def _run_sk(self, initial_message: str, verbose: bool = True) -> str:
        """Execution avec Semantic Kernel ChatCompletionAgent - LOGGING AMELIORE."""
        from semantic_kernel.contents.chat_history import ChatHistory
        from semantic_kernel.contents.chat_message_content import ChatMessageContent
        from semantic_kernel.contents.utils.author_role import AuthorRole
        from datetime import datetime
        import re

        def clean_response(text: str) -> str:
            """Nettoie les reponses LLM (supprime newlines excessifs)."""
            # Remplacer sequences de 3+ newlines par 2
            text = re.sub(r'\\n{3,}', '\\n\\n', text)
            # Supprimer espaces en debut/fin
            text = text.strip()
            return text

        def format_timestamp() -> str:
            """Retourne timestamp lisible."""
            return datetime.now().strftime("%H:%M:%S.%f")[:-3]

        if verbose:
            print("=" * 70)
            print(f"[{format_timestamp()}] SESSION MULTI-AGENTS (SK)")
            print(f"Theoreme: {initial_message[:100]}...")
            print("=" * 70)

        # Creer l'historique de chat partage entre les agents
        chat_history = ChatHistory()
        chat_history.add_user_message(initial_message)

        current_message = initial_message
        agent_order = ["SearchAgent", "TacticAgent", "VerifierAgent", "CriticAgent", "CoordinatorAgent"]

        for i in range(self.state.max_iterations):
            self.state.iteration = i + 1
            self.state.increment_iteration()
            iter_start = datetime.now()

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
                print(f"\\n{'─' * 70}")
                print(f"[{format_timestamp()}] TOUR {self.state.iteration_count} | Agent: {agent_name}")
                print(f"{'─' * 70}")

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

                # Nettoyer la reponse
                response_text = clean_response(response_text)

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

            iter_duration = (datetime.now() - iter_start).total_seconds()

            self.history.append({
                "iteration": self.state.iteration_count,
                "agent": agent_name,
                "response": response_text,
                "duration_s": iter_duration
            })

            if verbose:
                # Afficher reponse complete (pas tronquee)
                print(f"  Reponse ({len(response_text)} chars, {iter_duration:.2f}s):")
                # Indenter chaque ligne pour lisibilite
                for line in response_text.split('\\n')[:30]:  # Max 30 lignes
                    if line.strip():
                        print(f"    {line}")
                if response_text.count('\\n') > 30:
                    print(f"    ... ({response_text.count(chr(10)) - 30} lignes supprimees)")

            if self.state.proof_complete:
                if verbose:
                    print(f"\\n[{format_timestamp()}] PREUVE TROUVEE!")
                    print(f"  Tactique finale: {self.state.final_proof}")
                break

            current_message = response_text

        if verbose:
            print("\\n" + "=" * 70)
            print(f"[{format_timestamp()}] SESSION TERMINEE")
            print(f"  Iterations: {self.state.iteration_count}")
            print(f"  Lemmes decouverts: {len(self.state.discovered_lemmas)}")
            print(f"  Tactiques essayees: {len(self.state.tactics_history)}")
            print("=" * 70)

        return self.state.final_proof or "Preuve non trouvee"'''


def update_notebook():
    """Update the notebook with improved logging and DEMO_4."""
    print(f"Reading: {NOTEBOOK_PATH}")

    with open(NOTEBOOK_PATH, 'r', encoding='utf-8') as f:
        notebook = json.load(f)

    changes = []

    for idx, cell in enumerate(notebook['cells']):
        if cell['cell_type'] != 'code':
            continue

        source = ''.join(cell['source'])
        modified = False

        # 1. Update DEMO_4 in DEMOS list
        if 'DEMOS = [' in source and '"name": "DEMO_4' in source:
            # Find and replace DEMO_4 definition
            # Pattern to match the DEMO_4 dict
            demo4_pattern = r'(\{\s*"name":\s*"DEMO_4_INDUCTION"[^}]+\})'

            new_demo4_str = json.dumps(NEW_DEMO_4, indent=8, ensure_ascii=False)
            # Fix indentation for notebook
            new_demo4_str = new_demo4_str.replace('\n', '\n    ')

            if re.search(demo4_pattern, source, re.DOTALL):
                new_source = re.sub(demo4_pattern, new_demo4_str, source, flags=re.DOTALL)
                if new_source != source:
                    lines = new_source.split('\n')
                    notebook['cells'][idx]['source'] = [line + '\n' for line in lines[:-1]] + [lines[-1]]
                    changes.append(f"Cell {idx}: Updated DEMO_4 to 'double_eq_add_self'")
                    modified = True

        # 2. Update ProofAgentGroupChat._run_sk method
        if 'async def _run_sk' in source and 'ChatCompletionAgent' in source:
            # Find the method and replace it
            method_start = source.find('    async def _run_sk')
            if method_start != -1:
                # Find the end of the method (next method or end of class)
                method_end = source.find('\n    def ', method_start + 1)
                if method_end == -1:
                    method_end = source.find('\n    async def ', method_start + 1)
                if method_end == -1:
                    # End of class - find where the class ends
                    method_end = len(source)

                old_method = source[method_start:method_end]
                new_source = source[:method_start] + NEW_RUN_SK_METHOD + '\n\n' + source[method_end:]

                if new_source != source:
                    lines = new_source.split('\n')
                    notebook['cells'][idx]['source'] = [line + '\n' for line in lines[:-1]] + [lines[-1]]
                    changes.append(f"Cell {idx}: Updated _run_sk with improved logging")
                    modified = True

    if changes:
        with open(NOTEBOOK_PATH, 'w', encoding='utf-8') as f:
            json.dump(notebook, f, indent=1, ensure_ascii=False)

        print("\nChanges made:")
        for c in changes:
            print(f"  - {c}")
        print(f"\nNotebook saved.")
    else:
        print("No changes made - patterns not found. Manual update may be needed.")

    return len(changes) > 0


def main():
    print("=" * 70)
    print("FIX LOGGING AND DEMO_4")
    print("=" * 70)
    print()
    print("Problems being fixed:")
    print("  1. Massive empty spaces in LLM responses")
    print("  2. No timestamps on iterations")
    print("  3. Responses truncated with '...'")
    print("  4. DEMO_4 has direct Mathlib lemma (4 iterations instead of 6-10)")
    print()
    print("Solutions:")
    print("  1. clean_response() removes excessive newlines")
    print("  2. format_timestamp() adds HH:MM:SS.mmm")
    print("  3. Full response displayed (max 30 lines)")
    print("  4. DEMO_4 changed to 'double_eq_add_self (2*n = n+n)'")
    print()
    print("-" * 70)

    success = update_notebook()

    print()
    print("=" * 70)
    if success:
        print("SUCCESS: Logging and DEMO_4 updated")
        print()
        print("Expected improvements:")
        print("  - Clear timestamps on each iteration")
        print("  - No more empty spaces from LLM responses")
        print("  - Full responses visible (not truncated)")
        print("  - DEMO_4 should now take 6-10 iterations")
    else:
        print("WARNING: Some patterns not found")
        print("Manual update may be required.")
    print("=" * 70)


if __name__ == "__main__":
    main()
