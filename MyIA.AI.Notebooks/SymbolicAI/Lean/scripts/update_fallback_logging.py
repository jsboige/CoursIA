#!/usr/bin/env python3
"""
Update _run_fallback method with improved logging.
"""

import json
import re

NOTEBOOK_PATH = "d:/dev/CoursIA/MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-9-SK-Multi-Agents.ipynb"

NEW_FALLBACK = '''    def _run_fallback(self, initial_message: str, verbose: bool = True) -> str:
        """Execution sans Semantic Kernel (mode simulation) - LOGGING AMELIORE."""
        from datetime import datetime

        def format_timestamp() -> str:
            return datetime.now().strftime("%H:%M:%S.%f")[:-3]

        if verbose:
            print("=" * 70)
            print(f"[{format_timestamp()}] SESSION MULTI-AGENTS (Simulation)")
            print(f"Theoreme: {initial_message[:100]}...")
            print("=" * 70)

        current_message = initial_message
        agent_order = ["SearchAgent", "TacticAgent", "VerifierAgent", "CriticAgent", "CoordinatorAgent"]

        for i in range(self.state.max_iterations):
            self.state.iteration = i + 1
            iter_start = datetime.now()

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

            response = agent.invoke(current_message, self.state)
            iter_duration = (datetime.now() - iter_start).total_seconds()

            self.history.append({
                "iteration": self.state.iteration_count,
                "agent": agent_name,
                "response": response,
                "duration_s": iter_duration
            })

            if verbose:
                print(f"  Reponse ({len(response)} chars, {iter_duration:.3f}s):")
                for line in response.split('\\n')[:20]:
                    if line.strip():
                        print(f"    {line}")
                if response.count('\\n') > 20:
                    print(f"    ... ({response.count(chr(10)) - 20} lignes supprimees)")

            if self.state.proof_complete:
                if verbose:
                    print(f"\\n[{format_timestamp()}] PREUVE TROUVEE!")
                    print(f"  Tactique finale: {self.state.final_proof}")
                break

            current_message = response

        if verbose:
            print("\\n" + "=" * 70)
            print(f"[{format_timestamp()}] SESSION TERMINEE")
            print(f"  Iterations: {self.state.iteration_count}")
            print(f"  Lemmes decouverts: {len(self.state.discovered_lemmas)}")
            print(f"  Tactiques essayees: {len(self.state.tactics_history)}")
            print("=" * 70)

        return self.state.final_proof or "Preuve non trouvee"'''


def main():
    print(f"Reading: {NOTEBOOK_PATH}")

    with open(NOTEBOOK_PATH, 'r', encoding='utf-8') as f:
        nb = json.load(f)

    updated = False
    for idx, cell in enumerate(nb['cells']):
        if cell['cell_type'] != 'code':
            continue

        source = ''.join(cell['source'])

        if 'def _run_fallback' in source and 'Execution sans Semantic Kernel' in source:
            # Find method boundaries
            method_start = source.find('    def _run_fallback')
            if method_start == -1:
                continue

            # Find next method at same indent level
            remaining = source[method_start + 10:]  # Skip past 'def _run_'
            next_method = re.search(r'\n    def [a-z_]+\(', remaining)

            if next_method:
                method_end = method_start + 10 + next_method.start()
            else:
                method_end = len(source)

            # Replace
            new_source = source[:method_start] + NEW_FALLBACK + '\n' + source[method_end:]

            if new_source != source:
                lines = new_source.split('\n')
                nb['cells'][idx]['source'] = [line + '\n' for line in lines[:-1]] + [lines[-1]]
                print(f"Updated _run_fallback in Cell {idx}")
                updated = True
                break

    if updated:
        with open(NOTEBOOK_PATH, 'w', encoding='utf-8') as f:
            json.dump(nb, f, indent=1, ensure_ascii=False)
        print("Notebook saved.")
    else:
        print("No changes made.")

    return updated


if __name__ == "__main__":
    main()
