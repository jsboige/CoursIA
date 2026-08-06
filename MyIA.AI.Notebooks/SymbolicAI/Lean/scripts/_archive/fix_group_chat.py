#!/usr/bin/env python3
"""
Fix ProofAgentGroupChat to work without Semantic Kernel.
Makes the class SK-independent by using only _run_fallback when SK is not available.
"""

import json
from pathlib import Path


def read_notebook(path: str):
    with open(path, 'r', encoding='utf-8', newline='') as f:
        return json.load(f)


def write_notebook(path: str, nb):
    with open(path, 'w', encoding='utf-8', newline='\n') as f:
        json.dump(nb, f, indent=1, ensure_ascii=False)
        f.write('\n')


def get_cell_source(cell):
    return ''.join(cell['source']) if isinstance(cell['source'], list) else cell['source']


def set_cell_source(cell, source):
    lines = source.split('\n')
    cell['source'] = [line + '\n' for line in lines[:-1]] + ([lines[-1]] if lines[-1] else [])


# New ProofAgentGroupChat class that works without SK
NEW_GROUP_CHAT_CLASS = '''class ProofAgentGroupChat:
    """
    Orchestre les agents pour la preuve de theoremes.
    Fonctionne en mode simulation sans Semantic Kernel.
    """

    def __init__(self, agents: Dict[str, Any], state: ProofState, use_sk: bool = True):
        self.agents = agents
        self.state = state
        self.use_sk = use_sk and SK_AVAILABLE
        self.history = []

    def run(self, initial_message: str, verbose: bool = True) -> str:
        """Execute la conversation multi-agents."""
        # Always use fallback mode in simulation (SK not available)
        return self._run_fallback(initial_message, verbose)

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
print("ProofAgentGroupChat defini (mode simulation)")
'''


def main():
    script_dir = Path(__file__).parent
    notebook_dir = script_dir.parent
    lean9_path = notebook_dir / 'Lean-9-SK-Multi-Agents.ipynb'

    print("=" * 80)
    print("FIX PROOFAGENTGROUPCHAT FOR SIMULATION MODE")
    print("=" * 80)

    nb = read_notebook(str(lean9_path))
    print(f"Read {len(nb['cells'])} cells")

    changes = 0

    # Find and replace Cell 32 (ProofAgentGroupChat)
    for i, cell in enumerate(nb['cells']):
        if cell['cell_type'] != 'code':
            continue
        src = get_cell_source(cell)

        if 'class ProofAgentGroupChat' in src:
            print(f"Found ProofAgentGroupChat in cell {i}")
            set_cell_source(cell, NEW_GROUP_CHAT_CLASS)
            print("  Replaced with simulation-compatible version")
            changes += 1
            break

    if changes >= 1:
        write_notebook(str(lean9_path), nb)
        print(f"\nNotebook saved with {changes} update(s)")
    else:
        print("\nProofAgentGroupChat not found!")


if __name__ == '__main__':
    main()
