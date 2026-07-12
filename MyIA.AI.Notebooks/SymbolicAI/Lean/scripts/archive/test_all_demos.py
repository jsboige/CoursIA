#!/usr/bin/env python3
"""
Test all 4 DEMOS in simulation mode to verify the progression works.
"""

import json
import os
import sys

# Force simulation mode
os.environ['OPENAI_API_KEY'] = ''

NOTEBOOK_PATH = "d:/dev/CoursIA/MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-9-SK-Multi-Agents.ipynb"


def main():
    # Load notebook
    with open(NOTEBOOK_PATH, 'r', encoding='utf-8') as f:
        nb = json.load(f)

    # Execute all cells except demo runs
    namespace = {'__name__': '__main__', 'USE_LLM_MODE': False}

    for idx, cell in enumerate(nb['cells']):
        if cell['cell_type'] != 'code':
            continue
        source = ''.join(cell['source'])

        # Skip actual demo executions (result_X lines)
        if 'result_1 =' in source or 'result_2 =' in source:
            continue
        if 'result_3 =' in source or 'result_4 =' in source:
            continue

        # Force simulation mode
        source = source.replace('USE_LLM_MODE = True', 'USE_LLM_MODE = False')

        try:
            exec(source, namespace)
        except Exception as e:
            pass  # Ignore expected errors

    # Get required classes
    ProofState = namespace.get('ProofState')
    ProofAgentGroupChat = namespace.get('ProofAgentGroupChat')
    DEMOS = namespace.get('DEMOS')
    create_agents = namespace.get('create_agents')
    LeanRunner = namespace.get('LeanRunner')
    ProofStateManagerPlugin = namespace.get('ProofStateManagerPlugin')
    LeanSearchPlugin = namespace.get('LeanSearchPlugin')
    LeanTacticPlugin = namespace.get('LeanTacticPlugin')
    LeanVerificationPlugin = namespace.get('LeanVerificationPlugin')

    if not all([ProofState, ProofAgentGroupChat, DEMOS, create_agents]):
        print('Missing required classes:')
        print(f'  ProofState: {ProofState is not None}')
        print(f'  ProofAgentGroupChat: {ProofAgentGroupChat is not None}')
        print(f'  DEMOS: {DEMOS is not None}')
        print(f'  create_agents: {create_agents is not None}')
        return False

    print('=' * 70)
    print('TESTING ALL 4 DEMOS IN SIMULATION MODE')
    print('=' * 70)

    results = []
    for i, demo in enumerate(DEMOS):
        print()
        print('=' * 70)
        print(f'DEMO {i+1}/4: {demo["name"]}')
        print('=' * 70)
        print(f'Theoreme: {demo["theorem"]}')
        print(f'Attendu: {demo["expected_iterations"]} iterations')
        print('=' * 70)

        # Create state
        goal = demo['theorem'].split(':')[-1].strip() if ':' in demo['theorem'] else ''
        state = ProofState(
            theorem_statement=demo['theorem'],
            current_goal=goal,
            max_iterations=15
        )

        # Create runner and plugins
        runner = LeanRunner(backend='subprocess', timeout=30)
        plugins = {
            'state': ProofStateManagerPlugin(state),
            'search': LeanSearchPlugin(runner),
            'tactic': LeanTacticPlugin(),
            'verification': LeanVerificationPlugin(runner)
        }

        # Create agents with simulation=True
        agents = create_agents(plugins, state, use_sk=False, use_simulation=True)

        # Create chat
        chat = ProofAgentGroupChat(agents=agents, state=state, use_sk=False)

        # Run
        result = chat.run(f'Prouver: {demo["theorem"]}', verbose=True)

        results.append({
            'name': demo['name'],
            'expected': demo['expected_iterations'],
            'actual': state.iteration_count,
            'success': state.proof_complete,
            'proof': state.final_proof
        })

    print()
    print('=' * 70)
    print('SUMMARY')
    print('=' * 70)
    all_ok = True
    for r in results:
        status = 'OK' if r['success'] else 'FAIL'
        if not r['success']:
            all_ok = False
        print(f'{r["name"]}: {status} - {r["actual"]} iterations (expected: {r["expected"]})')
        if r['success']:
            print(f'  Proof: {r["proof"]}')

    return all_ok


if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)
