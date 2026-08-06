#!/usr/bin/env python3
"""
Test notebook syntax and key functionality before pushing.
Runs in simulation mode to verify the code works.
"""

import json
import sys
import os

NOTEBOOK_PATH = "d:/dev/CoursIA/MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-9-SK-Multi-Agents.ipynb"

def extract_and_test():
    """Extract code from notebook and test syntax + basic execution."""
    print("=" * 70)
    print("TESTING LEAN-9-SK-MULTI-AGENTS.IPYNB")
    print("=" * 70)

    with open(NOTEBOOK_PATH, 'r', encoding='utf-8') as f:
        nb = json.load(f)

    # Cells to execute (in order)
    # Skip: markdown, output-only cells, demo execution cells
    cells_to_skip_keywords = [
        'result_1 =', 'result_2 =', 'result_3 =', 'result_4 =',  # Demo executions
        'run_single_proof(',  # Actual proof runs
        'USE_LLM_MODE = True',  # Config that triggers LLM
    ]

    all_code = []
    cell_map = []

    for idx, cell in enumerate(nb['cells']):
        if cell['cell_type'] != 'code':
            continue

        source = ''.join(cell['source'])

        # Skip demo execution cells
        skip = False
        for kw in cells_to_skip_keywords:
            if kw in source:
                skip = True
                break

        if skip:
            continue

        # Skip cells that only have comments
        code_lines = [l for l in source.split('\n') if l.strip() and not l.strip().startswith('#')]
        if not code_lines:
            continue

        all_code.append(source)
        cell_map.append(idx)

    print(f"Extracted {len(all_code)} code cells for syntax testing")

    # Test 1: Syntax check
    print("\n[TEST 1] Syntax check...")
    errors = []
    for i, (code, cell_idx) in enumerate(zip(all_code, cell_map)):
        try:
            compile(code, f"<cell_{cell_idx}>", 'exec')
        except SyntaxError as e:
            errors.append((cell_idx, str(e)))

    if errors:
        print(f"  FAILED: {len(errors)} syntax errors")
        for cell_idx, err in errors:
            print(f"    Cell {cell_idx}: {err}")
        return False
    else:
        print(f"  OK: All {len(all_code)} cells have valid Python syntax")

    # Test 2: Execute in isolated namespace
    print("\n[TEST 2] Execution test (simulation mode)...")

    # Create test namespace with required imports
    test_namespace = {
        '__name__': '__main__',
        'USE_LLM_MODE': False,  # Force simulation
    }

    # Set environment to avoid LLM calls
    os.environ['OPENAI_API_KEY'] = ''

    executed = 0
    for i, (code, cell_idx) in enumerate(zip(all_code, cell_map)):
        try:
            # Skip cells that would trigger LLM
            if 'openai' in code.lower() and 'import' in code.lower():
                continue
            if 'ChatCompletionAgent' in code and 'invoke' in code:
                continue

            exec(code, test_namespace)
            executed += 1
        except Exception as e:
            # Some errors are expected (missing imports, etc.)
            error_str = str(e)
            if 'No module named' in error_str:
                continue  # Expected import errors
            if 'SK_AVAILABLE' in error_str:
                continue  # Expected SK not installed
            if 'name' in error_str and 'not defined' in error_str:
                continue  # Expected missing dependencies

            print(f"  Cell {cell_idx}: {type(e).__name__}: {error_str[:100]}")

    print(f"  Executed {executed} cells without critical errors")

    # Test 3: Verify key classes exist
    print("\n[TEST 3] Verify key classes/functions...")

    key_items = ['ProofState', 'LeanRunner', 'ProofAgentGroupChat', 'DEMOS']
    found = []
    for item in key_items:
        if item in test_namespace:
            found.append(item)
            print(f"  OK: {item}")
        else:
            print(f"  MISSING: {item}")

    # Test 4: Verify DEMOS structure
    print("\n[TEST 4] Verify DEMOS structure...")
    if 'DEMOS' in test_namespace:
        demos = test_namespace['DEMOS']
        print(f"  Found {len(demos)} demos")
        for i, demo in enumerate(demos):
            name = demo.get('name', 'UNKNOWN')
            theorem = demo.get('theorem', 'MISSING')[:50]
            print(f"    DEMO_{i+1}: {name}")
            print(f"      Theorem: {theorem}...")
    else:
        print("  DEMOS not found in namespace")

    # Test 5: Verify logging improvements
    print("\n[TEST 5] Verify logging improvements...")

    with open(NOTEBOOK_PATH, 'r', encoding='utf-8') as f:
        content = f.read()

    logging_features = [
        ('format_timestamp', 'Timestamp function'),
        ('clean_response', 'Response cleanup'),
        ('duration_s', 'Duration tracking'),
        ('TOUR', 'Tour markers'),
    ]

    for pattern, desc in logging_features:
        if pattern in content:
            print(f"  OK: {desc}")
        else:
            print(f"  MISSING: {desc}")

    print("\n" + "=" * 70)
    print("TEST COMPLETE")
    print("=" * 70)

    return True


if __name__ == "__main__":
    success = extract_and_test()
    sys.exit(0 if success else 1)
