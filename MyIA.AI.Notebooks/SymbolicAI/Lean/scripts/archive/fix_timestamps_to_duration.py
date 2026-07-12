#!/usr/bin/env python3
"""
Replace timestamps with execution durations in Lean-9 notebook.
"""

import json

NOTEBOOK_PATH = "d:/dev/CoursIA/MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-9-SK-Multi-Agents.ipynb"


def main():
    with open(NOTEBOOK_PATH, 'r', encoding='utf-8') as f:
        nb = json.load(f)

    cell = nb['cells'][32]
    source = ''.join(cell['source'])

    changes = []

    # Replace PREUVE TROUVEE with elapsed time
    old_preuve = 'print(f"\\n[{format_timestamp()}] PREUVE TROUVEE!")'
    new_preuve = 'elapsed = (datetime.now() - session_start).total_seconds(); print(f"\\n[+{elapsed:.2f}s] PREUVE TROUVEE!")'

    if old_preuve in source:
        source = source.replace(old_preuve, new_preuve)
        changes.append("PREUVE TROUVEE timestamps")

    # Save
    lines = source.split('\n')
    nb['cells'][32]['source'] = [line + '\n' for line in lines[:-1]] + [lines[-1]]

    with open(NOTEBOOK_PATH, 'w', encoding='utf-8') as f:
        json.dump(nb, f, indent=1, ensure_ascii=False)

    # Verify
    source2 = ''.join(nb['cells'][32]['source'])
    remaining = source2.count('format_timestamp()')
    # Subtract 2 for the function definitions
    usage_count = remaining - 2

    print(f"Changes: {changes}")
    print(f"Remaining format_timestamp() usages (excluding definitions): {usage_count}")


if __name__ == "__main__":
    main()
