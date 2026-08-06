#!/usr/bin/env python3
"""
Renumber all markdown sections in Lean notebooks for coherent progression
"""

import json
import sys
import re
from pathlib import Path
from typing import List, Dict, Any, Tuple

def extract_heading_level(line: str) -> Tuple[int, str]:
    """Extract heading level and title from a markdown line"""
    match = re.match(r'^(#{2,6})\s+(.+)$', line)
    if match:
        level = len(match.group(1))
        title = match.group(2)
        return level, title
    return 0, line

def renumber_notebook_sections(notebook_path: str, verbose: bool = True) -> None:
    """Renumber all markdown sections in a notebook"""

    if verbose:
        print(f"Processing: {notebook_path}")

    with open(notebook_path, 'r', encoding='utf-8') as f:
        nb = json.load(f)

    # Track section numbers
    section_counters = {
        2: 0,  # ## Main sections
        3: 0,  # ### Subsections
        4: 0,  # #### Sub-subsections
    }

    modified_count = 0

    for idx, cell in enumerate(nb['cells']):
        if cell['cell_type'] != 'markdown':
            continue

        source = ''.join(cell['source']) if isinstance(cell['source'], list) else cell['source']
        lines = source.split('\n')
        modified = False

        new_lines = []
        for line in lines:
            level, title = extract_heading_level(line)

            if level >= 2 and level <= 4:
                # Remove existing numbering (patterns like "1.", "8.2", "8.7.1")
                title_clean = re.sub(r'^[\d\.]+\s+', '', title)

                # Skip emoji-only titles
                if re.match(r'^[\U0001F300-\U0001F9FF]+\s*', title_clean):
                    new_lines.append(line)
                    continue

                # Increment counter at this level
                if level == 2:
                    section_counters[2] += 1
                    section_counters[3] = 0  # Reset subsections
                    section_counters[4] = 0
                    new_number = f"{section_counters[2]}"
                elif level == 3:
                    section_counters[3] += 1
                    section_counters[4] = 0
                    new_number = f"{section_counters[2]}.{section_counters[3]}"
                elif level == 4:
                    section_counters[4] += 1
                    new_number = f"{section_counters[2]}.{section_counters[3]}.{section_counters[4]}"

                # Reconstruct line
                new_line = f"{'#' * level} {new_number}. {title_clean}"
                new_lines.append(new_line)
                modified = True

                if verbose:
                    print(f"  Cell {idx}: {line.strip()} → {new_line.strip()}")
            else:
                new_lines.append(line)

        if modified:
            # Update cell source
            new_source = '\n'.join(new_lines)
            cell['source'] = new_source.split('\n')
            # Add newlines back (except last line)
            cell['source'] = [line + '\n' for line in cell['source'][:-1]] + [cell['source'][-1]]
            modified_count += 1

    if modified_count > 0:
        # Save backup
        backup_path = notebook_path + '.renumber.backup'
        if verbose:
            print(f"\nCreating backup: {backup_path}")
        with open(backup_path, 'w', encoding='utf-8') as f:
            json.dump(nb, f, indent=1, ensure_ascii=False)

        # Save renumbered notebook
        if verbose:
            print(f"Saving renumbered notebook: {notebook_path}")
        with open(notebook_path, 'w', encoding='utf-8') as f:
            json.dump(nb, f, indent=1, ensure_ascii=False)

        if verbose:
            print(f"\n✅ Renumbered {modified_count} cells")
            print(f"   Main sections: {section_counters[2]}")
            print(f"   Last subsection: {section_counters[3]}")
    else:
        if verbose:
            print("\n⚠ No changes needed")

if __name__ == '__main__':
    notebook_dir = Path(__file__).parent

    # Process both notebooks
    lean8_path = notebook_dir / 'Lean-8-Agentic-Proving.ipynb'
    lean9_path = notebook_dir / 'Lean-9-SK-Multi-Agents.ipynb'

    print("=" * 100)
    print("RENUMBERING LEAN-8")
    print("=" * 100)
    if lean8_path.exists():
        renumber_notebook_sections(str(lean8_path))
    else:
        print(f"Error: {lean8_path} not found")

    print("\n" + "=" * 100)
    print("RENUMBERING LEAN-9")
    print("=" * 100)
    if lean9_path.exists():
        renumber_notebook_sections(str(lean9_path))
    else:
        print(f"Error: {lean9_path} not found")

    print("\n" + "=" * 100)
    print("✅ ALL NOTEBOOKS RENUMBERED")
    print("=" * 100)
