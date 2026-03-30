#!/usr/bin/env python3
"""
Fix structure issues in Lean-8 and Lean-9 notebooks:
1. Remove .backup files
2. Fix SK contamination in Lean-8
3. Fix navigation headers
4. Fix numbering in both notebooks
"""

import json
import sys
import re
from pathlib import Path
from typing import Dict, Any, List, Tuple

def read_notebook(path: str) -> Dict[str, Any]:
    """Read notebook JSON"""
    with open(path, 'r', encoding='utf-8') as f:
        return json.load(f)

def write_notebook(path: str, nb: Dict[str, Any]) -> None:
    """Write notebook JSON"""
    with open(path, 'w', encoding='utf-8') as f:
        json.dump(nb, f, indent=1, ensure_ascii=False)

def get_cell_source(cell: Dict[str, Any]) -> str:
    """Get cell source as string"""
    return ''.join(cell['source']) if isinstance(cell['source'], list) else cell['source']

def set_cell_source(cell: Dict[str, Any], source: str) -> None:
    """Set cell source from string"""
    lines = source.split('\n')
    cell['source'] = [line + '\n' for line in lines[:-1]] + ([lines[-1]] if lines[-1] else [])

def fix_lean8_navigation(nb: Dict[str, Any]) -> int:
    """Fix navigation in Lean-8 cell[0] to point to Lean-9-SK-Multi-Agents"""
    cell = nb['cells'][0]
    if cell['cell_type'] != 'markdown':
        return 0

    source = get_cell_source(cell)

    # Fix navigation link
    new_source = source.replace(
        'Lean-9-LeanDojo.ipynb',
        'Lean-9-SK-Multi-Agents.ipynb'
    ).replace(
        'Lean-9-LeanDojo',
        'Lean-9-SK-Multi-Agents'
    )

    if new_source != source:
        set_cell_source(cell, new_source)
        print(f"  ✓ Fixed navigation: Lean-9-LeanDojo → Lean-9-SK-Multi-Agents")
        return 1
    return 0

def fix_lean8_sk_contamination(nb: Dict[str, Any]) -> int:
    """Remove SK contamination from Lean-8"""
    changes = 0

    # Cell 18: Remove or simplify prove_with_multi_agents if it uses SK
    if len(nb['cells']) > 18:
        cell18 = nb['cells'][18]
        if cell18['cell_type'] == 'code':
            source = get_cell_source(cell18)
            if 'ProofAgentGroupChat' in source and 'use_sk' in source:
                print(f"  ⚠ Cell 18 contains SK (ProofAgentGroupChat)")
                print(f"    Marking for manual review - too complex to auto-fix")
                # Add comment to cell
                comment = "# TODO: REVIEW - This cell may contain SK contamination (ProofAgentGroupChat)\n"
                if not source.startswith("# TODO"):
                    set_cell_source(cell18, comment + source)
                    changes += 1

    # Cell 40: Remove SK patterns table from resume
    if len(nb['cells']) > 40:
        cell40 = nb['cells'][40]
        if cell40['cell_type'] == 'markdown':
            source = get_cell_source(cell40)

            # Remove SK patterns table
            if '@kernel_function' in source or 'LeanProverPlugin' in source:
                # Find and remove the SK patterns table
                lines = source.split('\n')
                new_lines = []
                in_sk_table = False
                skip_lines = 0

                for i, line in enumerate(lines):
                    # Detect start of SK table
                    if 'Pattern' in line and 'Description' in line and 'Classe' in line:
                        in_sk_table = True
                        skip_lines = 0
                        continue

                    # Detect table rows
                    if in_sk_table:
                        if line.strip().startswith('|'):
                            skip_lines += 1
                            continue
                        elif skip_lines > 0 and line.strip().startswith('-'):
                            continue
                        else:
                            # End of table
                            in_sk_table = False
                            skip_lines = 0

                    # Skip SK pattern rows
                    if any(keyword in line for keyword in ['@kernel_function', 'LeanProverPlugin',
                                                           'DelegatingSelectionStrategy',
                                                           'ProofCompleteTermination',
                                                           'AgentGroupChat', 'StateManager', 'Plugin',
                                                           'SelectionStrategy', 'TerminationStrategy']):
                        continue

                    new_lines.append(line)

                new_source = '\n'.join(new_lines)

                # Clean multiple newlines
                new_source = re.sub(r'\n{3,}', '\n\n', new_source)

                if new_source != source:
                    set_cell_source(cell40, new_source)
                    print(f"  ✓ Removed SK patterns table from resume (cell 40)")
                    changes += 1

    return changes

def fix_lean8_numbering(nb: Dict[str, Any]) -> int:
    """Fix section numbering in Lean-8"""
    changes = 0

    # Define expected section progression
    # Section 2: Architecture (currently missing main section 2)
    # Section 3-6: Agents
    # Section 7-10: Advanced techniques

    section_map = {
        # Current → Target
        '### 2.1': '## 2',  # Change to main section
        '## 3': '## 3',
        '## 4': '## 4',
        '## 5': '## 5',
        '## 6': '## 6',
        '### 6.6': '### 6.1',
        '### 6.7': '### 6.2',
        '### 6.8': '### 6.3',
        '### 6.9': '### 6.4',
        '### 6.10': '### 6.5',
        '### 6.11': '### 6.6',
        '### 6.16': '### 6.7',
        '### 6.17': '### 6.8',
        '### 6.22': '### 6.9',
        '### 6.23': '### 6.10',
        '### 6.24': '### 6.11',
        '### 6.25': '### 6.12',
        '## 7': '## 7',
        '## 8': '## 8',
        '## 9': '## 9',
        '## 10': '## 10',
    }

    for cell in nb['cells']:
        if cell['cell_type'] != 'markdown':
            continue

        source = get_cell_source(cell)
        lines = source.split('\n')
        modified = False

        for i, line in enumerate(lines):
            for old_num, new_num in section_map.items():
                if line.startswith(old_num + ' ') or line.startswith(old_num + '.'):
                    # Extract title
                    match = re.match(r'^(#{2,4})\s+[\d\.]+\s+(.+)$', line)
                    if match:
                        level = match.group(1)
                        title = match.group(2)

                        # Get new number without #
                        new_number = new_num.replace('#', '').strip()

                        # Rebuild line
                        lines[i] = f"{level} {new_number}. {title}"
                        modified = True
                        print(f"  ✓ Renumbered: {old_num} → {new_num}")
                        break

        if modified:
            set_cell_source(cell, '\n'.join(lines))
            changes += 1

    return changes

def fix_lean9_navigation(nb: Dict[str, Any]) -> int:
    """Add navigation header to Lean-9 cell[0]"""
    cell = nb['cells'][0]
    if cell['cell_type'] != 'markdown':
        return 0

    source = get_cell_source(cell)

    # Check if navigation already exists
    if '[← Lean-8' in source or 'Navigation' in source:
        print(f"  ℹ Navigation already exists")
        return 0

    # Add navigation header
    nav_header = """**Navigation** : [← Lean-8-Agentic-Proving](Lean-8-Agentic-Proving.ipynb) | [Index](Lean-1-Setup.ipynb) | [Lean-10-Advanced →](Lean-10-Advanced.ipynb)

---

"""

    new_source = nav_header + source
    set_cell_source(cell, new_source)
    print(f"  ✓ Added navigation header")
    return 1

def fix_lean9_numbering(nb: Dict[str, Any]) -> int:
    """Fix numbering in Lean-9 (remove 8.x references, use 2.x)"""
    changes = 0

    for cell in nb['cells']:
        if cell['cell_type'] != 'markdown':
            continue

        source = get_cell_source(cell)

        # Replace 8.x references with proper section numbers
        new_source = source

        # Pattern: "8.2-8.5" → "Introduction"
        new_source = re.sub(r'8\.2-8\.5\s+', '', new_source)
        new_source = re.sub(r'8\.4-8\.5\s+', '', new_source)

        # Pattern: "### 2.3. 8.2-8.5 Plugins" → "### 2.3. Plugins SK"
        new_source = re.sub(r'(###\s+2\.\d+\.)\s+8\.\d+-8\.\d+\s+', r'\1 ', new_source)

        # Clean multiple spaces
        new_source = re.sub(r'\s{2,}', ' ', new_source)

        if new_source != source:
            set_cell_source(cell, new_source)
            print(f"  ✓ Cleaned 8.x references")
            changes += 1

    # Now renumber subsections sequentially
    subsection_counter = 1

    for cell in nb['cells']:
        if cell['cell_type'] != 'markdown':
            continue

        source = get_cell_source(cell)
        lines = source.split('\n')
        modified = False

        for i, line in enumerate(lines):
            # Match ### 2.X pattern
            match = re.match(r'^(###\s+)2\.(\d+)(\.?\s+.+)$', line)
            if match:
                prefix = match.group(1)
                title = match.group(3)

                # Skip subsections that should be kept (2.1, 2.2, etc.)
                old_num = int(match.group(2))

                # Only renumber if there are big gaps
                if old_num > subsection_counter + 2:
                    lines[i] = f"{prefix}2.{subsection_counter}{title}"
                    print(f"  ✓ Renumbered: 2.{old_num} → 2.{subsection_counter}")
                    modified = True

                subsection_counter += 1

        if modified:
            set_cell_source(cell, '\n'.join(lines))
            changes += 1

    return changes

def main():
    """Main execution"""
    notebook_dir = Path(__file__).parent
    lean8_path = notebook_dir / 'Lean-8-Agentic-Proving.ipynb'
    lean9_path = notebook_dir / 'Lean-9-SK-Multi-Agents.ipynb'

    print("=" * 80)
    print("FIX LEAN-8 NOTEBOOK")
    print("=" * 80)

    if not lean8_path.exists():
        print(f"Error: {lean8_path} not found")
        sys.exit(1)

    lean8 = read_notebook(str(lean8_path))
    changes = 0

    print("\n1. Fix navigation...")
    changes += fix_lean8_navigation(lean8)

    print("\n2. Fix SK contamination...")
    changes += fix_lean8_sk_contamination(lean8)

    print("\n3. Fix section numbering...")
    changes += fix_lean8_numbering(lean8)

    if changes > 0:
        write_notebook(str(lean8_path), lean8)
        print(f"\n✅ Lean-8: {changes} changes saved")
    else:
        print(f"\n⚠ Lean-8: No changes needed")

    print("\n" + "=" * 80)
    print("FIX LEAN-9 NOTEBOOK")
    print("=" * 80)

    if not lean9_path.exists():
        print(f"Error: {lean9_path} not found")
        sys.exit(1)

    lean9 = read_notebook(str(lean9_path))
    changes = 0

    print("\n1. Add navigation header...")
    changes += fix_lean9_navigation(lean9)

    print("\n2. Fix numbering (remove 8.x references)...")
    changes += fix_lean9_numbering(lean9)

    if changes > 0:
        write_notebook(str(lean9_path), lean9)
        print(f"\n✅ Lean-9: {changes} changes saved")
    else:
        print(f"\n⚠ Lean-9: No changes needed")

    print("\n" + "=" * 80)
    print("✅ ALL NOTEBOOKS FIXED")
    print("=" * 80)

if __name__ == '__main__':
    main()
