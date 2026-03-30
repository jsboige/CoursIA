#!/usr/bin/env python3
"""
Demo Manager for Lean-9 Multi-Agent Notebook.

Centralized tool for managing DEMO definitions and notebook cells.
Replaces: reorder_demos.py, reorganize_demos.py, update_demos_*.py, fix_demos_config.py

Commands:
    show        - Display current demo configuration
    update      - Update notebook cells with current demo definitions
    reorder     - Reorder demos (e.g., swap positions)
    add         - Add a new demo definition
    set-theorem - Change theorem for a specific demo

Usage:
    python demo_manager.py show
    python demo_manager.py update
    python demo_manager.py reorder 2 3  # Swap DEMO_2 and DEMO_3
    python demo_manager.py set-theorem 4 "theorem foo : ..."
"""

import json
import sys
import argparse
from pathlib import Path
from typing import List, Dict, Any, Optional
from dataclasses import dataclass, field, asdict


# =============================================================================
# Configuration
# =============================================================================

NOTEBOOK_PATH = Path(__file__).parent.parent / "Lean-9-SK-Multi-Agents.ipynb"

# Cell indices in the notebook (0-indexed)
CELL_INDICES = {
    'intro': 35,           # "## 4. Demonstrations Progressives"
    'demo1_md': 38,
    'demo1_code': 39,
    'demo2_md': 40,
    'demo2_code': 41,
    'demo3_md': 42,
    'demo3_code': 43,
    'demo4_md': 44,
    'demo4_code': 45,
    'comparison': 47,
}


# =============================================================================
# Demo Definitions
# =============================================================================

@dataclass
class DemoDefinition:
    """Definition of a single demo theorem."""
    num: int
    name: str
    theorem: str
    expected_iterations: int
    expected_lemmas: int
    complexity: str
    strategy: str
    md_title: str
    md_objective: str
    md_behavior: str

    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)


# Default demo definitions - edit these to change demos
DEFAULT_DEMOS = [
    DemoDefinition(
        num=1,
        name="DEMO_1_REFLEXIVITY",
        theorem="theorem demo_rfl (n : Nat) : n = n",
        expected_iterations=2,
        expected_lemmas=0,
        complexity="Triviale - rfl suffit",
        strategy="rfl",
        md_title="### 4.1. DEMO_1 : Reflexivite Pure",
        md_objective="Valider le pipeline complet avec un theoreme trivial",
        md_behavior="1-2 iterations : `rfl` suffit immediatement"
    ),
    DemoDefinition(
        num=2,
        name="DEMO_2_DISTRIBUTIVITY",
        theorem="theorem add_mul_distrib (a b c : Nat) : a * c + b * c = (a + b) * c",
        expected_iterations=5,
        expected_lemmas=1,
        complexity="Simple - forme inversee du lemme standard",
        strategy="rw [<- Nat.add_mul]",
        md_title="### 4.2. DEMO_2 : Distributivite Inversee",
        md_objective="Montrer la recherche de lemme avec reecriture inversee",
        md_behavior="4-6 iterations : recherche `Nat.add_mul`, reecriture inversee"
    ),
    DemoDefinition(
        num=3,
        name="DEMO_3_MUL_COMM",
        theorem="theorem mul_comm_manual (m n : Nat) : m * n = n * m",
        expected_iterations=8,
        expected_lemmas=2,
        complexity="Intermediaire - necessite lemme de commutativite",
        strategy="exact Nat.mul_comm m n",
        md_title="### 4.3. DEMO_3 : Commutativite Multiplication",
        md_objective="Tester une propriete fondamentale avec recherche",
        md_behavior="6-10 iterations : decouverte de `Nat.mul_comm`"
    ),
    DemoDefinition(
        num=4,
        name="DEMO_4_POWER_ADD",
        theorem="theorem pow_add_manual (a m n : Nat) : a ^ (m + n) = a ^ m * a ^ n",
        expected_iterations=15,
        expected_lemmas=4,
        complexity="Avancee - induction et lemmes auxiliaires multiples",
        strategy="induction n avec Nat.pow_succ, Nat.mul_assoc",
        md_title="### 4.4. DEMO_4 : Addition des Puissances",
        md_objective="Stresser le systeme avec induction et lemmes multiples",
        md_behavior="12-18 iterations : induction sur n, decouverte de pow_succ, mul_assoc"
    ),
]


# =============================================================================
# Cell Generation
# =============================================================================

def generate_markdown_cell(demo: DemoDefinition) -> str:
    """Generate markdown cell content for a demo."""
    return f"""{demo.md_title}

**Objectif** : {demo.md_objective}

**Theoreme** : `{demo.theorem}`

**Comportement attendu** : {demo.md_behavior}
"""


def generate_code_cell(demo: DemoDefinition) -> str:
    """Generate code cell content for a demo."""
    short_name = demo.name.replace(f"DEMO_{demo.num}_", "")
    return f'''# =============================================================================
# DEMO_{demo.num} : {short_name}
# =============================================================================

# Definition inline pour iteration independante
demo_{demo.num} = {{
    "name": "{demo.name}",
    "theorem": "{demo.theorem}",
    "expected_iterations": {demo.expected_iterations},
    "expected_lemmas": {demo.expected_lemmas},
    "complexity": "{demo.complexity}",
    "strategy": "{demo.strategy}"
}}

print("\\n" + "=" * 70)
print(f"DEMO {demo.num}/4: {{demo_{demo.num}['name']}}")
print("=" * 70)
print(f"Theoreme: {{demo_{demo.num}['theorem']}}")
print(f"Complexite: {{demo_{demo.num}['complexity']}}")
print(f"Iterations attendues: {{demo_{demo.num}['expected_iterations']}}")
print("=" * 70)

result_{demo.num} = prove_with_multi_agents(
    theorem=demo_{demo.num}["theorem"],
    max_iterations=20,
    verbose=True,
    use_simulation=not USE_LLM_MODE
)

print(f"\\nResultat DEMO_{demo.num}:")
print(f"  - Success: {{result_{demo.num}['success']}}")
print(f"  - Iterations: {{result_{demo.num}['iterations']}} (attendu: {{demo_{demo.num}['expected_iterations']}})")
print(f"  - Proof: {{result_{demo.num}['final_proof']}}"))'''


def generate_intro_cell(demos: List[DemoDefinition]) -> str:
    """Generate the intro markdown cell with table."""
    rows = []
    for d in demos:
        # Extract short theorem representation
        theorem_short = d.theorem.split(':')[-1].strip() if ':' in d.theorem else d.theorem
        if len(theorem_short) > 25:
            theorem_short = theorem_short[:22] + "..."
        rows.append(f"| DEMO_{d.num} | `{theorem_short}` | {d.complexity.split(' - ')[0]} | {d.expected_iterations} | {d.strategy.split()[0]} |")

    table = '\n'.join(rows)

    return f'''## 4. Demonstrations Progressives

Les 4 demonstrations suivantes illustrent le fonctionnement du systeme multi-agents avec une progression de complexite croissante :

| Demo | Theoreme | Complexite | Iterations | Technique |
|------|----------|------------|------------|-----------|
{table}

**Progression pedagogique** :
- DEMO_1 : Validation du pipeline (cas trivial)
- DEMO_2 : Introduction de la recherche de lemmes
- DEMO_3 : Propriete fondamentale avec `exact`
- DEMO_4 : Stress-test avec induction complexe
'''


def generate_comparison_cell(demos: List[DemoDefinition]) -> str:
    """Generate the comparison cell."""
    demos_info_lines = []
    for d in demos:
        theorem_short = d.theorem.split(':')[-1].strip() if ':' in d.theorem else d.theorem
        if len(theorem_short) > 20:
            theorem_short = theorem_short[:17] + "..."
        demos_info_lines.append(
            f'    {{"name": "{d.name}", "theorem": "{theorem_short}", '
            f'"expected_iter": {d.expected_iterations}, "expected_lemmas": {d.expected_lemmas}}},'
        )

    demos_info = '\n'.join(demos_info_lines)

    progression_lines = []
    for d in demos:
        short_name = d.name.replace(f"DEMO_{d.num}_", "").capitalize()
        progression_lines.append(f'print("DEMO_{d.num}: {short_name:<15} -> {d.strategy}")')

    progression = '\n'.join(progression_lines)

    return f'''# =============================================================================
# Comparaison des Resultats
# =============================================================================

print("\\n" + "=" * 70)
print("COMPARAISON DES RESULTATS")
print("=" * 70)

# Definitions inline pour iteration independante
demos_info = [
{demos_info}
]

results = [result_1, result_2, result_3, result_4]

print(f"{{'Demo':<25}} {{'Success':<10}} {{'Iter':<12}} {{'Lemmas':<10}} {{'Status':<15}}")
print("-" * 72)

for i, (demo, result) in enumerate(zip(demos_info, results), 1):
    success_str = "OK" if result["success"] else "FAILED"
    iter_str = f"{{result['iterations']}}/{{demo['expected_iter']}}"
    lemmas_str = f"{{result.get('lemmas_found', 0)}}/{{demo['expected_lemmas']}}"

    if result["success"]:
        if result["iterations"] <= demo["expected_iter"]:
            status = "Optimal"
        else:
            status = "Slow"
    else:
        status = "Failed"

    print(f"{{demo['name']:<25}} {{success_str:<10}} {{iter_str:<12}} {{lemmas_str:<10}} {{status:<15}}")

print("-" * 72)
total_success = sum(1 for r in results if r["success"])
print(f"Total: {{total_success}}/4 reussies")

# Resume de la progression
print("\\n" + "=" * 70)
print("PROGRESSION DE COMPLEXITE")
print("=" * 70)
{progression}'''


# =============================================================================
# Notebook Operations
# =============================================================================

def source_to_lines(source: str) -> List[str]:
    """Convert source string to Jupyter source list format."""
    lines = source.split('\n')
    return [line + '\n' if i < len(lines) - 1 else line for i, line in enumerate(lines)]


def update_cell(cells: List[Dict], index: int, source: str, description: str = ""):
    """Update a cell's source."""
    cells[index]['source'] = source_to_lines(source)
    print(f"  Updated cell {index}: {description}")


def load_notebook() -> Dict:
    """Load the notebook."""
    with open(NOTEBOOK_PATH, 'r', encoding='utf-8') as f:
        return json.load(f)


def save_notebook(notebook: Dict):
    """Save the notebook."""
    with open(NOTEBOOK_PATH, 'w', encoding='utf-8') as f:
        json.dump(notebook, f, indent=1, ensure_ascii=False)


# =============================================================================
# Commands
# =============================================================================

def cmd_show(demos: List[DemoDefinition]):
    """Display current demo configuration."""
    print(f"\n{'='*70}")
    print("CURRENT DEMO CONFIGURATION")
    print(f"{'='*70}\n")

    for d in demos:
        print(f"DEMO_{d.num}: {d.name}")
        print(f"  Theorem:    {d.theorem}")
        print(f"  Iterations: {d.expected_iterations}")
        print(f"  Lemmas:     {d.expected_lemmas}")
        print(f"  Complexity: {d.complexity}")
        print(f"  Strategy:   {d.strategy}")
        print()

    print(f"{'='*70}")
    print(f"Notebook: {NOTEBOOK_PATH}")
    print(f"{'='*70}\n")


def cmd_update(demos: List[DemoDefinition], dry_run: bool = False):
    """Update notebook cells with current demo definitions."""
    print(f"\n{'='*70}")
    print(f"UPDATING NOTEBOOK{'  (dry-run)' if dry_run else ''}")
    print(f"{'='*70}\n")

    if not dry_run:
        notebook = load_notebook()
        cells = notebook['cells']

    changes = 0

    # Update intro cell
    intro_source = generate_intro_cell(demos)
    if not dry_run:
        update_cell(cells, CELL_INDICES['intro'], intro_source, "Intro table")
    else:
        print(f"  Would update cell {CELL_INDICES['intro']}: Intro table")
    changes += 1

    # Update each demo's markdown and code cells
    for i, demo in enumerate(demos, 1):
        md_key = f'demo{i}_md'
        code_key = f'demo{i}_code'

        md_source = generate_markdown_cell(demo)
        code_source = generate_code_cell(demo)

        if not dry_run:
            update_cell(cells, CELL_INDICES[md_key], md_source, f"DEMO_{i} markdown")
            update_cell(cells, CELL_INDICES[code_key], code_source, f"DEMO_{i} code")
        else:
            print(f"  Would update cell {CELL_INDICES[md_key]}: DEMO_{i} markdown")
            print(f"  Would update cell {CELL_INDICES[code_key]}: DEMO_{i} code")
        changes += 2

    # Update comparison cell
    comparison_source = generate_comparison_cell(demos)
    if not dry_run:
        update_cell(cells, CELL_INDICES['comparison'], comparison_source, "Comparison")
    else:
        print(f"  Would update cell {CELL_INDICES['comparison']}: Comparison")
    changes += 1

    # Save
    if not dry_run:
        save_notebook(notebook)
        print(f"\nNotebook saved: {NOTEBOOK_PATH}")

    print(f"\nTotal: {changes} cells updated")


def cmd_reorder(demos: List[DemoDefinition], pos1: int, pos2: int) -> List[DemoDefinition]:
    """Swap two demos by position (1-4)."""
    if not (1 <= pos1 <= 4 and 1 <= pos2 <= 4):
        print("Error: Positions must be 1-4")
        return demos

    # Swap in list
    demos[pos1-1], demos[pos2-1] = demos[pos2-1], demos[pos1-1]

    # Update numbers
    for i, d in enumerate(demos, 1):
        d.num = i
        d.md_title = f"### 4.{i}. DEMO_{i} : {d.md_title.split(':')[-1].strip()}"

    print(f"Swapped DEMO_{pos1} and DEMO_{pos2}")
    return demos


# =============================================================================
# Main
# =============================================================================

def main():
    parser = argparse.ArgumentParser(
        description='Demo Manager for Lean-9 notebook',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__
    )
    subparsers = parser.add_subparsers(dest='command', help='Command to run')

    # show command
    subparsers.add_parser('show', help='Display current demo configuration')

    # update command
    update_parser = subparsers.add_parser('update', help='Update notebook cells')
    update_parser.add_argument('--dry-run', action='store_true', help='Show changes without applying')

    # reorder command
    reorder_parser = subparsers.add_parser('reorder', help='Swap two demos')
    reorder_parser.add_argument('pos1', type=int, help='First position (1-4)')
    reorder_parser.add_argument('pos2', type=int, help='Second position (1-4)')

    args = parser.parse_args()

    # Use default demos (edit DEFAULT_DEMOS to change)
    demos = list(DEFAULT_DEMOS)

    if args.command == 'show':
        cmd_show(demos)
    elif args.command == 'update':
        cmd_update(demos, args.dry_run)
    elif args.command == 'reorder':
        demos = cmd_reorder(demos, args.pos1, args.pos2)
        cmd_show(demos)
        print("\nNote: Run 'python demo_manager.py update' to apply to notebook")
    else:
        parser.print_help()


if __name__ == '__main__':
    main()
