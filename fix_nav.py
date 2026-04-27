#!/usr/bin/env python3
"""Fix broken navigation links and title mismatches across CoursIA notebooks.

Affected files:
- CSP-1, CSP-2, CSP-3, CSP-8: old Search-N references
- Search-5, Search-8, Search-9, Search-10, Search-11: wrong titles / wrong nav links
"""
import json
import re

def load_nb(path):
    with open(path, 'r', encoding='utf-8') as f:
        return json.load(f)

def save_nb(path, nb):
    with open(path, 'w', encoding='utf-8') as f:
        json.dump(nb, f, ensure_ascii=False, indent=1)
        f.write('\n')

def fix_cell_source(cell, replacements):
    """Apply list of (old, new) string replacements to cell source."""
    src = ''.join(cell['source'])
    changed = False
    for old, new in replacements:
        if old in src:
            src = src.replace(old, new)
            changed = True
    if changed:
        # Rebuild source as list of lines (preserve original line structure)
        cell['source'] = [line + '\n' for line in src.split('\n')[:-1]] + [src.split('\n')[-1]]
        # Remove trailing empty newline artifact
        if cell['source'] and cell['source'][-1] == '\n':
            cell['source'] = cell['source'][:-1]
    return changed

changes_log = []

# ============================================================
# CSP-1-Fundamentals.ipynb
# ============================================================
path = 'MyIA.AI.Notebooks/Search/Part2-CSP/CSP-1-Fundamentals.ipynb'
nb = load_nb(path)

# cell 0 (header/nav): Search-7 CSP-Consistency links
replacements_csp1 = [
    ('[Search-7 CSP-Consistency >>](Search-7-CSP-Consistency.ipynb)',
     '[CSP-2 Consistency >>](CSP-2-Consistency.ipynb)'),
    ('[Search-7 CSP-Consistency](Search-7-CSP-Consistency.ipynb)',
     '[CSP-2 Consistency](CSP-2-Consistency.ipynb)'),
]
for i in [0, 66, 69]:
    if fix_cell_source(nb['cells'][i], replacements_csp1):
        changes_log.append(f'CSP-1 cell {i}: fixed CSP-Consistency link')

save_nb(path, nb)
print(f'Fixed CSP-1: {sum(1 for _ in changes_log if "CSP-1" in _)} changes')

# ============================================================
# CSP-2-Consistency.ipynb
# ============================================================
path = 'MyIA.AI.Notebooks/Search/Part2-CSP/CSP-2-Consistency.ipynb'
nb = load_nb(path)

replacements_csp2 = [
    ('[<< Search-6 CSP-Fundamentals](Search-6-CSP-Fundamentals.ipynb)',
     '[<< CSP-1 Fundamentals](CSP-1-Fundamentals.ipynb)'),
    ('[Search-8 CSP-Advanced >>](Search-8-CSP-Advanced.ipynb)',
     '[CSP-3 Advanced >>](CSP-3-Advanced.ipynb)'),
    ('[Search-8-CSP-Advanced](Search-8-CSP-Advanced.ipynb)',
     '[CSP-3-Advanced](CSP-3-Advanced.ipynb)'),
    # Prose references
    ('dans le notebook precedent (Search-6)',
     'dans le notebook precedent (CSP-1)'),
    ('rappel de Search-6',
     'rappel de CSP-1'),
]
for i in [0, 1, 3, 61]:
    if i < len(nb['cells']):
        if fix_cell_source(nb['cells'][i], replacements_csp2):
            changes_log.append(f'CSP-2 cell {i}: fixed Search-6/8 references')

save_nb(path, nb)
print(f'Fixed CSP-2: {sum(1 for _ in changes_log if "CSP-2" in _)} changes')

# ============================================================
# CSP-3-Advanced.ipynb
# ============================================================
path = 'MyIA.AI.Notebooks/Search/Part2-CSP/CSP-3-Advanced.ipynb'
nb = load_nb(path)

replacements_csp3 = [
    ('[<< Search-7 CSP-Consistency](Search-7-CSP-Consistency.ipynb)',
     '[<< CSP-2 Consistency](CSP-2-Consistency.ipynb)'),
    # Prose references
    ('(Search-6 et Search-7)',
     '(CSP-1 et CSP-2)'),
    ('(Search-6/7)',
     '(CSP-1/2)'),
    ('Search-6/7',
     'CSP-1/2'),
]
for i in [0, 1]:
    if i < len(nb['cells']):
        if fix_cell_source(nb['cells'][i], replacements_csp3):
            changes_log.append(f'CSP-3 cell {i}: fixed Search-6/7 references')

save_nb(path, nb)
print(f'Fixed CSP-3: {sum(1 for _ in changes_log if "CSP-3" in _)} changes')

# ============================================================
# CSP-8-Temporal.ipynb
# ============================================================
path = 'MyIA.AI.Notebooks/Search/Part2-CSP/CSP-8-Temporal.ipynb'
nb = load_nb(path)

replacements_csp8 = [
    ('[<< Search-16 CSP-Soft](Search-16-CSP-Soft.ipynb)',
     '[<< CSP-7 Soft](CSP-7-Soft.ipynb)'),
    ('[Search-18 CSP-Distributed >>](Search-18-CSP-Distributed.ipynb)',
     '[CSP-9 Distributed >>](CSP-9-Distributed.ipynb)'),
    ('[Search-16 CSP-Soft](Search-16-CSP-Soft.ipynb)',
     '[CSP-7 Soft](CSP-7-Soft.ipynb)'),
    ('[Search-18 CSP-Distributed](Search-18-CSP-Distributed.ipynb)',
     '[CSP-9 Distributed](CSP-9-Distributed.ipynb)'),
    ('Search-18 CSP-Distributed',
     'CSP-9 Distributed'),
]
for i in [0, 25]:
    if i < len(nb['cells']):
        if fix_cell_source(nb['cells'][i], replacements_csp8):
            changes_log.append(f'CSP-8 cell {i}: fixed Search-16/18 references')

save_nb(path, nb)
print(f'Fixed CSP-8: {sum(1 for _ in changes_log if "CSP-8" in _)} changes')

# ============================================================
# Search-5-GeneticAlgorithms.ipynb
# ============================================================
path = 'MyIA.AI.Notebooks/Search/Part1-Foundations/Search-5-GeneticAlgorithms.ipynb'
nb = load_nb(path)

replacements_s5 = [
    ('[Search-6 CSP-Fundamentals >>](Search-6-CSP-Fundamentals.ipynb)',
     '[CSP-1 Fundamentals >>](../Part2-CSP/CSP-1-Fundamentals.ipynb)'),
]
for i in [0, 63]:
    if i < len(nb['cells']):
        if fix_cell_source(nb['cells'][i], replacements_s5):
            changes_log.append(f'Search-5 cell {i}: fixed Search-6 CSP link')

save_nb(path, nb)
print(f'Fixed Search-5: {sum(1 for _ in changes_log if "Search-5" in _)} changes')

# ============================================================
# Search-8-DancingLinks.ipynb
# ============================================================
path = 'MyIA.AI.Notebooks/Search/Part1-Foundations/Search-8-DancingLinks.ipynb'
nb = load_nb(path)

replacements_s8 = [
    # Title fix
    ('# Search-10-DancingLinks :', '# Search-8-DancingLinks :'),
    # Nav links: Search-9-Metaheuristics.ipynb is WRONG (file is Search-11)
    # The correct prev for Search-8 is Search-11-Metaheuristics (Metaheuristics comes after DLX in old numbering,
    # but in new numbering Search-8=DancingLinks, Search-9=LP, Search-10=SymbolicAutomata, Search-11=Metaheuristics)
    # Actually, looking at the original nav: << Metaheuristiques >> Programmation lineaire
    # This means Metaheuristiques is BEFORE DancingLinks and LP is AFTER.
    # With new numbering: Search-8(DLX) prev=Search-11(Metaheuristics), next=Search-9(LP)
    ('[<< Metaheuristiques](Search-9-Metaheuristics.ipynb)',
     '[<< Metaheuristiques](Search-11-Metaheuristics.ipynb)'),
    ('[Programmation lineaire >>](Search-11-LinearProgramming.ipynb)',
     '[Programmation lineaire >>](Search-9-LinearProgramming.ipynb)'),
]
for i in [0, 50]:
    if i < len(nb['cells']):
        if fix_cell_source(nb['cells'][i], replacements_s8):
            changes_log.append(f'Search-8 cell {i}: fixed title + nav')

save_nb(path, nb)
print(f'Fixed Search-8: {sum(1 for _ in changes_log if "Search-8" in _)} changes')

# ============================================================
# Search-9-LinearProgramming.ipynb
# ============================================================
path = 'MyIA.AI.Notebooks/Search/Part1-Foundations/Search-9-LinearProgramming.ipynb'
nb = load_nb(path)

replacements_s9 = [
    # Title fix
    ('# Search-11-LinearProgramming :', '# Search-9-LinearProgramming :'),
    # Nav links
    ('[<< DancingLinks](Search-10-DancingLinks.ipynb)',
     '[<< DancingLinks](Search-8-DancingLinks.ipynb)'),
    ('[SymbolicAutomata >>](Search-12-SymbolicAutomata.ipynb)',
     '[SymbolicAutomata >>](Search-10-SymbolicAutomata.ipynb)'),
]
for i in [0]:
    if i < len(nb['cells']):
        if fix_cell_source(nb['cells'][i], replacements_s9):
            changes_log.append(f'Search-9 cell {i}: fixed title + nav')

save_nb(path, nb)
print(f'Fixed Search-9: {sum(1 for _ in changes_log if "Search-9" in _)} changes')

# ============================================================
# Search-10-SymbolicAutomata.ipynb
# ============================================================
path = 'MyIA.AI.Notebooks/Search/Part1-Foundations/Search-10-SymbolicAutomata.ipynb'
nb = load_nb(path)

replacements_s10 = [
    # Title fix
    ('# Search-12 : Automates Symboliques', '# Search-10 : Automates Symboliques'),
    # Nav link
    ('[Search-11-LinearProgramming](Search-11-LinearProgramming.ipynb)',
     '[Search-9-LinearProgramming](Search-9-LinearProgramming.ipynb)'),
]
for i in [0]:
    if i < len(nb['cells']):
        if fix_cell_source(nb['cells'][i], replacements_s10):
            changes_log.append(f'Search-10 cell {i}: fixed title + nav')

save_nb(path, nb)
print(f'Fixed Search-10: {sum(1 for _ in changes_log if "Search-10" in _)} changes')

# ============================================================
# Search-11-Metaheuristics.ipynb
# ============================================================
path = 'MyIA.AI.Notebooks/Search/Part1-Foundations/Search-11-Metaheuristics.ipynb'
nb = load_nb(path)

replacements_s11 = [
    # Title fix
    ('# Search-9-Metaheuristiques :', '# Search-11-Metaheuristiques :'),
]
for i in [0]:
    if i < len(nb['cells']):
        if fix_cell_source(nb['cells'][i], replacements_s11):
            changes_log.append(f'Search-11 cell {i}: fixed title')

save_nb(path, nb)
print(f'Fixed Search-11: {sum(1 for _ in changes_log if "Search-11" in _)} changes')

# ============================================================
# Summary
# ============================================================
print(f'\nTotal changes: {len(changes_log)}')
for entry in changes_log:
    print(f'  - {entry}')
