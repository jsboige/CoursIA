#!/usr/bin/env python3
"""c.8259 reorder script for App-8-MiniZinc-Csharp.ipynb.

Hoist 5 section headers `## N.` (and 1 pedagogical sub-header `### N-Reines en CP-SAT C#`)
above their respective code blocks. Pattern: section header precedes code+interp.

Strategy: **direct mapping** (NOT walk-and-emit). With 6 cells to move in cascade,
walk-and-emit's mutable target indices are error-prone (each insert shifts downstream
indices). Direct mapping lists the final canonical order, then applies it via
`new_cells = [cells[orig_idx] for orig_idx in FINAL_ORDER]`. Guarantees the final
state matches expectation; 33 cells preserved (multiset byte-identique, anti-régression
CLAUDE.md §D).

6 hoisted cells:
- orig-6  `## 2. Syntaxe de base`         -> final 4
- orig-14 `## 3. Contraintes globales`     -> final 10
- orig-17 `### N-Reines en CP-SAT C#`     -> final 14
- orig-19 `## 4. Emploi du temps`         -> final 16
- orig-24 `## 5. Sudoku 4x4`              -> final 19
- orig-26 `## 6. Comparaison`             -> final 21

27 cells unchanged.
Markdown-only, no code cell touched (C.3 exception).
"""

import json
from pathlib import Path

NB_PATH = Path("MyIA.AI.Notebooks/Search/Applications/CSP/App-8-MiniZinc-Csharp.ipynb")

# Direct mapping: final_order[i] = orig index of cell that should be at final position i.
# Trailing [27, 28, 29, 30, 31, 32] left as the untouched tail (exercises + visualisation
# + synthèse + références).
FINAL_ORDER = [
    0,   # App-8 intro
    1,   # App-8 load
    2,   # utilitaire DisplayModel
    3,   # ## 1. Introduction
    6,   # ## 2. Syntaxe de base (HOISTED)
    4,   # code Section 2 Premier modèle
    5,   # interp x=7, y=3
    7,   # code Section 2 suite Optimisation
    8,   # interp 9 pièces
    9,   # sub-header Optimisation
    14,  # ## 3. Contraintes globales (HOISTED)
    10,  # code Section 3 N-Reines
    11,  # prose §3
    12,  # code N-Reines CP-SAT C#
    17,  # sub-header N-Reines en CP-SAT C# (HOISTED)
    13,  # interp [7,3,0,2,5,1,6,4]
    19,  # ## 4. Emploi du temps (HOISTED)
    15,  # code Section 4 Timetabling
    16,  # interp emploi du temps
    24,  # ## 5. Sudoku 4x4 (HOISTED)
    18,  # code Section 5 Sudoku
    26,  # ## 6. Comparaison (HOISTED)
    20,  # code Section 6 Comparaison
    21,  # interp backtracking
    22,  # prose §6
    23,  # code Tableau comparatif
    25,  # code #load helper
    # Tail (untouched): exercices + visualisation + synthèse + références
    27, 28, 29, 30, 31, 32,
]


def main():
    nb = json.loads(NB_PATH.read_text(encoding="utf-8"))
    cells = nb["cells"]
    n = len(cells)
    print(f"Total cells: {n}")
    # Validate direct mapping covers all 33 cells exactly once
    if sorted(FINAL_ORDER) != list(range(n)):
        raise ValueError(f"FINAL_ORDER does not cover 0..{n-1}: {sorted(FINAL_ORDER)}")
    # Apply the mapping
    new_cells = [cells[i] for i in FINAL_ORDER]
    nb["cells"] = new_cells
    # Verify expected canonical order (post-reorder)
    expected = [
        (3, "## 1. Introduction"),
        (4, "## 2. Syntaxe de base"),
        (5, "code"),  # Section 2 Premier modèle
        (6, "### Lecture"),  # x=7, y=3
        (10, "## 3. Contraintes globales"),
        (11, "code"),  # Section 3 N-Reines
        (14, "### N-Reines en CP-SAT C#"),
        (15, "### Lecture"),  # [7,3,0,2,5,1,6,4]
        (16, "## 4. Emploi du temps"),
        (19, "## 5. Sudoku 4x4"),
        (21, "## 6. Comparaison"),
    ]
    for i, expected_head in expected:
        if i >= len(new_cells):
            print(f"WARN: expected cell idx {i} not present")
            continue
        c = new_cells[i]
        head = "".join(c["source"]).strip().split("\n")[0][:60]
        if not head.startswith(expected_head[:25]):
            print(f"!!! Mismatch at idx {i}: expected {expected_head[:40]!r}, got {head!r}")
        else:
            print(f"OK idx {i}: {head[:60]!r}")
    out = json.dumps(nb, indent=1, ensure_ascii=False)
    NB_PATH.write_bytes(out.encode("utf-8"))
    print(f"WROTE {NB_PATH} ({len(out)} chars)")


if __name__ == "__main__":
    main()
