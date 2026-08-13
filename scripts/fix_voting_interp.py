#!/usr/bin/env python3
"""c.8258 reorder script for Voting-Methods-Csharp.ipynb.

Reorder 5 cells (indices 9, 12, 21, 24, 27 in original order) to canonical positions.
Pattern: hoist `## N.` headers above their code+interp blocks (5 sections bugged:
§2, §3, §6, §7, §8).

Walk-and-emit pattern (L933 ★): pop REVERSE order, insert TARGET POSITION order.
Markdown-only, no code cell touched (C.3 exception).
"""

import json
from pathlib import Path

NB_PATH = Path("MyIA.AI.Notebooks/GameTheory/SocialChoice/03-Voting-Methods-Csharp.ipynb")

# (source_index, target_index_after_each_move)
# Walk in reverse to keep downstream indices stable.
MOVES = [
    # Move §8 header [27] before [25] (its code)
    (27, 25),
    # Move §7 header [24] before [22] (its code)
    (24, 22),
    # Move §6 header [21] before [19] (its code)
    (21, 19),
    # Move §3 header [12] before [10] (its code)
    (12, 10),
    # Move §2 header [9] before [7] (its code)
    (9, 7),
]


def main():
    nb = json.loads(NB_PATH.read_text(encoding="utf-8"))
    cells = nb["cells"]
    n = len(cells)
    print(f"Total cells: {n}")
    for src_idx, tgt_idx in MOVES:
        if src_idx >= n or tgt_idx >= n:
            raise ValueError(f"Move {src_idx}->{tgt_idx} out of range (n={n})")
        popped = cells.pop(src_idx)
        cells.insert(tgt_idx, popped)
        header_preview = "".join(popped["source"]).strip().split("\n")[0][:60]
        print(f"OK: move idx {src_idx} -> {tgt_idx} : {header_preview!r}")
    # Sanity: count cells again, IDs preserved
    new_n = len(cells)
    if new_n != n:
        raise ValueError(f"Cell count changed: {n} -> {new_n}")
    # Verify each target now precedes its code
    expected_order = [
        (3, "## 1"),
        (4, "code §1 (suite)"),
        (5, "### Cycle"),
        (6, "### Interprétation : majorité"),
        (7, "## 2"),
        (8, "code §2"),
        (9, "### Lecture du résultat : existence"),
        (10, "## 3"),
        (11, "code §3"),
        (12, "### Lecture du résultat : symétrie"),
        (13, "code §4"),
        (14, "## 4"),
        (15, "### Interprétation : la règle"),
        (16, "code §5"),
        (17, "## 5"),
        (18, "### Interprétation : liberté"),
        (19, "## 6"),
        (20, "code §6"),
        (21, "### Lecture du résultat : violation"),
        (22, "## 7"),
        (23, "code §7"),
        (24, "### Lecture du résultat : médiane"),
        (25, "## 8"),
        (26, "code §8"),
        (27, "### Lecture du résultat : course"),
        (28, "code §9"),
        (29, "## 9"),
        (30, "code §10 (Exercice 1)"),
        # idx 31-32 are Exercice 2/3 code cells
        (33, "## 10"),
    ]
    for i, expected_head in expected_order:
        if i >= new_n:
            print(f"WARN: expected cell idx {i} not present")
            continue
        c = cells[i]
        head = "".join(c["source"]).strip().split("\n")[0][:60]
        if not head.startswith(expected_head[:30]):
            print(f"!!! Mismatch at idx {i}: expected {expected_head[:40]!r}, got {head!r}")
        else:
            # print(f"OK idx {i}: {head[:60]!r}")
            pass
    out = json.dumps(nb, indent=1, ensure_ascii=False)
    NB_PATH.write_bytes(out.encode("utf-8"))
    print(f"WROTE {NB_PATH} ({len(out)} chars)")


if __name__ == "__main__":
    main()