#!/usr/bin/env python3
"""EPIC #10678 Phase 1b : scan orphan end-of-notebook interp cells.

HONESTY-FIRST FINDINGS (c.240):
- 21 cells with gap_after=None AND verdict=OK found in c.237 inventory
- 1 confirmed MISPLACED (02-SK-Advanced cell[34], already fixed c.239 PR #10705)
- 1 POSSIBLE_MISPLACED (Sudoku-3-Genetic-Csharp cell[27] - last cell, manual review recommended)
- 19 LEGIT closing interps

The c.237 "blind spot" is **NOT** a classification bug — it's a missing semantic
heuristic. Closing interps that semantically belong to the immediately preceding
code are correctly classified OK; those that semantically belong to an earlier
code cell require a position-blind, semantic-based detector.

Recommendation: Phase 3 (PR #10682) should add _interp_matches_code() using
keyword matching (interp tokens vs previous-code tokens).
"""
import json
import re
import sys
from pathlib import Path
from collections import Counter

# Pattern matching c.237 audit exactly
INTERP_RE = re.compile(r'###\s+(?:Lecture du résultat|Interprétation|Interprétation des résultats?)\b')

# Code tokenization patterns (interp matches if shares ≥3 significant identifiers with code)
TOKEN_RE = re.compile(r'\b[A-Za-z_]\w{3,}\b')  # word identifiers ≥4 chars

def interp_matches_code(interp_src: str, code_src: str) -> bool:
    """Check if interp semantically matches the code by keyword sharing.

    Returns True if interp contains ≥3 keywords that also appear in code.
    False means the interp is talking about something else (potential orphan).
    """
    interp_words = set(w.lower() for w in TOKEN_RE.findall(interp_src))
    code_words = set(w.lower() for w in TOKEN_RE.findall(code_src))
    # Strip common stopwords (rough heuristic)
    common = {'this', 'that', 'with', 'from', 'have', 'they', 'them', 'will', 'been',
              'each', 'which', 'their', 'there', 'these', 'those', 'were', 'what'}
    interp_words -= common
    code_words -= common
    if not interp_words:
        return True  # vacuous interp, accept
    return len(interp_words & code_words) >= 2

REPO_ROOT = Path(__file__).parent
INVENTORY_PATH = REPO_ROOT / 'notebooks_interp_inventory.json'

if not INVENTORY_PATH.exists():
    print(f'ERROR: {INVENTORY_PATH} not found. Run from c.240 worktree after fetching inventory from PR #10681.')
    sys.exit(1)

with open(INVENTORY_PATH, encoding='utf-8') as f:
    inv = json.load(f)

print(f'Loaded {len(inv)} notebook entries from c.237 inventory')
print()

orphans = []

for nb_entry in inv:
    path = nb_entry['path']
    interp_cells = nb_entry.get('interp_cells', [])

    try:
        import nbformat
        nb = nbformat.read(path, as_version=4)
    except Exception as e:
        print(f'WARN: cannot read {path}: {e}')
        continue

    for c in nb_entry.get('strict', []):
        idx = c.get('idx')
        if c.get('gap_after') is None and c.get('verdict') == 'OK' and idx is not None and idx in interp_cells:
            if idx >= len(nb.cells):
                continue
            cell = nb.cells[idx]
            if cell.cell_type != 'markdown':
                continue
            src = ''.join(cell.get('source', []))
            if not INTERP_RE.search(src):
                continue

            prev_code_idx = None
            for i in range(idx - 1, -1, -1):
                if nb.cells[i].cell_type == 'code':
                    prev_code_idx = i
                    break

            next_code_idx = None
            for i in range(idx + 1, len(nb.cells)):
                if nb.cells[i].cell_type == 'code':
                    next_code_idx = i
                    break

            if next_code_idx is None and prev_code_idx is not None:
                prev_code_src = ''.join(nb.cells[prev_code_idx].get('source', []))
                matches = interp_matches_code(src, prev_code_src)
                if matches:
                    verdict = 'LEGIT'
                    reason = 'closing_interp_immediately_after_last_code'
                elif prev_code_idx == len(nb.cells) - 2 or idx == len(nb.cells) - 1:
                    verdict = 'POSSIBLE_MISPLACED'
                    reason = 'orphan_last_cell_review_manually'
                else:
                    verdict = 'POSSIBLE_MISPLACED'
                    reason = 'orphan_semantic_mismatch_review_manually'

                orphans.append({
                    'notebook': path,
                    'idx': idx,
                    'cell_type': 'markdown',
                    'preview': src[:120].replace('\n', ' / '),
                    'prev_code_idx': prev_code_idx,
                    'total_cells': len(nb.cells),
                    'is_last_cell': (idx == len(nb.cells) - 1),
                    'last_cell_preview': ''.join(nb.cells[-1].get('source', []))[:80].replace('\n', ' / '),
                    'c240_verdict': verdict,
                    'c240_reason': reason,
                })

# Print summary
counts = Counter(o['c240_verdict'] for o in orphans)
print(f'Found {len(orphans)} orphan end-of-notebook interp cells (gap_after=None AND verdict=OK)')
for k, v in counts.most_common():
    print(f'  {k}: {v}')
print()

# Output JSON
out_json = REPO_ROOT / 'notebooks_interp_orphans.json'
with open(out_json, 'w', encoding='utf-8') as f:
    json.dump({
        'generated_from': 'c.237 inventory (PR #10681 commit 077997913)',
        'method': 'gap_after=None AND verdict=OK + semantic_check via token matching',
        'orphan_count': len(orphans),
        'verdict_counts': dict(counts),
        'orphans': orphans,
    }, f, indent=1, ensure_ascii=False)
print(f'Wrote {out_json}')
