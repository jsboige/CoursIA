---
name: cleanup-notebooks
description: Clean up and reorganize markdown in enriched Jupyter notebooks. Arguments: [target] [--dry-run] [--aggressive] [--hierarchy-only]
---

# Cleanup Notebooks

Reorganize and deduplicate pedagogical markdown in Jupyter notebooks.

**Target**: `$ARGUMENTS`

## Arguments

- `target`: Notebook path, family name, or `all`
- `--dry-run`: List problems without modifying
- `--aggressive`: Aggressive deduplication
- `--hierarchy-only`: Fix heading structure only

## Process

1. **Parse target** - Discover notebooks
2. **For each notebook**, launch a background agent:
   - Read notebook-cleaner agent instructions (`.claude/agents/notebook-cleaner.md`)
   - Read entire notebook, analyze structure
   - Identify problems (duplicates, misplaced cells, heading jumps, empty cells)
   - Fix via NotebookEdit (one operation at a time, verify diff after each)
   - Re-read notebook after each operation (indices change)

3. **If --dry-run**: List problems without modifying
4. **Generate summary** with cells deleted/modified per notebook

## Common Issues

| Pattern | Fix |
|---------|-----|
| Double introduction | Keep first, delete second |
| Orphan interpretation (before code) | Move after code cell |
| Heading jump (`##` then `####`) | Change to `###` |
| Empty transition cell | Delete or add content |
| Repeated concept definition | Keep best, delete others |
| Consecutive interpretation cells | Merge or delete duplicate |

## Safety Rules

- GOLDEN RULE: "Don't break what works" - if structure is good, don't modify
- Verify diffs after every operation
- Never delete code cells (only markdown)
- Re-read notebook after each edit (indices change)
- Use cell CONTENT for identification, not indices
