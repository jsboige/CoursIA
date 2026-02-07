Clean up and reorganize markdown in Jupyter notebooks: $ARGUMENTS

Use the `cleanup-notebooks` skill for the detailed process.

1. **Analyze** - `python scripts/notebook_helpers.py list {path} --verbose` to identify issues
2. **Identify problems** - Duplicates, misplaced cells, heading jumps, empty cells, consecutive interpretations
3. **Fix** - Via NotebookEdit (one operation at a time, re-read after each edit)
4. **Verify** - Check diff, ensure no code cells were deleted

Arguments: `[target] [--dry-run] [--aggressive] [--hierarchy-only]`

Safety: Never delete code cells. Re-read notebook after each edit. If structure is good, don't modify.

Sub-agents: notebook-cleaner (model: sonnet) for per-notebook cleanup
