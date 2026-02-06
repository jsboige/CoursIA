Enrich Jupyter notebooks with pedagogical content: $ARGUMENTS

Use the `enrich-notebooks` and `notebook-patterns` skills for detailed patterns.

1. **Analyze structure** - `python scripts/notebook_helpers.py list {path} --verbose` to identify gaps
2. **Find enrichment needs** - Use `NotebookHelper.find_cells_needing_enrichment()` or `find_consecutive_code_cells()`
3. **For each notebook**, delegate to notebook-enricher agent (model: sonnet):
   - Insert markdown cells via NotebookEdit (work BOTTOM to TOP)
   - Interpretations AFTER code outputs, section intros BEFORE code
   - Use `validate_enrichment_context()` to verify placement
4. **Verify** - `git diff` should show more insertions than deletions

Arguments: `[target] [--execute] [--fix-errors] [--strict] [--consecutive] [--iterate]`

Tools:
- **Scripts**: `notebook_helpers.py list`, `find_cells_needing_enrichment()`, `validate_enrichment_context()`
- **NotebookEdit**: For cell insertion (use cell_id, not index)
- **Sub-agents**: notebook-enricher (sonnet), notebook-cell-iterator (sonnet) for --iterate
