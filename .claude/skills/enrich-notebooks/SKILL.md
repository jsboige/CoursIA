---
name: enrich-notebooks
description: Enrich Jupyter notebooks with pedagogical markdown content. Arguments: [target] [--execute] [--fix-errors] [--strict] [--consecutive] [--iterate]
---

# Enrich Notebooks

Add pedagogical markdown content to Jupyter notebooks.

**Target**: `$ARGUMENTS`

## Arguments

- `target`: Notebook path, family name (`Infer`, `Sudoku`, `Tweety`, `Lean`, `GenAI`, etc.), or `all`
- `--execute`: Run notebooks and capture outputs before enriching
- `--fix-errors`: Correct code errors found during execution
- `--strict`: Require interpretation after EVERY code cell
- `--consecutive`: Focus on consecutive code cells without markdown
- `--iterate`: Use cell-iterator for iterative correction

## Process

1. **Parse target** - Discover notebooks to enrich
2. **For each notebook**, launch a background agent:
   - Read the notebook-enricher agent instructions (`.claude/agents/notebook-enricher.md`)
   - Analyze structure: `python scripts/notebook_helpers.py list {path} --verbose`
   - Find gaps programmatically (Python API):
     ```python
     from scripts.notebook_helpers import NotebookHelper
     helper = NotebookHelper(path)
     gaps = helper.find_cells_needing_enrichment()      # Cells missing interpretation
     consecutive = helper.find_consecutive_code_cells()  # Code cells without markdown between
     ```
   - Validate placement: `helper.validate_enrichment_context(cell_index)` returns what's needed
   - Insert markdown cells via NotebookEdit (bottom-to-top to preserve indices)
   - Verify with: `helper.get_cell_sequence(start, end)` after each insertion

3. **If --execute**: Execute notebooks first to capture outputs for interpretation
4. **If --fix-errors**: Analyze errors, propose corrections, re-execute
5. **If --consecutive**: Prioritize fixing consecutive code cells
6. **If --iterate**: Use notebook-cell-iterator agent for targeted cell fixes

## Agent Delegation

Use `model: sonnet` for enrichment agents (good balance of speed and quality).
For complex domains (Probas, Lean), consider `model: inherit` for better reasoning.

```python
Task(
    subagent_type="general-purpose",
    model="sonnet",
    prompt="Tu es un agent notebook-enricher. Lis .claude/agents/notebook-enricher.md. Enrichis: {path}",
    description=f"Enrich {name}",
    run_in_background=True
)
```

## Enrichment Criteria

| Type | Placement | Tense |
|------|-----------|-------|
| Section intro | BEFORE code | Future: "This code will..." |
| Code explanation | BETWEEN code cells | Present: "This function..." |
| Result interpretation | AFTER code output | Past: "The results show..." |
| Transition | Between sections | "After seeing X, let's explore Y..." |
| Conclusion | End of section | Summary table |

## After Enrichment

- Verify with `git diff` (expect more insertions than deletions)
- Consider running `/cleanup-notebooks` to fix any positioning issues
- Update MEMORY.md with lessons learned about positioning accuracy
