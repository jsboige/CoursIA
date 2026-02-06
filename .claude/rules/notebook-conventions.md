---
paths: MyIA.AI.Notebooks/**/*.ipynb
---

# Notebook Conventions

## Manipulation

- ALWAYS use `scripts/notebook_helpers.py` and `scripts/notebook_tools.py` for notebook manipulation, NOT ad-hoc Python code
- Use `NotebookEdit` tool for cell-level changes (insert, replace, delete)
- When inserting cells, work from BOTTOM to TOP to avoid index shifting
- Use cell `cell_id` (not index) as reference for NotebookEdit insertions
- Re-read notebook after each edit operation (indices change)
- Verify with `git diff` after modifications (expect more insertions than deletions for enrichment)

## Pedagogical Structure

- Every notebook MUST have: navigation header, learning objectives, prerequisites, estimated duration
- No consecutive code cells without explanatory markdown between them
- Every significant output MUST have an interpretation cell AFTER it
- Section introductions go BEFORE the code they introduce
- Conclusion with summary table at end of each major section

## Execution

- Python notebooks: prefer Papermill for batch execution
- .NET notebooks: ALWAYS use cell-by-cell via MCP (Papermill does NOT work)
- .NET notebooks with `#!import`: cell-by-cell execution ONLY
- Set working directory explicitly for notebooks with relative paths
- Use BATCH_MODE=true for notebooks with interactive widgets

## Content Rules

- No emojis in content
- French as primary language for documentation
- Code comments may be in French or English
- Professional, descriptive naming (no "Pure", "Enhanced", "Advanced", "Ultimate" prefixes)
