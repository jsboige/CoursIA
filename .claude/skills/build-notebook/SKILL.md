---
name: build-notebook
description: Build or improve Jupyter notebooks iteratively with quality scoring
argument-hint: "<new|improve|fix> <path> [--topic=X] [--domain=X] [--level=X] [--quality=N] [--max-iter=N]"
disable-model-invocation: true
---

# Build Notebook

Create, improve, or fix Jupyter notebooks iteratively.

**Action**: `$ARGUMENTS`

## Actions

### `new` - Create from scratch
Requires: `--topic`, `--domain` (ML, Probas, GenAI, GameTheory, SymbolicAI, Sudoku, Search), `--level` (intro, intermediate, advanced)

### `improve` - Enhance existing notebook
Requires: notebook path, optional `--quality` (0-100, default 90), `--focus` (execution, pedagogy, content, structure)

### `fix` - Correct execution errors
Requires: notebook path, optional `--max-iter` (default 5)

## Iterative Workflow

```
while iteration < max_iterations and score < quality_target:
    1. Execute notebook (notebook-executor agent)
    2. Validate all aspects (notebook-validator agent)
    3. Plan corrective actions (prioritized by severity)
    4. Apply via appropriate sub-agent (enricher, cell-iterator, cleaner)
    5. Re-validate and measure improvement
```

## Quality Scoring

| Category | Weight | Criteria |
|----------|--------|----------|
| Structure | 15% | Valid JSON, metadata, cells |
| Syntax | 15% | Valid code, markdown, LaTeX |
| Execution | 30% | No errors, no timeouts |
| Pedagogy | 25% | Progression, code/markdown ratio, explanations |
| Content | 15% | Visualizations, formulas, conclusion |

## Sub-Agents Used

| Agent | Role | Model |
|-------|------|-------|
| notebook-designer | Create initial structure | inherit |
| notebook-executor | Run the notebook | sonnet |
| notebook-validator | Evaluate quality | sonnet |
| notebook-enricher | Add pedagogical content | sonnet |
| notebook-cell-iterator | Fix specific cells | sonnet |
| notebook-cleaner | Clean structure | sonnet |

## Model Selection Strategy

- Use `haiku` for quick validation checks
- Use `sonnet` for enrichment and standard fixes
- Use `inherit` (or `opus` if available) for complex design and orchestration
