# Notebook Enricher - Agent Memory

## Key Learnings

### Cell Positioning Rules (CRITICAL)

**Golden Rule**: Work BOTTOM to TOP to avoid index shifting during insertions.

**Verification**: After each insertion batch, re-read the notebook to confirm cell_id references.

**Never**: Insert cells before re-reading when doing multiple insertions in one notebook.

### Successful Enrichment Sessions

- **2026-02-07**: DataScienceWithAgents Labs (3 notebooks, 11 cells added) - See [enrichment-log-2026-02-07.md](enrichment-log-2026-02-07.md)
  - All cells positioned correctly on first attempt
  - BOTTOM-to-TOP strategy prevented index conflicts
  - No git rollbacks needed
- **2026-02-16**: Sudoku-3-ORTools (4 cells added: 1 header with objectives, 2 interpretations, 1 footer)
  - Navigation header and footer with Search notebook links
  - Learning objectives (Bloom taxonomy) for CSP, CP-SAT, MIP
  - Duration: 50 minutes, Prerequisites: Sudoku-1-Backtracking
  - Interpretations after CP solver test and performance comparison
  - BOTTOM-to-TOP strategy with re-read between each insertion
- **2026-02-16**: Search-9-Metaheuristics (3 cells added: 2 interpretations, 1 code improvement)
  - Added interpretation after parameter analysis visualization (pop_size impact)
  - Added interpretation after PSO convergence visualization with technical note
  - Replaced seaborn with matplotlib in comparative plots (removed dependency)
  - All cells positioned correctly, BOTTOM-to-TOP strategy used
- **2026-02-19**: Video GPU Notebooks Pedagogical Enhancement (6 notebooks)
  - Replaced "désactivé/non disponible" messages with detailed pedagogical outputs
  - Added MODE PEDAGOGIQUE sections with expected parameters, results, and reproduction code
  - Notebooks: 01-3-Qwen-VL, 01-4-ESRGAN, 02-1-HunyuanVideo, 02-2-LTX-Video, 02-3-Wan, 02-4-SVD
  - Used edit_mode="replace" on existing interpretation cells (not insertions)
  - No cell positioning issues since we replaced existing cells

### Domain-Specific Patterns

| Domain | Key Vocabulary | Common Patterns |
|--------|----------------|-----------------|
| Data Science with Agents | Pandas, LangChain, DataFrame, agent, tools, reasoning | Progressive questions (simple->complex), data cleaning workflow, agent orchestration |
| ML | accuracy, loss, overfitting, cross-validation | Train-test split, model evaluation, interpretation tables |
| Probas | prior, posterior, likelihood, inference | Bayesian updates, factor graphs, distribution visualization |
| Sudoku/Constraint Solving | CSP, CP-SAT, MIP, DecisionBuilder, AllDifferent, propagation | Solver comparison tables, performance benchmarks, constraint modeling patterns |
| Search/Optimization | fitness, convergence, population, exploration/exploitation, metaheuristics | Parameter sensitivity analysis, algorithm comparison tables, convergence plots |

### Content Strategy Templates

**Introduction Cell** (BEFORE code):
- Future tense ("nous allons...", "le code va...")
- Sets expectations
- Explains "why" before "how"

**Interpretation Cell** (AFTER code):
- Past/present tense ("le resultat montre...", "on observe...")
- Tables for structured data
- > **Note technique** for important details

**Transition Cell** (BETWEEN sections):
- Links concepts
- Previews next steps
- Maintains pedagogical flow

### Errors to Avoid

1. **Never** insert interpretation BEFORE the code it analyzes
2. **Never** skip re-reading after insertions
3. **Never** use ad-hoc Python for notebook manipulation (use notebook_helpers.py)
4. **Never** add emojis
5. **Never** modify existing code cells (unless --fix-errors flag)

### Quality Checklist

Before completing enrichment:
- [ ] No consecutive code cells without markdown
- [ ] All notebooks have learning objectives header
- [ ] Prerequisites and duration specified
- [ ] Interpretation cells are AFTER code cells
- [ ] Git diff shows more insertions than deletions
- [ ] Professional French language (no emojis)
- [ ] Domain vocabulary is accurate

### Tools Reference

```bash
# Analyze structure
python scripts/notebook_helpers.py list <path> --verbose

# Verify consecutive code cells
grep -A1 "cell_type.*code" <path>

# Check git diff
git diff --stat <path>
```

### Memory Organization

- `MEMORY.md` (this file): High-level patterns and lessons
- `enrichment-log-YYYY-MM-DD.md`: Detailed session logs
- Future: `domain-patterns.md` for domain-specific vocabulary expansion
