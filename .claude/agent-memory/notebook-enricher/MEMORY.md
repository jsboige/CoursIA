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

### Domain-Specific Patterns

| Domain | Key Vocabulary | Common Patterns |
|--------|----------------|-----------------|
| Data Science with Agents | Pandas, LangChain, DataFrame, agent, tools, reasoning | Progressive questions (simple->complex), data cleaning workflow, agent orchestration |
| ML | accuracy, loss, overfitting, cross-validation | Train-test split, model evaluation, interpretation tables |
| Probas | prior, posterior, likelihood, inference | Bayesian updates, factor graphs, distribution visualization |

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
