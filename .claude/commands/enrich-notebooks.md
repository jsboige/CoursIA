# Enrich Notebooks Command

Enrich Jupyter notebooks with pedagogical markdown content.

## Usage

```
/enrich-notebooks [target] [options]
```

## Arguments

- `target`: Notebook path, family name, or "all"
  - Individual: `MyIA.AI.Notebooks/Probas/Infer/Infer-2-Gaussian-Mixtures.ipynb`
  - Family: `Infer`, `Sudoku`, `Search`, `SymbolicAI`, `Tweety`, `Lean`, `GenAI`
  - All: `all` (enriches all notebooks)

- Options (in target string):
  - `--execute`: Execute notebooks and verify outputs before enriching
  - `--fix-errors`: Attempt to fix code errors found during execution
  - `--strict`: Require interpretation after EVERY code cell
  - `--consecutive`: Focus on fixing consecutive code cells (cells de code qui se suivent)

## Instructions for Claude

When this command is invoked:

### 1. Parse the target argument

Determine if the user wants to enrich:
- A specific notebook file
- A notebook family (directory)
- All notebooks

### 2. Discover notebooks to enrich

Use Glob to find notebooks:

```python
# For a family
pattern = f"MyIA.AI.Notebooks/**/{family}*.ipynb"

# For Infer specifically
pattern = "MyIA.AI.Notebooks/Probas/Infer/Infer-*.ipynb"

# For all
pattern = "MyIA.AI.Notebooks/**/*.ipynb"
```

Exclude output notebooks (`*_output.ipynb`) and checkpoint files.

### 3. Read agent instructions

Read the enricher agent instructions:
```
Read(".claude/agents/notebook-enricher.md")
```

### 4. Launch parallel agents for each notebook

For each notebook, launch a background agent:

```python
Task(
    subagent_type="general-purpose",
    prompt=f"""
    Tu es un agent notebook-enricher.
    Lis les instructions dans .claude/agents/notebook-enricher.md

    Enrichis le notebook: {notebook_path}
    Options: {options}

    PROCESSUS:
    1. Lis le notebook entierement avec Read
    2. Identifie les endroits necessitant du markdown pedagogique:
       - Cellules de code consecutives sans markdown entre elles
       - Resultats sans interpretation
       - Sections sans introduction
       - Transitions abruptes
    3. Ajoute les cellules markdown via NotebookEdit (edit_mode="insert")
    4. Verifie la coherence finale

    {execute_instructions if --execute}
    {fix_instructions if --fix-errors}
    """,
    description=f"Enrich {notebook_name}",
    run_in_background=True
)
```

### 5. If --execute is specified

Add these instructions to the agent prompt:

```
EXECUTION:
1. Demarre un kernel adapte (python3 ou .net-csharp)
2. Execute chaque cellule sequentiellement
3. Capture les sorties pour les interpretations
4. Arrete le kernel a la fin
```

### 6. If --fix-errors is specified

Add these instructions to the agent prompt:

```
CORRECTION D'ERREURS:
1. Si une cellule echoue, analyse l'erreur
2. Propose une correction du code
3. Applique la correction via NotebookEdit
4. Re-execute pour verifier
5. Maximum 3 tentatives par cellule
```

### 7. If --consecutive is specified

Add emphasis on consecutive cells:

```
PRIORITE CELLULES CONSECUTIVES:
Focus sur les cellules de code qui se suivent sans markdown.
Pour chaque paire de cellules de code consecutives, ajouter:
- Soit une interpretation du resultat precedent
- Soit une introduction de ce qui suit
- Soit une transition entre concepts
```

### 8. Monitor agent completion

Check agent outputs periodically:
```python
TaskOutput(task_id=agent_id, block=False, timeout=5000)
```

### 9. Generate summary report

After all agents complete:

```
=== Notebook Enrichment Report ===
Date: {timestamp}
Target: {target}

Results:
  - ENRICHED: {count} notebooks
  - CELLS_ADDED: {total_cells} markdown cells
  - ERRORS_FIXED: {count} (if --fix-errors)

Details per notebook:
  [+5 cells] Infer-2-Gaussian-Mixtures.ipynb
    - Added section introduction
    - Added 3 result interpretations
    - Fixed consecutive code cells

  [+3 cells] Infer-3-Factor-Graphs.ipynb
    - Added conclusion table
    - Added 2 concept transitions
```

## Enrichment Criteria Reference

| Type | Description | Example |
|------|-------------|---------|
| Section intro | Contexte et objectifs | "Cette section explore..." |
| Code explanation | Ce que fait le code | "Le code suivant initialise..." |
| Result interpretation | Analyse des sorties | "Cette valeur indique que..." |
| Transition | Lien entre concepts | "Apres avoir vu X, explorons Y..." |
| Conclusion | Resume avec tableau | Table recapitulative |

## Known Families

| Family | Path Pattern | Kernel | Domain |
|--------|--------------|--------|--------|
| Infer | Probas/Infer/Infer-*.ipynb | .NET C# | Probabilistic programming |
| Sudoku | Sudoku/Sudoku-*.ipynb | .NET C# | Constraint solving |
| Tweety | SymbolicAI/Tweety-*.ipynb | Python | Argumentation |
| Lean | SymbolicAI/Lean/Lean-*.ipynb | Lean 4 / Python | Theorem proving |
| Search | Search/*.ipynb | Mixed | Optimization |
| GenAI | GenAI/*.ipynb | Python | Image generation |

## Examples

```
/enrich-notebooks Infer
/enrich-notebooks Infer --consecutive
/enrich-notebooks Infer --execute --fix-errors
/enrich-notebooks MyIA.AI.Notebooks/Probas/Infer/Infer-2-Gaussian-Mixtures.ipynb --strict
/enrich-notebooks Tweety --execute
/enrich-notebooks all --consecutive
```
