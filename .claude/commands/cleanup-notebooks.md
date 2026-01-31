# Cleanup Notebooks Command

Nettoyer et reorganiser le markdown dans les notebooks Jupyter enrichis.

## Usage

```
/cleanup-notebooks [target] [options]
```

## Arguments

- `target`: Notebook path, family name, or "all"
  - Individual: `MyIA.AI.Notebooks/Probas/Infer/Infer-2-Gaussian-Mixtures.ipynb`
  - Family: `Infer`, `Sudoku`, `Search`, `SymbolicAI`, `Tweety`, `Lean`, `GenAI`
  - All: `all`

- Options (in target string):
  - `--dry-run`: Lister les problemes sans modifier
  - `--aggressive`: Supprimer plus agressivement les redondances
  - `--hierarchy-only`: Ne corriger que les problemes de hierarchie

## Instructions for Claude

### 1. Parse target and discover notebooks

```python
# For a family
pattern = f"MyIA.AI.Notebooks/**/{family}*.ipynb"

# For Infer specifically
pattern = "MyIA.AI.Notebooks/Probas/Infer/Infer-*.ipynb"
```

Exclude output notebooks (`*_output.ipynb`).

### 2. Read agent instructions

```
Read(".claude/agents/notebook-cleaner.md")
```

### 3. Launch parallel agents

```python
for notebook in notebooks:
    Task(
        subagent_type="general-purpose",
        prompt=f"""
        Tu es un agent notebook-cleaner.
        Lis les instructions dans .claude/agents/notebook-cleaner.md

        Nettoie le notebook: {notebook_path}
        Options: {options}

        PROCESSUS:
        1. Lis le notebook entierement avec Read
        2. Identifie les problemes:
           - Cellules markdown redondantes ou dupliquees
           - Hierarchie de titres incoherente
           - Information mal placee (interpretation avant code, etc.)
           - Cellules vides ou quasi-vides
           - Repetitions inutiles
        3. Corrige via NotebookEdit:
           - edit_mode="delete" pour supprimer
           - edit_mode="replace" pour modifier
        4. Verifie la coherence finale

        IMPORTANT: Ne PAS supprimer de contenu pedagogique utile.
        Objectif: reorganiser et dedupliquer, pas appauvrir.

        {dry_run_instructions if --dry-run}
        """,
        description=f"Cleanup {notebook_name}",
        run_in_background=True
    )
```

### 4. If --dry-run

Add these instructions:
```
MODE DRY-RUN:
Ne fais AUCUNE modification. Liste uniquement les problemes detectes
avec leur localisation (numero de cellule) et la correction proposee.
Format:
- [CELL 5] REDONDANCE: "Introduction aux priors" repete cellule 3
- [CELL 12] HIERARCHIE: ### suivi de # (devrait etre ##)
- [CELL 18] MAL PLACE: Interpretation avant le code
```

### 5. Generate summary report

```
=== Notebook Cleanup Report ===
Date: {timestamp}
Target: {target}

Results:
  - CLEANED: {count} notebooks
  - CELLS_DELETED: {total}
  - CELLS_MODIFIED: {total}
  - HIERARCHIES_FIXED: {total}

Details per notebook:
  [-3 cells] Infer-2-Gaussian-Mixtures.ipynb
    - Deleted 2 redundant introduction cells
    - Fixed heading hierarchy (3 corrections)
    - Merged 2 interpretation cells

  [-1 cell] Infer-5-Skills-IRT.ipynb
    - Removed empty markdown cell
    - Fixed misplaced conclusion
```

## Known Issues to Fix

| Pattern | Example | Fix |
|---------|---------|-----|
| Double introduction | "Dans cette section..." x2 | Keep first, delete second |
| Orphan interpretation | Result analysis before code | Move after code cell |
| Heading jump | `## Section` then `#### Detail` | Change to `### Detail` |
| Empty transition | `### Transition` with no content | Delete or add content |
| Repeated concept | Same definition in 3 places | Keep best, delete others |

## Examples

```
/cleanup-notebooks Infer
/cleanup-notebooks Infer --dry-run
/cleanup-notebooks MyIA.AI.Notebooks/Probas/Infer/Infer-2-Gaussian-Mixtures.ipynb
/cleanup-notebooks all --hierarchy-only
```
