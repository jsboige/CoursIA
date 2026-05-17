---
paths: MyIA.AI.Notebooks/**/*.ipynb
---

# Notebook Conventions

**Regles user (C.1/C.2/C.3 detaillees)** : voir CLAUDE.md section C.

## Manipulation

- Utiliser `scripts/notebook_tools/notebook_helpers.py` et `notebook_tools.py` (PAS de code Python ad-hoc)
- `NotebookEdit` pour cell-level changes — references par `cell_id`, pas par index
- Insertions multiples : travailler BAS vers HAUT (evite index shift)
- Re-read le notebook apres chaque edit (indices changent)
- `git diff` apres modifs : enrichissement = insertions > deletions

## Structure pedagogique

- Header obligatoire : navigation, objectifs d'apprentissage, prerequis, duree estimee
- Pas de cellules code consecutives sans markdown entre elles
- Interpretation APRES chaque output significatif
- Introduction de section AVANT le code qu'elle introduit
- Conclusion avec table recap en fin de section majeure

## Execution

- **Python notebooks** : Papermill pour batch (`notebook_tools.py execute <path>`)
- **.NET notebooks** : cell-by-cell via MCP Jupyter UNIQUEMENT (Papermill ne marche pas, surtout avec `#!import`)
- **WSL notebooks** (GameTheory/Lean) : `wsl_papermill.py` (cf [.claude/rules/wsl-kernels.md](wsl-kernels.md))
- Working directory explicite pour notebooks avec paths relatifs
- `BATCH_MODE=true` pour notebooks avec widgets interactifs

## Patterns stub d'exercice (rule C.1)

`raise NotImplementedError` / `assert False` / `1/0` **INTERDITS partout** (notebook doit s'executer end-to-end). Patterns corrects :

| Contexte | Pattern |
|----------|---------|
| Top-level | `print("Exercice a completer")` ou `pass` |
| Methode classe | `def foo(self): pass  # TODO etudiant : <desc>` |
| Fonction utilitaire | `def helper(...): return None  # TODO etudiant` |
| Variable attendue | `result = None  # TODO etudiant : remplacer par compute_thing()` |

Preserver TOUS les commentaires `# TODO`, `# Indice`, `# Etape N`. Remplacer `raise NotImplementedError` legacy par ce pattern = **conforme**, anti-regression ne s'applique pas.

## Commit avec outputs (rule C.2)

Tout notebook committe : `execution_count: <int>` + `outputs: [...]` coherents pour chaque cellule code executable. Modification source = re-execution complete avant commit. Exception : modifs uniquement markdown → outputs precedents valides.

## Scope strict re-execution (rule C.3)

Commit UNIQUEMENT les notebooks dont la source a change (`git diff <nb> | grep -cE '^\+\s*"source"' > 0`). Pour audit/inventaire : Papermill dans `/tmp/audit_<famille>_$(date +%s)/`, rapport sur dashboard, pas dans le repo.
