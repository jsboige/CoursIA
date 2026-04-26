---
paths: MyIA.AI.Notebooks/**/*.ipynb
---

# Notebook Conventions

## Manipulation

- ALWAYS use `scripts/notebook_tools/notebook_helpers.py` and `scripts/notebook_tools/notebook_tools.py` for notebook manipulation, NOT ad-hoc Python code
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

## Notebooks committés AVEC leurs sorties (règle user 2026-04-26)

**Tout notebook committé doit contenir ses sorties (outputs).** Les notebooks sont du contenu pédagogique : les sorties font partie du livrable.

- **JAMAIS** commit un notebook avec `execution_count: null` partout ou `outputs: []` vidés sans re-exécution
- **JAMAIS** "clean outputs avant commit" comme étape de routine
- Toute modification de cellule code (source, dépendances, paramètres) implique une **re-exécution complète** du notebook avant commit
- Format attendu : `execution_count: <int>` + `outputs: [<résultats>]` cohérents pour chaque cellule code exécutable
- Exception : cellules d'exercice avec stub `pass`/`print("Exercice a completer")` → `execution_count: <int>` + `outputs: [{stdout: "Exercice a completer\n"}]` ou outputs vide selon le stub
- Exception légitime : notebook qui n'est pas exécutable dans CI (kernel manquant, GPU requis, données privées) → documenter pourquoi dans le notebook (markdown), mais l'auteur DOIT exécuter localement avant commit

**Workflow obligatoire avant commit d'un notebook modifié** :

1. Re-exécuter intégralement via Papermill (`scripts/notebook_tools/notebook_tools.py execute <path>`) ou cell-by-cell pour .NET/Lean
2. Vérifier qu'aucune cellule n'est en erreur (cf règle "Aucune cellule en erreur")
3. Commit le notebook avec ses outputs
4. Si l'exécution est impossible : annuler le commit et signaler le blocage

**Pour la review** : un PR qui modifie un notebook **sans** mettre à jour ses outputs doit être rejeté avec demande de re-exécution. Exception : modifications uniquement dans les cellules markdown (introduction, conclusion, transitions) — alors les outputs des cellules code restent valides.

**Conséquence pour la coordination Papermill** : la règle "scope strict" (re-exécuter UNIQUEMENT les notebooks dont la source change) **reste valide** — elle évite les collisions d'outputs entre agents. Mais quand la source d'un notebook change, ses outputs DOIVENT être mis à jour dans le même commit.

## Aucune cellule en erreur (règle user 2026-04-26)

**Aucune cellule de notebook ne doit échouer volontairement.** Les scripts de validation trackent les cellules en erreur comme bugs à corriger.

- **`raise NotImplementedError(...)` est INTERDIT partout** dans un notebook (top-level, méthode, fonction utilitaire). Aucune exception.
- **Toute autre erreur volontaire interdite aussi** : `assert False`, `1/0`, `raise X("...")`, etc.
- **Pour signaler une cellule à compléter par l'étudiant**, utiliser selon le contexte :
  - Top-level : `print("Exercice a completer")` ou `pass`
  - Méthode/fonction : `pass  # TODO étudiant : <description>` ou `return None  # TODO étudiant`
  - Variable attendue : `result = None  # TODO étudiant : remplacer par <calcul>`
- **Préserver TOUS les commentaires `# TODO`, `# Indice`, `# Étape N`** au-dessus du stub (le scaffolding pédagogique est le livrable).
- Le notebook doit s'exécuter de bout en bout sans erreur même quand les exercices ne sont pas complétés.
- **Conséquence pour la review** : remplacer un `raise NotImplementedError` legacy par le pattern correct est conforme et doit être mergé sans contestation. La règle anti-régression (CLAUDE.md / `anti-regression.md`) **ne s'applique pas** à ce remplacement.
