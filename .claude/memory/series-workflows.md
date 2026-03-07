# Series Improvement Workflows - Project Memory

Ce fichier persiste l'etat des series de notebooks en cours d'amelioration.

## Sessions actives

| Serie | Workflow | Status | Progression | Dernier checkpoint |
|-------|----------|--------|-------------|-------------------|
| (aucune session active) | - | - | - | - |

## Series completees

| Serie | Workflow | Date | Notebooks | Score moyen |
|-------|----------|------|-----------|-------------|
| GenAI/Image/01-Foundation | validate | 2026-02-28 | 5/5 | 100% |
| GenAI/Video | validate | 2026-03-05 | 16/16 | 100% |
| GenAI/Texte | validate | 2026-03-06 | 11/11 | 100% |
| Search/Part1-Foundations | enrich | (en attente) | - | - |
| Search/Part2-CSP | enrich | (en attente) | - | - |

## Patterns d'erreurs frequents par famille

### GenAI
- **dotenv path**: Utiliser `../.env` (relatif au sous-repertoire)
- **gpt-4o-mini obsolete**: Migrer vers gpt-5-mini
- **ComfyUI timeout**: Verifier COMFYUI_AUTH_TOKEN avant execution

### Sudoku (.NET)
- **Cold start**: Premier kernel .NET prend 30-60s
- **Working directory**: Definir `Directory.SetCurrentDirectory` en premiere cellule
- **#!import**: Ne PAS utiliser Papermill, cell-by-cell uniquement

### GameTheory (WSL)
- **Kernel WSL**: Verifier que lean4/python3-wsl est disponible
- **Chemins Windows**: Le wrapper WSL convertit automatiquement

### Probas/Infer
- **Infer.NET 0.5.0**: Version specifique requise
- **NuGet restore**: Parfois necessaire avant execution

## Lessons apprises

### Enrichissement
- Interpretation = APRES le code, JAMAIS avant
- Travailler du BAS vers le HAUT pour eviter decalage indices
- Ratio cible: ~40% markdown / 60% code

### Execution
- .NET + `#!import`: cell-by-cell UNIQUEMENT
- BATCH_MODE=true pour widgets interactifs
- Timeout 300s minimum pour algorithmes genetiques

### Validation
- Toujours executer avant de valider (mode standard)
- Verifier git diff apres NotebookEdit
- Jamais git checkout sauf corruption majeure

## Templates de commandes

### Lancer une serie
```
Agent: series-improver
Target: MyIA.AI.Notebooks/<famille>
Workflow: <enrich|validate|fix|full>
Quality target: 85
Resume: true
```

### Reprendre apres crash
```
1. Lire .claude/progress/<hash>-progress.json
2. Identifier dernier notebook "in_progress"
3. Relancer series-improver avec resume=true
```

### Consulter progression
```
cat .claude/progress/*.json | jq '.statistics'
```
