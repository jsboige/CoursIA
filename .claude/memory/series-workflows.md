# Series Improvement Workflows - Project Memory

Ce fichier persiste l'etat des series de notebooks en cours d'amelioration.

## Sessions actives

| Serie | Workflow | Status | Progression | Dernier checkpoint |
|-------|----------|--------|-------------|-------------------|
| (aucune session active) | - | - | - | - |

## Series completes

| Serie | Workflow | Date | Notebooks | Score moyen |
|-------|----------|------|-----------|-------------|
| GenAI/Image/01-Foundation | validate | 2026-02-28 | 5/5 | 100% |
| GenAI/Video | validate | 2026-03-05 | 16/16 | 100% |
| GenAI/Texte | validate | 2026-03-06 | 11/11 | 100% |
| Search/Part1-Foundations | validate | 2026-03-07 | 11/11 | 53.1% (structure) |
| Search/Part1-Foundations | enrich | 2026-03-07 | 11/11 | 12 cells added |
| Search/Part2-CSP | enrich | 2026-03-07 | 9/9 | 15 cells added |
| GenAI/Image | enrich | 2026-03-08 | 7/16 completed | 61 cells added |

## Detail des series Search (Mars 2026)

### Search/Part1-Foundations - Validation (2026-03-07)

**Workflow**: validate (structure, pedagogie, syntaxe)
**Target**: MyIA.AI.Notebooks/Search/Part1-Foundations
**Resultats**:
- 11/11 notebooks valides
- Score moyen: 53.1/100 (structure uniquement)
- Tous les objectifs pedagogiques presents
- Ratios markdown: 57-67% (excellent)

| Notebook | Score | Cells | MD Ratio | Sections |
|----------|-------|-------|----------|----------|
| Search-1-StateSpace | 53.2 | 48 | 62.5% | 29 |
| Search-2-Uninformed | 54.8 | 61 | 57.4% | 26 |
| Search-3-Informed | 53.5 | 52 | 61.5% | 30 |
| Search-4-LocalSearch | 53.4 | 58 | 62.1% | 25 |
| Search-5-GeneticAlgorithms | 53.6 | 62 | 61.3% | 33 |
| Search-6-AdversarialSearch | 54.0 | 20 | 60.0% | 12 |
| Search-7-MCTS-And-Beyond | 54.6 | 19 | 57.9% | 11 |
| Search-8-DancingLinks | 52.0 | 48 | 66.7% | 25 |
| Search-9-LinearProgramming | 52.8 | 39 | 64.1% | 22 |
| Search-10-SymbolicAutomata | 52.0 | 63 | 66.7% | 41 |
| Search-11-Metaheuristics | 47.2 | 44 | 65.9% | 22 |

### Search/Part1-Foundations - Enrichment (2026-03-07)

**Workflow**: enrich (ajout interpretations pedagogiques)
**Target**: MyIA.AI.Notebooks/Search/Part1-Foundations
**Resultats**:
- 11/11 notebooks traites
- 12 cellules markdown ajoutees
- 3 notebooks enrichis (Search-1, 2, 3), 8 deja complets

| Notebook | Cells Added | Enrichments |
|----------|-------------|-------------|
| Search-1-StateSpace | 5 | Explosion combinatoire, BFS solution, classification, visualisation, dynamique taquin |
| Search-2-Uninformed | 5 | Comparaison BFS/DFS, resultat DFS, trace DFS, resultat BFS, trace BFS |
| Search-3-Informed | 2 | Impact heuristique non admissible, A* avec obstacles |
| Search-4-LocalSearch | 0 | Already complete |
| Search-5-GeneticAlgorithms | 0 | Already complete |
| Search-6-AdversarialSearch | 0 | Theoretical only |
| Search-7-MCTS-And-Beyond | 0 | Theoretical only |
| Search-8-DancingLinks | 0 | Already complete |
| Search-9-LinearProgramming | 0 | Already complete |
| Search-10-SymbolicAutomata | 0 | Already complete |
| Search-11-Metaheuristics | 0 | Already complete |

### Search/Part2-CSP - Enrichment (2026-03-07)

**Workflow**: enrich
**Target**: MyIA.AI.Notebooks/Search/Part2-CSP
**Resultats**:
- 9/9 notebooks traites
- 15 cellules markdown ajoutees
- Focus sur CSP-4-Scheduling (+20.3% ratio)

| Notebook | MD Ratio | Cells Added |
|----------|----------|-------------|
| CSP-1-Fundamentals | 63.0% | 0 |
| CSP-2-Consistency | 59.7% | 0 |
| CSP-3-Advanced | 61.5% | 0 |
| CSP-4-Scheduling | 57.1% | 9 (36.8% -> 57.1%) |
| CSP-5-Optimization | 45.8% | 1 |
| CSP-6-Hybridization | 47.1% | 1 |
| CSP-7-Soft | 47.4% | 1 |
| CSP-8-Temporal | 47.4% | 1 |
| CSP-9-Distributed | 52.2% | 1 |

## Detail des series GenAI (Mars 2026)

### GenAI/Image - Enrichment (2026-03-08)

**Workflow**: enrich (ajout interpretations pedagogiques)
**Target**: MyIA.AI.Notebooks/GenAI/Image
**Progression**: 7/16 completes
**Resultats**: 61 cellules ajoutees, ratio moyen 25.4% -> 55.3%

| Notebook | Initial | Final | Cells Added |
|----------|---------|-------|-------------|
| 01-1-OpenAI-DALL-E-3 | 18.2% | 47.1% | 6 |
| 01-2-GPT-5-Image-Generation | 15.4% | 47.6% | 8 |
| 02-4-Z-Image-Lumina2 | 33.3% | 60.0% | 4 |
| 03-3-Performance-Optimization | 38.5% | 61.9% | 24 |
| 04-1-Educational-Content | 25.0% | 57.1% | 6 |
| 04-2-Creative-Workflows | 25.0% | 57.1% | 6 |
| 04-3-Production-Integration | 22.2% | 56.2% | 7 |
| 01-3-Stable-Diffusion-Forge | 50.0% | - | pending |
| 01-4-ComfyUI-Introduction | 46.7% | - | pending |
| 01-5-Qwen-Image-Edit | 40.0% | - | pending |
| 02-1-Workflow-Optimization | 45.5% | - | pending |
| 02-2-ControlNet-Integration | 42.9% | - | pending |
| 02-3-LoRA-FineTuning | 44.4% | - | pending |
| 03-1-Prompt-Engineering | 50.0% | - | pending |
| 03-2-Style-Transfer | 50.0% | - | pending |
| 04-4-Project-Image-Editor | 55.6% | - | pending |

## Patterns d'erreurs frequents par famille

### GenAI
- **dotenv path**: Utiliser `../.env` (relatif au sous-repertoire)
- **gpt-4o-mini obsolete**: Migrer vers gpt-5-mini
- **ComfyUI timeout**: Verifier COMFYUI_AUTH_TOKEN avant execution

### Search/Part1 (Python)
- **State space explosion**: Exercices sur taquin > 4x4 explosent
- **Visualization requires matplotlib**: Pour graphes et grilles
- **French graphs**: Labels et titres en francais

### Search/Part2 (CSP)
- **Consistency algorithms**: Forward checking vs ARC consistency
- **Scheduling CSP**: Variables = taches, Domaines = creneaux
- **Optimization**: Minimiser cout vs maximiser satisfaction
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
- **BOTTOM-to-TOP rule**: Toujours travailler du bas vers le haut pour eviter decalage indices
- **Re-reading obligatoire**: Apres chaque insertion batch, relire le notebook
- **Ratio markdown cible**: ~40-60% markdown pour contenu pedagogique
- **Domain vocabulary**: Utiliser le vocabulaire specifique du domaine (zero-sum game, CSP, backtracking, etc.)

### Execution
- .NET + `#!import`: cell-by-cell UNIQUEMENT
- BATCH_MODE=true pour widgets interactifs
- Timeout 300s minimum pour algorithmes genetiques

### Validation
- Toujours executer avant de valider (mode standard)
- Verifier git diff apres NotebookEdit
- Jamais git checkout sauf corruption majeure

### Quality Metrics
- **No consecutive code cells**: Separer par markdown
- **Standard headers**: Objectifs, prerequis, duree
- **Professional tone**: Pas d'emojis, langue francaise
- **Pedagogical flow**: Introduction -> Execution -> Interpretation
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
<<<<<<< HEAD
=======

## Historique des sessions

### 2026-03-09: Creation du fichier series-workflows.md
- Synchronisation avec les memoires des agents notebook-enricher
- Consolidation des fichiers de progression .claude/progress/
- Index des workflows completes et en cours

### 2026-03-08: Enrichment GenAI/Image (partiel)
- 7/16 notebooks enrichis
- 61 cellules markdown ajoutees
- Progression sauvegardee dans genai-image-enrich.json

### 2026-03-07: Validation et Enrichment Search
- Search/Part1-Foundations: 11/11 validates + 12 cells added
- Search/Part2-CSP: 9/9 enrichis + 15 cells added
- Sessions sauvegardees dans search-part1-*.json et csp-part2-progress.json

## Agents concernes

- **notebook-enricher**: Ajout de contenu pedagogique
- **notebook-validator**: Verification structure et syntaxe
- **series-improver**: Orchestration des workflows multi-notebooks
- **readme-updater**: Mise a jour des README de series

## Liens vers les memoires specifiques

- [notebook-enricher/MEMORY.md](../.claude/agent-memory/notebook-enricher/MEMORY.md) - Patterns d'enrichment
- [notebook-enricher/enrichment-log-*.md](../.claude/agent-memory/notebook-enricher/) - Logs detailles des sessions
- [MEMORY.md](../.claude/memory/MEMORY.md) - Memoire principale du projet
>>>>>>> origin/main
