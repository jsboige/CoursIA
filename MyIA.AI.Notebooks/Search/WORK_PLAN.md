# Search Series - Work Plan

> **Date de création**: 2026-03-07
> **Objectif**: Améliorer systématiquement les 40 notebooks de la série Search
> **Référence**: IMPROVEMENT_CHECKLIST.md

---

## Vue d'ensemble

```
PHASE 1: Exécution Critique        [██████████] 90%  (11 tâches)
PHASE 2: Consistance Structurelle  [████▓░░░░░░] 49%  (51 tâches)
PHASE 3: Complétion Contenu        [░░░░░░░░░░] 0%   (41 tâches)
PHASE 4: Qualité & Finalisation    [░░░░░░░░░░] 0%   (23 tâches)
                                      ────────────────
                                      TOTAL: 126 tâches
```

---

## PHASE 1: Exécution Critique (90% → 10/11 complétés)

### Batch 1.1: Notebooks Python ✓ (2 notebooks)

**État**: ✅ Terminé

| Notebook | Path | Status | Notes |
|----------|------|--------|-------|
| Search-6 | `Part1-Foundations/Search-6-AdversarialSearch.ipynb` | ✅ 100% | 8/8 code cells exécutés |
| Search-7 | `Part1-Foundations/Search-7-MCTS-And-Beyond.ipynb` | ✅ 100% | 8/8 code cells exécutés |

**Commandes MCP**:
```python
# Via MCP Jupyter
mcp__jupyter__execute_notebook(
    input_path="MyIA.AI.Notebooks/Search/Foundations/Search-6-AdversarialSearch.ipynb",
    mode="sync",
    report_mode="summary"
)
```

### Batch 1.2: Applications ✓ (2 notebooks)

**État**: ✅ Terminé

| Notebook | Path | Status | Notes |
|----------|------|--------|-------|
| App-14 | `Applications/Search/App-14-ConnectFour-Adversarial.ipynb` | ✅ 100% | 12/12 code cells exécutés |
| App-11 | `Applications/CSP/App-11-Picross.ipynb` | ✅ 100% | 13/16 cells exécutés (3 exercices vides) |

### Batch 1.3: Notebooks avec erreurs ✓ (1 notebook)

**État**: ✅ Terminé

| Notebook | Problème | Action | Status |
|----------|----------|--------|--------|
| Search-11-Metaheuristics | 1 erreur + 40% exécuté | Correction + exécution complète | ✅ 100% (15/15 cells) |

**Algorithmes MEALPy à valider**:
- PSO (Particle Swarm Optimization)
- GA (Genetic Algorithm)
- SA (Simulated Annealing)
- TS (Tabu Search)
- ACO (Ant Colony Optimization)
- WOA (Whale Optimization Algorithm)
- GWO (Grey Wolf Optimizer)

### Batch 1.4: Notebooks C# ⚠️ (2 notebooks)

**État**: ⚠️ Partiel (kernel .NET bloqué)

| Notebook | Path | Action | Status |
|----------|------|--------|--------|
| App-9b | `Applications/Hybrid/App-9b-EdgeDetection-CSharp.ipynb` | MCP .NET kernel | ⚠️ 78% (7/9 cells) |
| App-10b | `Applications/Hybrid/App-10b-Portfolio-CSharp.ipynb` | MCP .NET kernel | ✅ 100% (5/5 cells) |

**Note**: Le kernel .NET Interactive ne démarre pas via MCP (erreur: "Kernel died before replying"). App-9b reste partiellement exécuté.

---

## PHASE 2: Consistance Structurelle (49% → 25/51 complétés)

### Batch 2.1: Headers manquants (5 notebooks) ✓

**État**: ✅ Terminé

| Notebook | Header actuel | Action |
|----------|---------------|--------|
| CSP-4-Scheduling | ❌ Manquant | Ajouter |
| CSP-5-Optimization | ❌ Manquant | Ajouter |
| CSP-6-Hybridization | ❌ Manquant | Ajouter |
| CSP-9-Distributed | ❌ Manquant | Ajouter |
| Search-11-Metaheuristics | ❌ Manquant | Ajouter |

### Batch 2.2: Conclusions manquantes (22 notebooks) ✓

**État**: ✅ Terminé

**Format**:
```markdown
---

## Conclusion

Résumé des concepts clés :
- Point 1
- Point 2
- Point 3

**Voir aussi**: [Notebook connexe](url)
```

**Détail**:

- Part1-Foundations: 11/11 ✓ (3 ajoutés: Search-2,4,10 / 8 existaient déjà)
- Part2-CSP: 9/9 ✓ (tous ajoutés)
- Applications: 2/2 ✓ (App-3, App-4 ajoutés; les autres avaient déjà des conclusions)

### Batch 2.1: Headers manquants (5 notebooks) ✓

**État**: ✅ Terminé

| Notebook | Header actuel | Action |
|----------|---------------|--------|
| CSP-4-Scheduling | ❌ Manquant | Ajouter |
| CSP-5-Optimization | ❌ Manquant | Ajouter |
| CSP-6-Hybridization | ❌ Manquant | Ajouter |
| CSP-9-Distributed | ❌ Manquant | Ajouter |
| Search-11-Metaheuristics | ❌ Manquant | Ajouter |

### Batch 2.2: Conclusions manquantes (39 notebooks)

**Format**:
```markdown
---
## Conclusion

Résumé des concepts clés :
- Point 1
- Point 2
- Point 3

**Voir aussi**: [Notebook connexe](url)
```

**État**: ✅ Foundations (11/11) + CSP (9/9) + Applications (2/2) terminés

**Par section**:

- Part1-Foundations: 11/11 ✓ (3 ajoutés: Search-2,4,10 / 8 existaient déjà)
- Part2-CSP: 9/9 ✓ (tous ajoutés)
- Applications: 2/2 ✓ (App-3, App-4 ajoutés; les autres avaient déjà des conclusions)

**Note**: L'audit initial indiquait 39 notebooks manquant des conclusions, mais beaucoup en avaient déjà (Search-1,3,5,6,7,8,9,11, App-1,2,5,6,7,8,9,9b,10,10b,12,13,14). Seuls **3 notebooks Foundations**, **9 notebooks CSP** et **2 notebooks Applications** avaient vraiment besoin de conclusions.

### Batch 2.3: Cellules consécutives (11 notebooks)

**État**: ⏳ En cours (20/35 paires complétées)

| Notebook | Pairs | Localisation | Status |
|----------|-------|--------------|--------|
| Search-3 | 4 | Algorithmes A* | ⏳ À faire |
| Search-7 | 1 | MCTS | ✅ 1/1 |
| Search-8 | 3 | Algorithm X | ✅ 3/3 |
| Search-10 | 2 | Z3 | ✅ 2/2 |
| CSP-1 | 1 | Contraintes | ✅ 1/1 |
| CSP-2 | 3 | AC algorithms | ✅ 3/3 |
| CSP-3 | 5 | Techniques avancées | ✅ 5/5 |
| CSP-4 | 6 | Modèles scheduling | ⏳ À faire |
| CSP-5 | 5 | Méthodes optimisation | ⏳ À faire |
| CSP-6 | 2 | Approches hybrides | ✅ 2/2 |
| CSP-7 | 4 | Soft constraints | ✅ 4/4 |
| CSP-8 | 4 | Raisonnement temporel | ✅ 4/4 |

---

## PHASE 3: Complétion Contenu (0% → 41/41)

### Batch 3.1: Exécutions partielles - Foundations (3 notebooks)

**État**: ⏳ À faire

| Notebook | Actuel | Cible | Cells manquantes |
|----------|--------|-------|------------------|
| Search-2 | 73% | 100% | 7 cells |
| Search-4 | 86% | 100% | 3 cells |
| Search-10 | 95% | 100% | 1 cell |

### Batch 3.2: Exécutions partielles - CSP (9 notebooks)

**État**: ⏳ À faire

| Notebook | Actuel | Cible |
|----------|--------|-------|
| CSP-1 | 78% | 100% |
| CSP-2 | 84% | 100% |
| CSP-3 | 75% | 100% |
| CSP-4 | 58% | 100% |
| CSP-5 | 54% | 100% |
| CSP-6 | 89% | 100% |
| CSP-7 | 90% | 100% |
| CSP-8 | 90% | 100% |
| CSP-9 | 55% | 100% |

### Batch 3.3: Exécutions partielles - Applications (9 notebooks)

**État**: ⏳ À faire

**CSP Apps**: App-1 à App-8 (76-88% → 100%)
**Search Apps**: App-12 (partiel → 100%)

### Batch 3.4: Interprétations (Priorité haute)

**État**: ⏳ À faire

- Search-3: Outputs A*
- Search-8: Outputs Algorithm X
- CSP-2: Outputs AC algorithms
- CSP-3: Outputs techniques avancées

### Batch 3.5: Cross-références

**État**: ⏳ À faire

```
CSP-1 → App-1, App-2, App-3, App-4, App-5, App-6, App-7, App-8
Search-1,2 → App-12, App-14
Search-5,11 → App-13, App-17, App-18
CSP-4 → App-3, App-4, App-5
Search-6,7 → App-14
```

---

## PHASE 4: Qualité & Finalisation (0% → 23/23)

### Batch 4.1: Réduction ratio code (5 notebooks >50%)

**État**: ⏳ À faire

| Notebook | Ratio | Action |
|----------|-------|--------|
| CSP-4 | 63% | Ajouter explications |
| CSP-5 | 54% | Ajouter explications |
| CSP-6 | 53% | Ajouter explications |
| CSP-7 | 53% | Ajouter explications |
| CSP-8 | 53% | Ajouter explications |

### Batch 4.2: Visualisations

**État**: ⏳ À faire

- Graphiques algorithmes recherche (BFS, DFS, A*)
- Diagrammes réseaux contraintes (CSP)
- Plots qualité solution (optimisation)
- Visualisations MCTS (Search-7)

### Batch 4.3: Commentaires de code

**État**: ⏳ À faire

- Vérifier FR/EN pour metaheuristics
- Vérifier FR/EN pour local search
- Vérifier FR/EN pour CSP algorithms

### Batch 4.4: Validation finale + README

**État**: ⏳ À faire

**Checklist par notebook** (40):
- [ ] Pas d'erreurs d'exécution
- [ ] Outputs présents (non null)
- [ ] Header navigation correct
- [ ] Objectifs énoncés
- [ ] Prérequis listés
- [ ] Durée estimée
- [ ] Pas de cells consécutives
- [ ] Interprétations présentes
- [ ] Conclusion présente
- [ ] Cross-références
- [ ] Commentaires FR/EN
- [ ] Visualisations
- [ ] Algorithmes corrects

**Mise à jour README.md**:
- Statistiques de série
- État des notebooks
- Notes de version

---

## Ordre d'exécution recommandé

### Session 1: Phase 1 Batch 1.1
1. Exécuter Search-6
2. Exécuter Search-7
3. Vérifier outputs

### Session 2: Phase 1 Batch 1.2 + 1.3
1. Exécuter App-14
2. Vérifier App-11
3. Corriger Search-11

### Session 3: Phase 1 Batch 1.4
1. Exécuter App-9b (C#)
2. Exécuter App-10b (C#)

### Sessions 4-5: Phase 2
1. Headers manquants (5)
2. Conclusions (39)

### Sessions 6-8: Phase 3
1. Exécutions partielles Foundations
2. Exécutions partielles CSP
3. Exécutions partielles Applications
4. Interprétations + Cross-références

### Sessions 9-10: Phase 4
1. Réduction ratio code
2. Visualisations + Commentaires
3. Validation finale
4. Mise à jour README

---

## Commandes MCP utiles

### Exécution notebook (Papermill)
```python
mcp__jupyter__execute_notebook(
    input_path="path/to/notebook.ipynb",
    mode="sync",
    report_mode="summary"
)
```

### Exécution cellule par cellule (.NET)
```python
# 1. Démarrer kernel
mcp__jupyter__manage_kernel(action="start", kernel_name="csharp")

# 2. Lire cells
mcp__jupyter__read_cells(path="path/to/notebook.ipynb", mode="all")

# 3. Exécuter chaque cellule
mcp__jupyter__execute_on_kernel(kernel_id="...", mode="notebook_cell", ...)
```

### Inspecter outputs
```python
mcp__jupyter__inspect_notebook(path="path/to/notebook.ipynb", mode="outputs")
```

---

**Fin du Work Plan**
