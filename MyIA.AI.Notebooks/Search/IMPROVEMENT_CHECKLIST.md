# Search Series - Improvement Checklist

> **Date de création**: 2026-03-07
> **Basé sur**: REVIEW_NOTES.md
> **Objectif**: Guide systématique pour améliorer les 40 notebooks de la série Search

---

## PHASE 1: Exécution Critique (Semaine 1)

### 1.1 Notebooks 0% - Python

- [ ] **Search-6-AdversarialSearch.ipynb**
  - [ ] Vérifier environnement Python (recherche de jeux)
  - [ ] Exécuter via Papermill ou MCP
  - [ ] Valider outputs: minimax, alpha-beta pruning
  - [ ] Vérifier outputs visuels (arbres de jeu)

- [ ] **Search-7-MCTS-And-Beyond.ipynb**
  - [ ] Vérifier dépendances (numpy, matplotlib)
  - [ ] Exécuter via Papermill ou MCP
  - [ ] Valider outputs: MCTS, simulations
  - [ ] Ajouter cellule d'interprétation (1 pair consecutive)

### 1.2 Notebooks 0% - Applications

- [ ] **App-14-ConnectFour-Adversarial.ipynb**
  - [ ] Vérifier dépendances (pygame, numpy)
  - [ ] Exécuter via Papermill ou MCP
  - [ ] Valider outputs: algorithmes adversariaux
  - [ ] Vérifier outputs visuels (grille, simulation)

- [ ] **App-11-Picross.ipynb**
  - [ ] Vérifier existence du fichier
  - [ ] Exécuter si présent
  - [ ] Marquer "N/A" si absent

### 1.3 Notebooks avec erreurs

- [ ] **Search-11-Metaheuristics.ipynb**
  - [ ] Identifier l'erreur dans les outputs
  - [ ] Corriger le code problématique
  - [ ] Vérifier installation MEALPy
  - [ ] Compléter exécution (40% → 100%)
  - [ ] Valider tous les algorithmes: PSO, GA, SA, TS, ACO, WOA, GWO

### 1.4 Notebooks C# - Exécution MCP

- [ ] **App-9b-EdgeDetection-CSharp.ipynb**
  - [ ] Démarrer kernel .NET via MCP
  - [ ] Exécuter cellule par cellule
  - [ ] Valider outputs de traitement d'image

- [ ] **App-10b-Portfolio-CSharp.ipynb**
  - [ ] Démarrer kernel .NET via MCP
  - [ ] Exécuter cellule par cellule
  - [ ] Valider outputs d'optimisation

---

## PHASE 2: Consistance Structurelle (Semaine 2)

### 2.1 En-têtes standard manquants

Format attendu:
```markdown
# <Titre>

> **Navigation**: [← Précédent](url) | [Sommaire](url) | [Suivant →](url)
>
> **Objectifs**: ...
>
> **Prérequis**: ...
>
> **Durée estimée**: ...
```

- [ ] **CSP-4-Scheduling.ipynb** - Ajouter header complet
- [ ] **CSP-5-Optimization.ipynb** - Ajouter header complet
- [ ] **CSP-6-Hybridization.ipynb** - Ajouter header complet
- [ ] **CSP-9-Distributed.ipynb** - Ajouter header complet
- [ ] **Search-11-Metaheuristics.ipynb** - Ajouter header complet

### 2.2 Conclusions manquantes

Format attendu:
```markdown
---
## Conclusion

Résumé des concepts clés :
- Point 1
- Point 2
- Point 3

**Voir aussi**: [Notebook connexe](url)
```

**Part1-Foundations** (11 notebooks)
- [ ] Search-1-StateSpace.ipynb
- [ ] Search-2-Uninformed.ipynb
- [ ] Search-3-Informed.ipynb
- [ ] Search-4-LocalSearch.ipynb
- [ ] Search-5-GeneticAlgorithms.ipynb
- [ ] Search-6-AdversarialSearch.ipynb
- [ ] Search-7-MCTS-And-Beyond.ipynb
- [ ] Search-8-DancingLinks.ipynb
- [x] Search-9-LinearProgramming.ipynb (DÉJÀ FAIT)
- [ ] Search-10-SymbolicAutomata.ipynb
- [ ] Search-11-Metaheuristics.ipynb

**Part2-CSP** (9 notebooks)
- [ ] CSP-1-Fundamentals.ipynb
- [ ] CSP-2-Consistency.ipynb
- [ ] CSP-3-Advanced.ipynb
- [ ] CSP-4-Scheduling.ipynb
- [ ] CSP-5-Optimization.ipynb
- [ ] CSP-6-Hybridization.ipynb
- [ ] CSP-7-Soft.ipynb
- [ ] CSP-8-Temporal.ipynb
- [ ] CSP-9-Distributed.ipynb

**Applications/CSP** (11 notebooks)
- [ ] App-1-NQueens.ipynb
- [ ] App-2-GraphColoring.ipynb
- [ ] App-3-NurseScheduling.ipynb
- [ ] App-4-JobShopScheduling.ipynb
- [ ] App-5-Timetabling.ipynb
- [ ] App-6-Minesweeper.ipynb
- [ ] App-7-Wordle.ipynb
- [ ] App-8-MiniZinc.ipynb
- [ ] App-11-Picross.ipynb (si existe)
- [ ] App-15-SportsScheduling.ipynb
- [ ] App-16-Crossword-CSP.ipynb

**Applications/Hybrid** (7 notebooks)
- [ ] App-9-EdgeDetection.ipynb
- [ ] App-9b-EdgeDetection-CSharp.ipynb
- [ ] App-10-Portfolio.ipynb
- [ ] App-10b-Portfolio-CSharp.ipynb
- [ ] App-13-TSP-Metaheuristics.ipynb
- [ ] App-17-VRP-Logistics.ipynb
- [ ] App-18-HyperparameterTuning.ipynb

**Applications/Search** (2 notebooks)
- [ ] App-12-ConnectFour.ipynb
- [ ] App-14-ConnectFour-Adversarial.ipynb

### 2.3 Cellules de code consécutives

Pour chaque pair consécutive, ajouter une cellule markdown d'interprétation:

- [ ] **Search-3-Informed.ipynb** (4 pairs)
- [ ] **Search-7-MCTS-And-Beyond.ipynb** (1 pair)
- [ ] **Search-8-DancingLinks.ipynb** (3 pairs)
- [ ] **Search-10-SymbolicAutomata.ipynb** (2 pairs)
- [ ] **CSP-1-Fundamentals.ipynb** (1 pair)
- [ ] **CSP-2-Consistency.ipynb** (3 pairs)
- [ ] **CSP-3-Advanced.ipynb** (5 pairs)
- [ ] **CSP-4-Scheduling.ipynb** (6 pairs)
- [ ] **CSP-5-Optimization.ipynb** (5 pairs)
- [ ] **CSP-6-Hybridization.ipynb** (2 pairs)
- [ ] **CSP-7-Soft.ipynb** (4 pairs)
- [ ] **CSP-8-Temporal.ipynb** (4 pairs)

---

## PHASE 3: Complétion de Contenu (Semaine 3)

### 3.1 Exécutions partielles

- [ ] **Search-2-Uninformed.ipynb** (73% → 100%)
  - [ ] Identifier les 7 cellules avec null outputs
  - [ ] Déterminer si intentionnel ou incomplet
  - [ ] Compléter si nécessaire

- [ ] **Search-4-LocalSearch.ipynb** (86% → 100%)
  - [ ] Compléter les 3 cellules manquantes

- [ ] **Search-10-SymbolicAutomata.ipynb** (95% → 100%)
  - [ ] Compléter la 1 cellule manquante

**Série CSP**
- [ ] CSP-1-Fundamentals.ipynb (78% → 100%)
- [ ] CSP-2-Consistency.ipynb (84% → 100%)
- [ ] CSP-3-Advanced.ipynb (75% → 100%)
- [ ] CSP-4-Scheduling.ipynb (58% → 100%)
- [ ] CSP-5-Optimization.ipynb (54% → 100%)
- [ ] CSP-6-Hybridization.ipynb (89% → 100%)
- [ ] CSP-7-Soft.ipynb (90% → 100%)
- [ ] CSP-8-Temporal.ipynb (90% → 100%)
- [ ] CSP-9-Distributed.ipynb (55% → 100%)

**Applications/CSP**
- [ ] App-1-NQueens.ipynb (84% → 100%)
- [ ] App-2-GraphColoring.ipynb (86% → 100%)
- [ ] App-3-NurseScheduling.ipynb (86% → 100%)
- [ ] App-4-JobShopScheduling.ipynb (88% → 100%)
- [ ] App-5-Timetabling.ipynb (76% → 100%)
- [ ] App-6-Minesweeper.ipynb (84% → 100%)
- [ ] App-7-Wordle.ipynb (85% → 100%)
- [ ] App-12-ConnectFour.ipynb (partiel → 100%)

### 3.2 Cellules d'interprétation

Priorité haute (outputs complexes):
- [ ] **Search-3-Informed.ipynb** - Outputs A*
- [ ] **Search-8-DancingLinks.ipynb** - Outputs Algorithm X
- [ ] **CSP-2-Consistency.ipynb** - Outputs AC algorithms
- [ ] **CSP-3-Advanced.ipynb** - Outputs techniques avancées

### 3.3 Cross-références

- [ ] Ajouter références CSP-1 → App-1 à App-8
- [ ] Ajouter références Search-1, Search-2 → App-12, App-14
- [ ] Ajouter références Search-5, Search-11 → App-13, App-17, App-18
- [ ] Ajouter références CSP-4 → App-3, App-4, App-5
- [ ] Ajouter références Search-6, Search-7 → App-14

---

## PHASE 4: Amélioration Qualité (Semaine 4)

### 4.1 Réduction ratio code/explication

Notebooks avec >50% de code:
- [ ] **CSP-4-Scheduling.ipynb** (63%) - Ajouter explications
- [ ] **CSP-5-Optimization.ipynb** (54%) - Ajouter explications
- [ ] **CSP-6-Hybridization.ipynb** (53%) - Ajouter explications
- [ ] **CSP-7-Soft.ipynb** (53%) - Ajouter explications
- [ ] **CSP-8-Temporal.ipynb** (53%) - Ajouter explications

### 4.2 Visualisations

- [ ] Graphiques pour algorithmes de recherche (BFS, DFS, A*)
- [ ] Diagrammes de réseaux de contraintes (CSP)
- [ ] Plots de qualité de solution (optimisation)
- [ ] Visualisations MCTS (Search-7)

### 4.3 Commentaires de code

- [ ] Vérifier commentaires en français/anglais
- [ ] Priorité: metaheuristics, local search, CSP algorithms
- [ ] Ajouter commentaires pour algorithmes complexes

### 4.4 Validation finale

Pour chaque notebook (checklist complète):
- [ ] Toutes les cellules de code s'exécutent sans erreur
- [ ] Tous les outputs sont présents (non null)
- [ ] Header navigation présent et correct
- [ ] Objectifs d'apprentissage énoncés
- [ ] Prérequis listés
- [ ] Durée estimée indiquée
- [ ] Aucune cellule de code consécutive sans markdown
- [ ] Toutes les outputs significatives ont interprétation
- [ ] Conclusion résumant les concepts clés
- [ ] Cross-références vers notebooks connexes
- [ ] Commentaires de code en français/anglais
- [ ] Visualisations incluses si approprié
- [ ] Correction algorithmique vérifiée

---

## Résumé des tâches

### Compteurs

| Phase | Tâches totales | Complétées | Restantes | Progression |
|-------|---------------|-----------|-----------|-------------|
| **Phase 1** | 11 | 0 | 11 | 0% |
| **Phase 2** | 51 | 1 | 50 | 2% |
| **Phase 3** | 41 | 0 | 41 | 0% |
| **Phase 4** | 23 | 0 | 23 | 0% |
| **TOTAL** | **126** | **1** | **125** | **1%** |

### Ordre recommandé

1. **Commencer par Phase 1** - Exécution critique (bloqueur pour le reste)
2. **Puis Phase 2** - Structure (gagne en clarté rapidement)
3. **Ensuite Phase 3** - Contenu (améliore la pédagogie)
4. **Enfin Phase 4** - Qualité (polissage final)

---

**Notes importantes:**
- Cette checklist est un **document de travail** (TEMPORAIRE)
- Elle sera mise à jour au fur et à mesure de la progression
- Cocher les cases au fur et à mesure de la completion
- Mettre à jour les compteurs après chaque session de travail

---

**Fin de Checklist**
