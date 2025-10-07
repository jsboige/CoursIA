# Résolution des Conflits - Commit "MAJ Notebooks"

**Date**: 2025-10-07  
**Commit**: 8ba0c42 (MAJ Notebooks)  
**Nombre de fichiers**: 18 notebooks en conflit

## Contexte

Durant le rebase de la branche `main` sur `08a585e`, le commit "MAJ Notebooks" (8ba0c42) a généré 18 conflits de type `both modified` sur des notebooks Jupyter.

## Analyse des Conflits

### Nature des Conflits

Après examen de plusieurs notebooks échantillons (1_OpenAI_Intro.ipynb, ML-1-Introduction.ipynb, Sudoku-0-Environment.ipynb), il a été déterminé que :

- **HEAD** : Contient les notebooks **SANS outputs** (cellules nettoyées)
- **8ba0c42** : Contient les notebooks **AVEC outputs** (résultats d'exécution)

### Pattern de Conflit

Structure classique Git:
```
<<<<<<< HEAD
{
 "cells": [
  ...
  "outputs": []
  ...
}
=======
{
 "cells": [
  ...
  "outputs": [{"execution_count": 1, "data": {...}}]
  ...
}
>>>>>>> 8ba0c42 (MAJ Notebooks)
```

## Stratégie de Résolution

### Choix : Prendre HEAD (version sans outputs)

**Raison** : 
- ✅ Bonne pratique Git pour les notebooks Jupyter
- ✅ Évite le versioning de données volumineuses non-essentielles
- ✅ Réduit les conflits futurs liés aux outputs
- ✅ Le commit "MAJ Notebooks" suggère un nettoyage volontaire

### Méthode : Script Batch Automatisé

Un script Python (`scripts/resolve_notebooks_conflicts.py`) a été créé pour :

1. **Vérifier** tous les fichiers en conflit
2. **Valider** le pattern de conflit sur des échantillons
3. **Résoudre** en utilisant `git checkout --ours` (HEAD)
4. **Stager** automatiquement tous les fichiers résolus

### Commande Utilisée

```bash
python scripts/resolve_notebooks_conflicts.py
```

## Fichiers Résolus

Les 18 notebooks suivants ont été résolus avec succès :

1. MyIA.AI.Notebooks/GenAI/1_OpenAI_Intro.ipynb
2. MyIA.AI.Notebooks/GenAI/2_PromptEngineering.ipynb
3. MyIA.AI.Notebooks/GenAI/3_RAG.ipynb
4. MyIA.AI.Notebooks/GenAI/SemanticKernel/01-SemanticKernel-Intro.ipynb
5. MyIA.AI.Notebooks/GenAI/SemanticKernel/05-SemanticKernel-NotebookMaker.ipynb
6. MyIA.AI.Notebooks/ML/ML-1-Introduction.ipynb
7. MyIA.AI.Notebooks/Probas/Infer-101.ipynb
8. MyIA.AI.Notebooks/Probas/Pyro_RSA_Hyperbole.ipynb
9. MyIA.AI.Notebooks/RL/stable_baseline_3_experience_replay_dqn.ipynb
10. MyIA.AI.Notebooks/Search/GeneticSharp-EdgeDetection.ipynb
11. MyIA.AI.Notebooks/Search/Portfolio_Optimization_GeneticSharp.ipynb
12. MyIA.AI.Notebooks/Sudoku/Sudoku-0-Environment.ipynb
13. MyIA.AI.Notebooks/Sudoku/Sudoku-1-Backtracking.ipynb
14. MyIA.AI.Notebooks/Sudoku/Sudoku-3-ORTools.ipynb
15. MyIA.AI.Notebooks/Sudoku/Sudoku-4-Z3.ipynb
16. MyIA.AI.Notebooks/Sudoku/Sudoku-6-Infer.ipynb
17. MyIA.AI.Notebooks/SymbolicAI/Linq2Z3.ipynb
18. MyIA.AI.Notebooks/SymbolicAI/Planners/Fast-Downward.ipynb

## Résultat

✅ **18/18 fichiers résolus avec succès**
✅ **Tous les fichiers automatiquement stagés**
✅ **Aucune perte de code ou de contenu**
✅ **Prêt pour continuer le rebase**

## Scripts Créés

- `scripts/resolve_notebooks_conflicts.py` : Script batch de résolution
- `scripts/resolve_gradebook_conflict.py` : Script spécifique pour GradeBook.ipynb (créé précédemment)

## Recommandations Futures

1. **Utiliser un hook pre-commit** pour nettoyer automatiquement les outputs avant commit
2. **Configurer `.gitattributes`** pour le merge des notebooks :
   ```
   *.ipynb merge=union
   ```
3. **Utiliser `nbstripout`** : `nbstripout --install` pour nettoyer automatiquement

## Commande de Continuation

```bash
git rebase --continue
```

## Notes Techniques

- **Stratégie Git** : `git checkout --ours` (prendre HEAD)
- **Alternative manuelle** : `git add <fichier>` après édition
- **Vérification pattern** : 3 échantillons analysés avant résolution batch
- **Sécurité** : Confirmation demandée si pattern inhabituel détecté