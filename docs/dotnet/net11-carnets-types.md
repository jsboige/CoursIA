# Sélection des 3 carnets types pour la mesure .NET 11 (P1 #18695)

Part of #18769.

## Méthode

Trois carnets représentatifs du périmètre CoursIA, choisis pour couvrir les trois profils de charge identifiés dans l'Epic :

1. **GenAI/SemanticKernel** — awaits profonds, I/O réseau (APIs OpenAI/Anthropic), allocations de strings/JSON.
2. **ML.NET Backtester** — calcul numérique intensif, LINQ, allocations de structs, accès mémoire dense.
3. **Probas/Infer** — allocations massives (matrices, vecteurs), boucles serrées, collecte GC.

Critères communs : carnet exécutable (C.2), présence d'outputs, taille suffisante pour exercer le runtime, pas de dépendance GPU-only (règle F).

## Sélection

| Type | Carnet | Taille | Cellules code | Justification |
|---|---|---:|---:|---|
| GenAI/SK | `GenAI/SemanticKernel/02-SemanticKernel-Advanced.ipynb` | 1 927 lignes | 10 | Await profonds sur OpenAI/Anthropic, parsing JSON, strings. Couvre le profil I/O async. |
| ML.NET Backtester | `QuantConnect/ML-Training-Pipeline/m12_har_rv_j_research.ipynb` | 704 lignes | 5 | Modèle HAR-RV-J (regressions linéaires, matrices), ML.NET 6 preview. Couvre le profil numérique. |
| Probas | `Probas/Applications/Percolation/Percolation-01-Supercritique-Python.ipynb` | 1 358 lignes | 11 | Percolation sur grille L×L, allocations de tableaux numpy, boucles de simulation. Couvre le profil allocations/GC. |

## Ce que ce livrable n'est pas

- Pas de banc BenchmarkDotNet : c'est #18770.
- Pas de mesure .NET 11 : c'est #18771.
- Pas de modification des carnets : la sélection est une lecture, pas une réécriture.

## Suite

#18770 (banc d'essai BenchmarkDotNet in-repo par sous-module) peut commencer dès que cette sélection est validée. #18771 (mesure delta .NET 9 → 11) en dépend.
