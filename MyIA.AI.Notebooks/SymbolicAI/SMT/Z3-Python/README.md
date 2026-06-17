# Série Z3-Python - Résolution de contraintes SMT en Python

[← SMT](../README.md) | [Z3 C# (Z3.Linq) →](../Z3/README.md)

## Série en quelques mots

L'API z3-py expose l'intégralité du solveur Z3 en Python — `Solver`, `Optimize`, tactiques, théories `BitVec`/`Array`/`String`. Série complète de **6 notebooks** (z3-solver + matplotlib), de la satisfaction de contraintes à l'optimisation avancée.

**À qui s'adresse cette série** : étudiants en IA, développeurs Python souhaitant découvrir la programmation par contraintes, et tout curieux voulant comprendre comment exprimer un problème non pas comme un algorithme de résolution, mais comme un ensemble de contraintes que le solveur satisfait automatiquement. Aucun prérequis en logique formelle n'est supposé : les notebooks partent de la syntaxe de base de z3-py pour monter progressivement vers l'optimisation et la modélisation de problèmes combinatoires.

## Présentation

**Z3** (Microsoft Research) est un solveur SMT (*Satisfiability Modulo Theories*) qui résout des systèmes de contraintes sur des entiers, des réels, des booléens, des vecteurs de bits, des tableaux et des chaînes. Cette série utilise **z3-py** (package pip `z3-solver`), le binding Python officiel qui expose **l'intégralité** de l'API Z3 : `Solver`, `Optimize`, théories (BitVec, Array, String, Real), tactiques et quantificateurs.

L'intérêt pédagogique : au lieu d'écrire un algorithme de backtracking pour un Sudoku ou un planificateur, on décrit les contraintes (une seule valeur par case, pas de doublon par ligne) et le solveur trouve les solutions. Ce changement de paradigme — de l'impératif au déclaratif — est au cœur de cette série.

### Python (z3-py) vs C# (Z3.Linq)

Une série sœur existe en C# : [SymbolicAI/Z3/](../Z3/README.md), basée sur le binding **Z3.Linq** qui traduit des expressions LINQ en formules SMT. La série Python présentée ici va plus loin : z3-py n'impose **aucune couche déclarative restrictive**, ce qui donne accès à l'API complète (tactiques, `Optimize`, théories de bas niveau).

| Aspect | Z3.Linq (C#) | z3-py (Python, cette série) |
|--------|--------------|------------------------------|
| **Binding** | LINQ -> Z3 (déclaratif) | API Z3 directe (impératif-symbolique) |
| **Theories** | Entiers, arrays (via lambdas) | BitVec, Array, String, Real, quantificateurs |
| **Optimisation** | Limitée | `Optimize` complet (maximize/minimize) |
| **Tactiques** | Non exposées | `Tactic`, `Then`, `Repeat` |
| **Courbe** | Syntaxe C# familière | API Python explicite, plus de contrôle |

### Déclaratif vs Impératif

| Aspect | Impératif (classique) | Déclaratif (Z3) |
|--------|----------------------|---------------------|
| **Approche** | Écrire l'algorithme de résolution | Décrire les contraintes, laisser le solveur résoudre |
| **Complexité** | Backtracking, heuristiques, pruning | Syntaxe Python naturelle |
| **Évolution** | Modifier l'algorithme pour chaque nouveau problème | Ajouter des contraintes, le solveur s'adapte |
| **Vérification** | Tester les solutions | Les solutions satisfont les contraintes par construction |
| **Limite** | Difficile à généraliser | Performance sur les très grandes instances |

## Vue d'ensemble

| # | Notebook | Sujet | Durée | Statut |
|---|----------|-------|------|--------|
| 01 | [Introduction](Z3-Python-01-Introduction.ipynb) | `Solver`, `Int`/`Bool`/`Real`, sat/unsat, `Optimize` | ~30 min | PRODUCTION |
| 02 | [Sudoku](Z3-Python-02-Sudoku.ipynb) | Sudoku comme CSP, `Distinct`, visualisation matplotlib | ~25 min | PRODUCTION |
| 03 | [Tactiques et théories](Z3-Python-03-Tactics.ipynb) | `Tactic`, `BitVec`, `Array` | ~35 min | PRODUCTION |
| 04 | [Chaînes et expressions régulières](Z3-Python-04-Strings-Regex.ipynb) | `String`, `Re` (théorie des chaînes Z3) | ~30 min | PRODUCTION |
| 05 | [Quantificateurs et preuves](Z3-Python-05-Quantifiers-Proofs.ipynb) | `ForAll`, `Exists`, preuves par réfutation, `unknown` | ~35 min | PRODUCTION |
| 06 | [Optimisation avancée](Z3-Python-06-Advanced-Optimization.ipynb) | Pareto, objectifs multiples, `Optimize` hiérarchique, MaxSAT | ~40 min | PRODUCTION |

### Fil pédagogique

1. **Notebook 01** pose les bases : le patron `Solver()`, les types de base (`Int`, `Bool`, `Real`), les réponses `sat`/`unsat`/`unknown`, et l'optimisation avec `Optimize`
2. **Notebook 02** applique l'approche déclarative au Sudoku : modélisation par `Distinct`, résolution et visualisation (donné en noir / résolu en bleu)
3. **Notebook 03** explore les tactiques (`simplify`, `Then`, `OrElse`), les théories `BitVec` (arithmétique modulaire) et `Array` (tableaux symboliques)
4. **Notebook 04** introduit la théorie des chaînes : `String`, `Contains`, `IndexOf`, `Replace`, et les expressions régulières (`Re`, `Star`, `Range`, `InRe`)
5. **Notebook 05** aborde les quantificateurs (`ForAll`, `Exists`) et la notion de preuve formelle par réfutation (une formule est valide si sa négation est insatisfiable), avec le cas honnête `unknown`
6. **Notebook 06** explore l'optimisation avancée : contraintes hiérarchiques pondérées, objectifs multiples, front de Pareto et MaxSAT (contraintes souples)

## Prérequis

| Besoin | Détail |
|--------|--------|
| **Python 3.10+** | [Download](https://www.python.org/downloads/) |
| **z3-solver** | `pip install z3-solver` |
| **matplotlib** | `pip install matplotlib` (visualisation, notebook 02) |
| **Kernel Jupyter** | `python3` |

> Les notebooks sont autonomes : les imports sont inclus dans la cellule de setup de chaque notebook. Le package s'appelle `z3-solver` (et non `z3`).

```bash
# Installation complete
pip install -r requirements.txt
```

## Objectifs d'apprentissage

À l'issue de cette série, l'étudiant sera capable de :

1. **Modéliser** un problème de satisfaction de contraintes en Python avec z3-py
2. **Utiliser** les types et théories Z3 (`Int`, `Real`, `Bool`, `BitVec`, `Array`, `String`)
3. **Optimiser** une fonction objectif sous contraintes (`Optimize`)
4. **Comparer** l'approche déclarative (Z3) aux approches impératives (backtracking, CP)
5. **Appliquer** la résolution SMT à des problèmes concrets (Sudoku, ordonnancement, allocation)

## Contexte technique

**z3-py** combine deux technologies :

- **Z3** : solveur SMT (*Satisfiability Modulo Theories*) capable de résoudre des contraintes sur des entiers, réels, booléens, vecteurs de bits, tableaux et chaînes
- **Python** : le binding `z3-solver` expose l'API C++ de Z3 via des wrappers Python, avec surcharge des opérateurs (`==`, `+`, `*`) pour construire des formules symboliques de façon naturelle

### Liens

- [Z3 Guide (officiel)](https://microsoft.github.io/z3guide/) — documentation et tutoriels
- [Z3 Python API](https://z3prover.github.io/api/html/namespacez3py.html) — référence de l'API z3-py
- [PyPI : z3-solver](https://pypi.org/project/z3-solver/) — package pip
- [Série Z3 C# (Z3.Linq)](../Z3/README.md) — série sœur en .NET 9
- [Série Sudoku](../../../Sudoku/README.md) — compare Z3 à 10 autres approches algorithmiques
