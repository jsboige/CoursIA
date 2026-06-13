# Serie Z3-Python - Resolution de contraintes SMT en Python

**Navigation** : [Index SymbolicAI](../README.md) | [Serie Z3 C# (Z3.Linq)](../Z3/README.md) | [Index general](../../README.md)

## Serie en quelques mots

**2 notebooks (en cours) | 1 kernel | z3-solver (Python) | matplotlib**

**A qui s'adresse cette serie** : etudiants en IA, developpeurs Python souhaitant decouvrir la programmation par contraintes, et tout curieux voulant comprendre comment exprimer un probleme non pas comme un algorithme de resolution, mais comme un ensemble de contraintes que le solveur satisfait automatiquement. Aucun prerequis en logique formelle n'est suppose : les notebooks partent de la syntaxe de base de z3-py pour monter progressivement vers l'optimisation et la modelisation de problemes combinatoires.

## Presentation

**Z3** (Microsoft Research) est un solveur SMT (*Satisfiability Modulo Theories*) qui resout des systemes de contraintes sur des entiers, des reels, des booleens, des vecteurs de bits, des tableaux et des chaines. Cette serie utilise **z3-py** (package pip `z3-solver`), le binding Python officiel qui expose **l'integralite** de l'API Z3 : `Solver`, `Optimize`, theories (BitVec, Array, String, Real), tactiques et quantificateurs.

L'interet pedagogique : au lieu d'ecrire un algorithme de backtracking pour un Sudoku ou un planificateur, on decrit les contraintes (une seule valeur par case, pas de doublon par ligne) et le solveur trouve les solutions. Ce changement de paradigme — de l'imperatif au declaratif — est au coeur de cette serie.

### Python (z3-py) vs C# (Z3.Linq)

Une serie sœur existe en C# : [SymbolicAI/Z3/](../Z3/README.md), basee sur le binding **Z3.Linq** qui traduit des expressions LINQ en formules SMT. La serie Python presente ici va plus loin : z3-py n'impose **aucune couche declarative restrictive**, ce qui donne acces a l'API complete (tactiques, `Optimize`, theories de bas niveau).

| Aspect | Z3.Linq (C#) | z3-py (Python, cette serie) |
|--------|--------------|------------------------------|
| **Binding** | LINQ -> Z3 (declaratif) | API Z3 directe (impératif-symbolique) |
| **Theories** | Entiers, arrays (via lambdas) | BitVec, Array, String, Real, quantificateurs |
| **Optimisation** | Limitee | `Optimize` complet (maximize/minimize) |
| **Tactiques** | Non exposees | `Tactic`, `Then`, `Repeat` |
| **Courbe** | Syntaxe C# familiere | API Python explicite, plus de controle |

### Declaratif vs Imperatif

| Aspect | Imperatif (classique) | Declaratif (Z3) |
|--------|----------------------|---------------------|
| **Approche** | Ecrire l'algorithme de resolution | Decrire les contraintes, laisser le solveur resoudre |
| **Complexite** | Backtracking, heuristiques, pruning | Syntaxe Python naturelle |
| **Evolution** | Modifier l'algorithme pour chaque nouveau probleme | Ajouter des contraintes, le solveur s'adapte |
| **Verification** | Tester les solutions | Les solutions satisfont les contraintes par construction |
| **Limite** | Difficile a generaliser | Performance sur les tres grandes instances |

## Vue d'ensemble

| # | Notebook | Sujet | Duree | Statut |
|---|----------|-------|------|--------|
| 01 | [Introduction](Z3-Python-01-Introduction.ipynb) | `Solver`, `Int`/`Bool`/`Real`, sat/unsat, `Optimize` | ~30 min | PRODUCTION |
| 02 | [Sudoku](Z3-Python-02-Sudoku.ipynb) | Sudoku comme CSP, `Distinct`, visualisation matplotlib | ~25 min | PRODUCTION |
| 03 | *(a venir)* Tactiques et theories | `Tactic`, `BitVec`, `Array` | — | Planifie |
| 04 | *(a venir)* Chaines et expressions regulieres | `String`, `Re` (theorie des chaines Z3) | — | Planifie |
| 05 | *(a venir)* Quantificateurs et preuves | `ForAll`, `Exists`, proofs, modele checking | — | Planifie |
| 06 | *(a venir)* Optimisation avancee | Pareto, objectifs multiples, `Optimize` hierarchique | — | Planifie |

### Fil pedagogique

1. **Notebook 01** pose les bases : le patron `Solver()`, les types de base (`Int`, `Bool`, `Real`), les reponses `sat`/`unsat`/`unknown`, et l'optimisation avec `Optimize`
2. **Notebook 02** applique l'approche declarative au Sudoku : modelisation par `Distinct`, resolution et visualisation (donne en noir / resolu en bleu)
3. **Notebooks suivants (planifies)** : tactiques, theories de chaines, quantificateurs et optimisation avancee

## Prerequis

| Besoin | Detail |
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

A l'issue de cette serie, l'etudiant sera capable de :

1. **Modeliser** un probleme de satisfaction de contraintes en Python avec z3-py
2. **Utiliser** les types et theories Z3 (`Int`, `Real`, `Bool`, `BitVec`, `Array`, `String`)
3. **Optimiser** une fonction objectif sous contraintes (`Optimize`)
4. **Comparer** l'approche declarative (Z3) aux approches imperatives (backtracking, CP)
5. **Appliquer** la resolution SMT a des problemes concrets (Sudoku, ordonnancement, allocation)

## Contexte technique

**z3-py** combine deux technologies :

- **Z3** : solveur SMT (*Satisfiability Modulo Theories*) capable de resoudre des contraintes sur des entiers, reels, booleens, vecteurs de bits, tableaux et chaines
- **Python** : le binding `z3-solver` expose l'API C++ de Z3 via des wrappers Python, avec surcharge des operateurs (`==`, `+`, `*`) pour construire des formules symboliques de facon naturelle

### Liens

- [Z3 Guide (officiel)](https://microsoft.github.io/z3guide/) — documentation et tutoriels
- [Z3 Python API](https://z3prover.github.io/api/html/namespacez3py.html) — reference de l'API z3-py
- [PyPI : z3-solver](https://pypi.org/project/z3-solver/) — package pip
- [Serie Z3 C# (Z3.Linq)](../Z3/README.md) — serie sœur en .NET 9
- [Serie Sudoku](../../Sudoku/README.md) — compare Z3 a 10 autres approches algorithmiques
