# SMT - Satisfiability Modulo Theories

**Navigation** : [Index SymbolicAI](../README.md) | [Index général](../../README.md)

## En quelques mots

Ce répertoire regroupe les séries consacrées aux **solveurs SMT** (*Satisfiability Modulo Theories*) et, en pratique, au solveur de référence **Z3** (Microsoft Research). On y aborde le même changement de paradigme — passer de l'impératif (écrire l'algorithme de résolution) au déclaratif (décrire les contraintes, laisser le solveur résoudre) — sous deux angles complémentaires : une approche **C# déclarative bornée** (Z3.Linq) et une approche **Python impérative complète** (z3-py).

## Qu'est-ce que SMT ?

Un solveur **SAT** décide si une formule booléenne est satisfiable. Un solveur **SMT** étend SAT en raisonnant directement sur des *théories* : arithmétique linéaire sur les entiers et les réels, tableaux (`Array`), vecteurs de bits (`BitVec`), chaînes de caractères, fonctions non interprétées. Plutôt que d'encoder un Sudoku ou un planificateur de repas en variables booléennes à la main, on exprime les contraintes dans le langage naturel de la théorie concernée, et le solveur retourne un modèle (`sat`) ou prouve l'impossibilité (`unsat`).

**Z3** est le solveur SMT le plus utilisé en recherche comme en industrie (vérification de programmes, planification, synthèse, sécurité). Les deux séries ci-dessous l'exploitent via deux bindings différents.

## Les deux séries

| Série | Langage / Binding | Style | Notebooks | Statut |
|-------|-------------------|-------|-----------|--------|
| [**Z3/**](Z3/README.md) | C# .NET 9 / **Z3.Linq** | Déclaratif borné : on traduit des expressions LINQ en formules SMT | 5 (`01` -> `05`) | PRODUCTION / BETA |
| [**Z3-Python/**](Z3-Python/README.md) | Python / **z3-py** | Impératif complet : accès à l'API intégrale du solveur | 6 (`01` -> `06`, série complète) | PRODUCTION |

### Z3.Linq (C#) — la porte d'entrée déclarative

`Z3.Linq` traduit des expressions LINQ C# en formules SMT. On écrit une requête proche de la syntaxe métier (`from ... where ... select ...`) et la couche cache les appels Z3 bas niveau. L'avantage pédagogique est la lisibilité : un théorème s'énonce presque comme une spécification. La contrepartie est une **couverture bornée** de l'API (pas de tactiques, pas de théories exotiques) et une montée en charge limitée sur les très grandes instances.

### z3-py (Python) — l'API complète

`z3-py` n'impose aucune couche déclarative restrictive : tactiques (`simplify`, `Then`, `OrElse`), théories `BitVec` et `Array`, `Optimize`, quantificateurs, `SolverFor(...)` spécialisés. C'est l'outil de référence pour aller au-delà de la modélisation introductive et explorer les ressorts internes du solveur.

## Quelle série choisir ?

- **Découvrir le paradigme déclaratif en C# / .NET** : commencer par [Z3/](Z3/README.md). Idéal si vous venez de l'écosystème .NET (Sudoku, Search/CSP du dépôt).
- **Exploiter toute la puissance de Z3 en Python** : aller vers [Z3-Python/](Z3-Python/README.md). Idéal pour la recherche, le prototypage rapide et les théories avancées (BitVec, Array, tactiques).

Les deux séries traitent volontairement des **mêmes problèmes phares** (théorèmes linéaires, Sudoku comme CSP) afin de rendre la comparaison déclaratif/impératif explicite d'un binding à l'autre.

## Voir aussi

- [Série Sudoku](../../Sudoku/README.md) — compare Z3 à une dizaine d'autres approches algorithmiques
- [Search / CSP](../../Search/README.md) — programmation par contraintes et automates symboliques (prédicats Z3)
- [Z3 Prover (upstream)](https://github.com/Z3Prover/z3) — le solveur SMT lui-même
- [Z3.Linq (endjin)](https://github.com/endjin/Z3.Linq) — le binding C# déclaratif
