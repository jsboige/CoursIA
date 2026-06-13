# SMT - Satisfiability Modulo Theories

**Navigation** : [Index SymbolicAI](../README.md) | [Index general](../../README.md)

## En quelques mots

Ce repertoire regroupe les series consacrees aux **solveurs SMT** (*Satisfiability Modulo Theories*) et, en pratique, au solveur de reference **Z3** (Microsoft Research). On y aborde le meme changement de paradigme — passer de l'imperatif (ecrire l'algorithme de resolution) au declaratif (decrire les contraintes, laisser le solveur resoudre) — sous deux angles complementaires : une approche **C# declarative bornee** (Z3.Linq) et une approche **Python imperative complete** (z3-py).

## Qu'est-ce que SMT ?

Un solveur **SAT** decide si une formule booleenne est satisfiable. Un solveur **SMT** etend SAT en raisonnant directement sur des *theories* : arithmetique lineaire sur les entiers et les reels, tableaux (`Array`), vecteurs de bits (`BitVec`), chaines de caracteres, fonctions non interpretees. Plutot que d'encoder un Sudoku ou un planificateur de repas en variables booleennes a la main, on exprime les contraintes dans le langage naturel de la theorie concernee, et le solveur retourne un modele (`sat`) ou prouve l'impossibilite (`unsat`).

**Z3** est le solveur SMT le plus utilise en recherche comme en industrie (verification de programmes, planification, synthese, securite). Les deux series ci-dessous l'exploitent via deux bindings differents.

## Les deux series

| Serie | Langage / Binding | Style | Notebooks | Statut |
|-------|-------------------|-------|-----------|--------|
| [**Z3/**](Z3/README.md) | C# .NET 9 / **Z3.Linq** | Declaratif borne : on traduit des expressions LINQ en formules SMT | 5 (`01` -> `05`) | PRODUCTION / BETA |
| [**Z3-Python/**](Z3-Python/README.md) | Python / **z3-py** | Imperatif complet : acces a l'API integrale du solveur | 3 (`01` -> `03`, en cours) | PRODUCTION |

### Z3.Linq (C#) — la porte d'entree declarative

`Z3.Linq` traduit des expressions LINQ C# en formules SMT. On ecrit une requete proche de la syntaxe metier (`from ... where ... select ...`) et la couche cache les appels Z3 bas niveau. L'avantage pedagogique est la lisibilite : un theoreme s'enonce presque comme une specification. La contrepartie est une **couverture bornee** de l'API (pas de tactiques, pas de theories exotiques) et une montee en charge limitee sur les tres grandes instances.

### z3-py (Python) — l'API complete

`z3-py` n'impose aucune couche declarative restrictive : tactiques (`simplify`, `Then`, `OrElse`), theories `BitVec` et `Array`, `Optimize`, quantificateurs, `SolverFor(...)` specialises. C'est l'outil de reference pour aller au-dela de la modelisation introductive et explorer les ressorts internes du solveur.

## Quelle serie choisir ?

- **Decouvrir le paradigme declaratif en C# / .NET** : commencer par [Z3/](Z3/README.md). Ideal si vous venez de l'ecosysteme .NET (Sudoku, Search/CSP du depot).
- **Exploiter toute la puissance de Z3 en Python** : aller vers [Z3-Python/](Z3-Python/README.md). Ideal pour la recherche, le prototypage rapide et les theories avancees (BitVec, Array, tactiques).

Les deux series traitent volontairement des **memes problemes phares** (theoremes lineaires, Sudoku comme CSP) afin de rendre la comparaison declaratif/imperatif explicite d'un binding a l'autre.

## Voir aussi

- [Serie Sudoku](../../Sudoku/README.md) — compare Z3 a une dizaine d'autres approches algorithmiques
- [Search / CSP](../../Search/README.md) — programmation par contraintes et automates symboliques (predicats Z3)
- [Z3 Prover (upstream)](https://github.com/Z3Prover/z3) — le solveur SMT lui-meme
- [Z3.Linq (endjin)](https://github.com/endjin/Z3.Linq) — le binding C# declaratif
