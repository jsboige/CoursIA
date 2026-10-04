# Partie 1 — Fondations de la Planification

[← Setup (00-Environment)](../00-Environment/Planners-0-Setup.ipynb) | [↑ Planification](../README.md) | [Partie 2 — Classique →](../02-Classical/README.md)

Cette première partie pose le **vocabulaire formel** de la planification automatique. Avant de résoudre un problème, il faut savoir le *décrire* : qu'est-ce qu'un état, une action, un but ? Comment représenter un monde assez précisément pour qu'une machine puisse y chercher une suite d'actions ? Les trois notebooks de cette partie construisent progressivement ce cadre conceptuel, du triptyque État-Action-But jusqu'à la constatation qui motive toute la suite de la série : la recherche aveugle dans l'espace d'états explose combinatoirement.

## Position dans la série

| Étape | Question |
|-------|----------|
| ← `00-Environment` | L'environnement Python/Docker est-il prêt ? |
| **Partie 1 — Fondations** | **Comment *modéliser* un problème de planification ?** |
| `02-Classical` → | Comment *résoudre* ce problème avec un planificateur industriel ? |

Le fil conducteur de cette partie est le passage du problème *informel* (« je veux empiler ces blocs ») au modèle *formel* (un domaine PDDL, un état initial, un but). C'est cette traduction qui rend le problème soluble par un algorithme — et qui révèle, au notebook 3, pourquoi un algorithme naïf ne suffit pas.

## Notebooks

| # | Notebook | Durée | Contenu |
|---|----------|-------|---------|
| 1 | [Planners-1-Introduction](Planners-1-Introduction.ipynb) | 30 min | Triptyque État-Action-But, hypothèses STRIPS (1971), taxonomie des paradigmes de planification |
| 1 (C#) | [Planners-1-Introduction-Csharp](Planners-1-Introduction-Csharp.ipynb) | 30 min | Jumeau C# du 1 : la planification automatique from-scratch en .NET 9, triptyque État-Action-But réimplémenté sans lib de planification (See #4956) |
| 2 | [Planners-2-PDDL-Basics](Planners-2-PDDL-Basics.ipynb) | 40 min | Syntaxe PDDL : domaines, problèmes, types, prédicats, actions, préconditions, effets |
| 2 (C#) | [Planners-2-PDDL-Basics-Csharp](Planners-2-PDDL-Basics-Csharp.ipynb) | 40 min | Jumeau C# du 2 : planificateur STRIPS from-scratch (modèle typé, grounding, BFS forward), domaines Logistics + Gripper (See #4956) |
| 3 | [Planners-3-State-Space](Planners-3-State-Space.ipynb) | 35 min | Recherche dans l'espace d'états, explosion combinatoire $O(2^n)$, nécessité des heuristiques |
| 3 (C#) | [Planners-3-State-Space-Csharp](Planners-3-State-Space-Csharp.ipynb) | 35 min | Jumeau C# du 3 : BFS/DFS/Greedy/A* from-scratch sur terrain pondéré (See #4956) |

## Prérequis

- **Python 3.9+** : programmation orientée objet, types, dataclasses
- **.NET 9 (jumeaux C# uniquement)** : les notebooks `-Csharp` s'exécutent sous .NET Interactive, sans prérequis Python
- **Algorithmique de base** : graphes (BFS, DFS), parcours
- **Logique propositionnelle** : prédicats, connecteurs

Aucun prérequis en planification : les concepts sont introduits depuis zéro. Le notebook `0-Setup` (partie précédente) doit avoir été exécuté une fois pour installer `unified-planning` et vérifier l'environnement.

## À l'issue de cette partie

Vous saurez :

1. **Définir** ce qu'est la planification automatique et la distinguer de l'apprentissage supervisé
2. **Modéliser** un problème en PDDL — domaine, problème, actions avec préconditions et effets
3. **Représenter** l'espace d'états d'un problème et mesurer son explosion combinatoire
4. **Justifier** pourquoi la recherche aveugle ne suffit pas — et donc pourquoi les heuristiques (partie 2) sont indispensables

## Pour continuer

- **Résoudre les problèmes modélisés ici** → [Partie 2 — Planification Classique](../02-Classical/README.md) : Fast Downward, heuristiques A* / h-FF / LM-cut, domaines IPC
- **Revoir la vue d'ensemble** → [Planification (README parent)](../README.md)

La transition vers la partie 2 est naturelle : le notebook 3 conclut que la recherche dans l'espace d'états est nécessaire mais coûteuse ; la partie 2 montre comment un planificateur industriel (Fast Downward) et de bonnes heuristiques (LM-cut) la rendent praticable.
