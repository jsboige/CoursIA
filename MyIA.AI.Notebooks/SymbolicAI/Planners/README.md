# Planners - Planification Automatique

Introduction a la planification automatique avec Fast Downward, un planificateur PDDL (Planning Domain Definition Language) de reference.

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 1 |
| Kernel | Python 3 |
| Duree estimee | ~45-60 min |

## Notebook

| Notebook | Contenu | Duree |
|----------|---------|-------|
| [Fast-Downward](Fast-Downward.ipynb) | Introduction PDDL, planification, heuristiques | 45-60 min |

## Contenu detaille

### Fast-Downward.ipynb

| Section | Contenu |
|---------|---------|
| PDDL | Syntaxe domaine et probleme |
| Planification | Espace d'etats, recherche |
| Heuristiques | h^FF, h^add, landmarks |
| Fast Downward | Installation, utilisation |
| Exemples | Blocks World, Logistics |

## PDDL - Planning Domain Definition Language

PDDL est un langage standard pour decrire des problemes de planification :

### Domaine (domain.pddl)

```lisp
(define (domain blocks)
  (:predicates (on ?x ?y) (clear ?x) (ontable ?x) (holding ?x))
  (:action pick-up
    :parameters (?x)
    :precondition (and (clear ?x) (ontable ?x))
    :effect (and (holding ?x) (not (ontable ?x)) (not (clear ?x)))))
```

### Probleme (problem.pddl)

```lisp
(define (problem blocks-4)
  (:domain blocks)
  (:objects a b c d)
  (:init (clear a) (clear b) (ontable c) (ontable d) (on a c) (on b d))
  (:goal (and (on a b) (on b c) (on c d))))
```

## Fast Downward

Planificateur optimal developpe a l'Universite de Bale :

| Caracteristique | Description |
|-----------------|-------------|
| **Algorithmes** | A*, GBFS, LAMA |
| **Heuristiques** | FF, add, landmark-cut |
| **Performance** | Gagnant IPC multiple fois |

### Installation

Le notebook auto-compile Fast Downward si necessaire :

```bash
# Prerequis Linux/WSL
sudo apt install cmake g++ python3

# Compilation
cd fast-downward
./build.py
```

### Utilisation

```bash
./fast-downward.py domain.pddl problem.pddl --search "astar(lmcut())"
```

## Concepts cles

| Concept | Description |
|---------|-------------|
| **Etat** | Configuration du monde |
| **Action** | Transition entre etats |
| **Precondition** | Conditions d'applicabilite |
| **Effet** | Changements apres action |
| **Plan** | Sequence d'actions |
| **Heuristique** | Estimation du cout restant |

## Prerequisites

### Environnement

```bash
# Linux/WSL recommande
# Windows : utiliser WSL2

# Dependances
sudo apt install cmake g++ python3
pip install unified-planning
```

## Relation avec SymbolicAI

La planification automatique est une branche de l'IA symbolique :
- Raisonnement sur actions et etats
- Recherche dans espace d'etats
- Heuristiques admissibles pour optimalite

Voir aussi :
- [Tweety](../Tweety/) - Logique et argumentation
- [Lean](../Lean/) - Verification formelle

## Ressources

- [Fast Downward](https://www.fast-downward.org/)
- [PDDL Reference](https://planning.wiki/)
- [IPC - International Planning Competition](https://ipc2023-classical.github.io/)

## Licence

Voir la licence du repository principal.
