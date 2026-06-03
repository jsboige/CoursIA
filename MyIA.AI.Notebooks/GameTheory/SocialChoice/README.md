# Social Choice - Theorie du Choix Social

<!-- CATALOG-STATUS
series: SocialChoice
pedagogical_count: 4
maturity: PRODUCTION=4
-->

La theorie du choix social etudie comment aggreger des preferences individuelles en une decision collective. Ses resultats les plus celebres sont des **theoremes d'impossibilite** : le theoreme d'Arrow (1951) montre qu'aucune regle de vote ne peut satisfaire simultanement des axiomes "raisonnables" (Pareto, IIA, non-dictature) des que 3 alternatives ou plus sont en jeu ; le theoreme de Sen (1970) demontre un conflit fondamental entre liberte individuelle et efficacite collective.

Cette sous-serie du parcours [GameTheory](../README.md) explore ces resultats sous quatre angles complementaires : la simulation Python des axiomes, la formalisation en Lean 4 (preuve formelle), les methodes de vote concrete, et l'encodage SAT/Z3 pour la verification mecanique.

**A qui s'adresse cette serie** : etudiants en economie, informatique, sciences politiques et mathematiques appliquees. Les notebooks 01 et 03 ne necessitent que Python (numpy, matplotlib). Les notebooks 02 (Lean) et 04 (SAT/Z3) requierent des installations supplementaires decrites dans le [README parent](../README.md). Aucun prerequis en theorie du choix social : les concepts sont introduits progressivement.

## Notebooks

| # | Notebook | Titre | Duree | Status |
|---|----------|-------|-------|--------|
| SC-01 | [01-Arrow-Impossibility-Theorem](01-Arrow-Impossibility-Theorem.ipynb) | Theoreme d'Arrow : Preuve Formelle et Simulation | 45 min | COMPLET |
| SC-02 | [02-Lean-SocialChoice-Formal](02-Lean-SocialChoice-Formal.ipynb) | Choix Social Formel en Lean 4 (Arrow, Sen, Electeur Median, Tour Peters) | 80 min | COMPLET |
| SC-03 | [03-Voting-Methods](03-Voting-Methods.ipynb) | Methodes de Vote et Paradoxes (Condorcet, Borda, Copeland, Downs) | 35 min | COMPLET |
| SC-04 | [04-Computational-Aggregation-SAT-Z3](04-Computational-Aggregation-SAT-Z3.ipynb) | Agregation Computationnelle : SAT et Z3 | 45 min | COMPLET |

**Duree totale** : ~3h25

## Parcours d'apprentissage

### Etape 1 : Le theoreme d'Arrow par la simulation (SC-01, 45 min)

Le notebook SC-01 introduit les trois axiomes d'Arrow (Pareto faible, IIA, non-dictature) en les testant empiriquement sur des regles de vote usuelles (Borda, pluralite, dictature). Il suit la structure de la preuve de Geanakoplos (2005) -- lemme extremal, existence du pivot, dictateur partiel -- et l'illustre pas a pas en Python. La conclusion montre pourquoi la preuve formelle couvre une infinite de cas que la simulation ne peut atteindre.

### Etape 2 : Methodes de vote et paradoxes (SC-03, 35 min)

Le notebook SC-03 implemente les regles de vote classiques (pluralite, Borda, Copeland), illustre le paradoxe de Condorcet et l'exemple de Lady Chatterley (theoreme de Sen), puis montre la convergence vers l'electeur median dans le modele de Downs (1957). Ce notebook est le compagnon Python du formalisme Lean du SC-02.

### Etape 3 : Preuve formelle en Lean 4 (SC-02, 80 min)

Le notebook SC-02 formalise les preferences, les axiomes d'Arrow et de Sen, et le theoreme de l'electeur median en Lean 4. Il inclut un tour de la librairie SocialChoiceLean de DominikPeters (Gibbard-Satterthwaite, Split Cycle, 12 regles de vote, theoreme de Duggan-Schwartz). Les definitions sont compatibles avec le projet Lake `social_choice_lean/` (0 sorry sur Arrow, Sen et Voting).

### Etape 4 : Verification mecanique par SAT et Z3 (SC-04, 45 min)

Le notebook SC-04 encode les theoremes d'Arrow et de Sen comme des problemes SAT (PySAT) et SMT (Z3). Le resultat UNSAT des solveurs constitue une preuve mecanique de l'impossibilite. Il compare les approches SAT (variables booleennes, clauses CNF) et SMT (variables entieres, rangs sociaux), et analyse la relaxation des axiomes (chaque paire d'axiomes est realisable).

## Formalisations Lean

Les notebooks SC-01 et SC-02 renvoient au projet Lake `social_choice_lean/` qui contient les preuves completes :

| Resultat | Fichier | sorry | Statut |
|----------|---------|-------|--------|
| Theoreme d'Arrow | `Arrow.lean` | 0 | Prouve (~950 lignes) |
| Theoreme de Sen | `Sen.lean` | 0 | Prouve (~300 lignes) |
| Modeles de vote | `Voting.lean` | 0 | Banks, STV, Median Voter |

Le projet `social_choice_lean_peters/` (DominikPeters, Lean 4 + Mathlib) formalise 12 regles de vote et 4 theoremes d'impossibilite supplementaires (Gibbard-Satterthwaite, Condorcet Participation, Condorcet Reinforcement, Duggan-Schwartz). Inventaire detaille : [LEAN_INVENTORY.md](../LEAN_INVENTORY.md).

## Concepts cles

| Concept | Description |
|---------|-------------|
| **Theoreme d'Arrow** | Aucune SWF avec 3+ alternatives ne peut satisfaire Pareto + IIA + non-dictature |
| **Theoreme de Sen** | Liberte minimale + Pareto + transitivite sont incompatibles |
| **Paradoxe de Condorcet** | Les preferences majoritaires peuvent etre cycliques (A > B > C > A) |
| **Electeur median** | Avec des preferences unimodales, le vainqueur de Condorcet existe |
| **IIA** | Le classement social entre x et y ne depend que des preferences individuelles sur {x, y} |
| **Gibbard-Satterthwaite** | Toute regle de vote non-dictatoriale est manipulable (pour 3+ candidats) |
| **Split Cycle** | Regle de vote la plus fine satisfaisant Condorcet + acyclicite |

## Navigation

- **Serie parente** : [GameTheory](../README.md) (theorie des jeux, Nash, Shapley, design de mecanismes)
- **Notebook 16 (Mechanism Design)** : introduction au choix social dans le fil principal GameTheory
- **SymbolicAI/Lean** : [README Lean](../../SymbolicAI/Lean/README.md) pour les prerequis Lean 4

---

## Prerequisites

- Python 3.10+ avec numpy, matplotlib, networkx (notebooks 01, 03, 04)
- pysat et z3-solver pour le notebook 04
- Lean 4 + kernel WSL pour le notebook 02 (cf [README parent](../README.md))

## Installation

```bash
pip install -r ../requirements.txt
pip install pysat z3-solver
```

Pour le notebook 02 (Lean 4) : suivre les instructions dans [README parent](../README.md#notebooks-lean-4-2b-4b-8b-15b-16b).

## Ressources

| Reference | Couverture |
|-----------|------------|
| Arrow, *Social Choice and Individual Values* (1951) | Theoreme d'impossibilite |
| Sen, *Collective Choice and Social Welfare* (1970) | Paradoxe liberal |
| Geanakoplos, "Three Brief Proofs of Arrow's Impossibility Theorem" (2005) | Preuve utilisee dans SC-01 et SC-02 |
| Moulin, "Condorcet's Principle Implies the No Show Paradox" (1988) | Paradoxe de la non-participation |
| Holliday & Pacuit, "Split Cycle" (2023) | Regle de vote optimale |
| Peters, [SocialChoiceLean](https://github.com/DominikPeters/SocialChoiceLean) | Formalisation Lean 4 de 12 regles + 4 theoremes |

## Licence

Voir la licence du repository principal.
