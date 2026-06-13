# Social Choice - Théorie du Choix Social

<!-- CATALOG-STATUS
series: GameTheory-SocialChoice
pedagogical_count: 4
breakdown: SocialChoice=4
maturity: PRODUCTION=3, BETA=1
-->

La théorie du choix social étudie comment agréger des préférences individuelles en une décision collective. Ses résultats les plus célèbres sont des **théorèmes d'impossibilité** : le théorème d'Arrow (1951) montre qu'aucune règle de vote ne peut satisfaire simultanément des axiomes "raisonnables" (Pareto, IIA, non-dictature) dès que 3 alternatives ou plus sont en jeu ; le théorème de Sen (1970) démontre un conflit fondamental entre liberté individuelle et efficacité collective.

Cette sous-série du parcours [GameTheory](../README.md) explore ces résultats sous quatre angles complémentaires : la simulation Python des axiomes, la formalisation en Lean 4 (preuve formelle), les méthodes de vote concrète, et l'encodage SAT/Z3 pour la vérification mécanique.

**À qui s'adresse cette série** : étudiants en économie, informatique, sciences politiques et mathématiques appliquées. Les notebooks 01 et 03 ne nécessitent que Python (numpy, matplotlib). Les notebooks 02 (Lean) et 04 (SAT/Z3) requièrent des installations supplémentaires décrites dans le [README parent](../README.md). Aucun prérequis en théorie du choix social : les concepts sont introduits progressivement.

## Notebooks

| # | Notebook | Titre | Durée | Status |
|---|----------|-------|-------|--------|
| SC-01 | [01-Arrow-Impossibility-Theorem](01-Arrow-Impossibility-Theorem.ipynb) | Théorème d'Arrow : Preuve Formelle et Simulation | 45 min | COMPLET |
| SC-02 | [02-Lean-SocialChoice-Formal](02-Lean-SocialChoice-Formal.ipynb) | Choix Social Formel en Lean 4 (Arrow, Sen, Électeur Médian, Tour Peters) | 80 min | COMPLET |
| SC-03 | [03-Voting-Methods](03-Voting-Methods.ipynb) | Méthodes de Vote et Paradoxes (Condorcet, Borda, Copeland, Downs) | 35 min | COMPLET |
| SC-04 | [04-Computational-Aggregation-SAT-Z3](04-Computational-Aggregation-SAT-Z3.ipynb) | Agrégation Computationnelle : SAT et Z3 | 45 min | COMPLET |

**Durée totale** : ~3h25

## Parcours d'apprentissage

### Étape 1 : Le théorème d'Arrow par la simulation (SC-01, 45 min)

Le notebook SC-01 introduit les trois axiomes d'Arrow (Pareto faible, IIA, non-dictature) en les testant empiriquement sur des règles de vote usuelles (Borda, pluralité, dictature). Il suit la structure de la preuve de Geanakoplos (2005) -- lemme extrémal, existence du pivot, dictateur partiel -- et l'illustre pas à pas en Python. La conclusion montre pourquoi la preuve formelle couvre une infinité de cas que la simulation ne peut atteindre.

### Étape 2 : Méthodes de vote et paradoxes (SC-03, 35 min)

Le notebook SC-03 implémente les règles de vote classiques (pluralité, Borda, Copeland), illustre le paradoxe de Condorcet et l'exemple de Lady Chatterley (théorème de Sen), puis montre la convergence vers l'électeur médian dans le modèle de Downs (1957). Ce notebook est le compagnon Python du formalisme Lean du SC-02.

### Étape 3 : Preuve formelle en Lean 4 (SC-02, 80 min)

Le notebook SC-02 formalise les préférences, les axiomes d'Arrow et de Sen, et le théorème de l'électeur médian en Lean 4. Il inclut un tour de la librairie SocialChoiceLean de DominikPeters (Gibbard-Satterthwaite, Split Cycle, 12 règles de vote, théorème de Duggan-Schwartz). Les définitions sont compatibles avec le projet Lake `social_choice_lean/` (0 sorry sur Arrow, Sen et Voting).

### Étape 4 : Vérification mécanique par SAT et Z3 (SC-04, 45 min)

Le notebook SC-04 encode les théorèmes d'Arrow et de Sen comme des problèmes SAT (PySAT) et SMT (Z3). Le résultat UNSAT des solveurs constitue une preuve mécanique de l'impossibilité. Il compare les approches SAT (variables booléennes, clauses CNF) et SMT (variables entières, rangs sociaux), et analyse la relaxation des axiomes (chaque paire d'axiomes est réalisable).

## Formalisations Lean

Les notebooks SC-01 et SC-02 renvoient au projet Lake `social_choice_lean/` qui contient les preuves complètes :

| Résultat | Fichier | sorry | Statut |
|----------|---------|-------|--------|
| Théorème d'Arrow | `Arrow.lean` | 0 | Prouvé (~950 lignes) |
| Théorème de Sen | `Sen.lean` | 0 | Prouvé (~300 lignes) |
| Modèles de vote | `Voting.lean` | 0 | Banks, STV, Median Voter |

Le projet `social_choice_lean_peters/` (DominikPeters, Lean 4 + Mathlib) formalise 12 règles de vote et 4 théorèmes d'impossibilité supplémentaires (Gibbard-Satterthwaite, Condorcet Participation, Condorcet Reinforcement, Duggan-Schwartz). Inventaire détaillé : [LEAN_INVENTORY.md](../LEAN_INVENTORY.md).

## Concepts clés

| Concept | Description |
|---------|-------------|
| **Théorème d'Arrow** | Aucune SWF avec 3+ alternatives ne peut satisfaire Pareto + IIA + non-dictature |
| **Théorème de Sen** | Liberté minimale + Pareto + transitivité sont incompatibles |
| **Paradoxe de Condorcet** | Les préférences majoritaires peuvent être cycliques (A > B > C > A) |
| **Électeur médian** | Avec des préférences unimodales, le vainqueur de Condorcet existe |
| **IIA** | Le classement social entre x et y ne dépend que des préférences individuelles sur {x, y} |
| **Gibbard-Satterthwaite** | Toute règle de vote non-dictatoriale est manipulable (pour 3+ candidats) |
| **Split Cycle** | Règle de vote la plus fine satisfaisant Condorcet + acyclicité |

## Navigation

- **Série parente** : [GameTheory](../README.md) (théorie des jeux, Nash, Shapley, design de mécanismes)
- **Notebook 16 (Mechanism Design)** : introduction au choix social dans le fil principal GameTheory
- **SymbolicAI/Lean** : [README Lean](../../SymbolicAI/Lean/README.md) pour les prérequis Lean 4

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

| Référence | Couverture |
|-----------|------------|
| Arrow, *Social Choice and Individual Values* (1951) | Théorème d'impossibilité |
| Sen, *Collective Choice and Social Welfare* (1970) | Paradoxe liberal |
| Geanakoplos, "Three Brief Proofs of Arrow's Impossibility Theorem" (2005) | Preuve utilisée dans SC-01 et SC-02 |
| Moulin, "Condorcet's Principle Implies the No Show Paradox" (1988) | Paradoxe de la non-participation |
| Holliday & Pacuit, "Split Cycle" (2023) | Règle de vote optimale |
| Peters, [SocialChoiceLean](https://github.com/DominikPeters/SocialChoiceLean) | Formalisation Lean 4 de 12 règles + 4 théorèmes |

## Licence

Voir la licence du repository principal.
