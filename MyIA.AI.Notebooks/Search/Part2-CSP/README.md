# Partie 2 : Programmation par Contraintes

[← Partie 1 : Search](../Part1-Foundations/README.md) | [↑ Serie Search](../README.md) | [Applications →](../Applications/README.md)

Au lieu de concevoir un algorithme d'exploration, que se passe-t-il si l'on declare les contraintes du probleme et que l'on laisse le solveur trouver les solutions ? La programmation par contraintes (CSP) represente ce changement de paradigme : on ne cherche plus, on contraint. Ce modele declaratif est au coeur des outils industriels (ordonnancement, logistique, verification) et s'applique naturellement aux problemes NP-difficiles.

Les deux premiers notebooks installent le socle. CSP-1 pose le modèle (X, D, C) — variables, domaines, contraintes — et montre que le backtracking de la Partie 1, enrichi de deux heuristiques de bon sens (choisir d'abord la variable la plus contrainte, essayer d'abord la valeur la moins contraignante), résout déjà des problèmes non triviaux. CSP-2 introduit l'idée qui fait la puissance du paradigme : la propagation. Plutôt que de découvrir une impasse en s'y enfonçant, AC-3 et MAC élaguent les valeurs impossibles avant même de les essayer — l'espace de recherche se réduit de lui-même, par simple déduction locale.

La montée en puissance occupe les quatre notebooks suivants. CSP-3 passe aux contraintes globales (AllDifferent, Cumulative, Circuit), ces contraintes de haut niveau pour lesquelles les solveurs embarquent des propagateurs spécialisés — c'est là que CP-SAT se met à résoudre en quelques millisecondes ce qu'un backtracking naïf mettrait des heures à parcourir. CSP-4 et CSP-5 appliquent l'arsenal aux deux grands classiques industriels : l'ordonnancement (Job-Shop, RCPSP, planification d'infirmiers) et l'optimisation combinatoire (Bin Packing, Knapsack, portefeuille). CSP-6, le notebook le plus avancé, ouvre le capot : la Lazy Clause Generation explique pourquoi CP-SAT s'appelle ainsi — un solveur CP qui apprend des clauses SAT en cours de route — et les hybridations CP+ML et LLM+CSP esquissent ce que devient la discipline à l'ère des grands modèles : le langage naturel comme interface de modélisation, le solveur comme garant.

Les trois derniers notebooks desserrent chacun une hypothèse du cadre classique : et si toutes les contraintes n'avaient pas le même poids (CSP-7, contraintes souples) ? Et si les variables étaient des intervalles de temps (CSP-8, algèbre d'Allen) ? Et si personne ne détenait le problème en entier (CSP-9, résolution distribuée et préservation de la vie privée) ?

## Pourquoi cette partie

Si la Partie 1 enseigne à chercher, celle-ci enseigne à modéliser — et c'est un art plus subtil qu'il n'y paraît. Le même problème, déclaré avec des contraintes binaires ou avec une contrainte globale équivalente, peut passer de plusieurs heures de calcul à quelques millisecondes : le solveur n'a pas changé, seule la formulation a changé. Cette sensibilité à la modélisation est la compétence centrale du praticien, et la raison pour laquelle ces techniques équipent les outils d'ordonnancement, de logistique et de vérification utilisés en production. C'est aussi le premier contact de la série avec le raisonnement déclaratif — celui qu'approfondissent Z3 et la planification PDDL côté SymbolicAI.

## Objectifs d'apprentissage

A l'issue de cette partie, vous serez capable de :

1. **Modeliser** un probleme NP-difficile comme un CSP (variables, domaines, contraintes) et le resoudre avec OR-Tools CP-SAT
2. **Maitriser** les techniques de propagation (AC-3, Forward Checking, MAC) pour reduire l'espace de recherche
3. **Exploiter** les contraintes globales (AllDifferent, Cumulative, Circuit) pour les problemes industriels
4. **Composer** CSP avec SAT, ML et LLM pour des solutions hybrides (LCG, CP+ML, LLM+CSP)
5. **Etendre** le cadre classique aux contraintes souples, temporelles et distribuees

## Notebooks

| # | Notebook | Kernel | Contenu | Duree |
|---|----------|--------|---------|-------|
| 1 | [CSP-1-Fundamentals](CSP-1-Fundamentals.ipynb) | Python 3 | Modele CSP (X, D, C), backtracking, heuristiques MRV et LCV | ~50 min |
| 2 | [CSP-2-Consistency](CSP-2-Consistency.ipynb) | Python 3 | AC-3, Forward Checking, MAC : propagation de contraintes | ~45 min |
| 3 | [CSP-3-Advanced](CSP-3-Advanced.ipynb) | Python 3 | Contraintes globales OR-Tools : AllDifferent, Cumulative, Circuit, LNS | ~50 min |
| 4 | [CSP-4-Scheduling](CSP-4-Scheduling.ipynb) | Python 3 | Job-Shop (JSSP), RCPSP, Nurse Scheduling, IntervalVar, NoOverlap | ~1h |
| 5 | [CSP-5-Optimization](CSP-5-Optimization.ipynb) | Python 3 | Bin Packing, Knapsack, Cutting Stock, Portfolio Optimization | ~1h |
| 6 | [CSP-6-Hybridization](CSP-6-Hybridization.ipynb) | Python 3 | Lazy Clause Generation (LCG), CP+SAT, CP+ML, LLM+CSP | ~1h30 |
| 7 | [CSP-7-Soft](CSP-7-Soft.ipynb) | Python 3 | Contraintes souples : Fuzzy CSP, Weighted CSP, Semiring-based CSP | ~1h |
| 8 | [CSP-8-Temporal](CSP-8-Temporal.ipynb) | Python 3 | Algebre d'intervalles d'Allen, Simple Temporal Problems (STP), TCSP | ~1h |
| 9 | [CSP-9-Distributed](CSP-9-Distributed.ipynb) | Python 3 | Asynchronous Backtracking (ABT), AWC, Privacy-preserving CSP | ~1h30 |

## Progression

CSP-1 et CSP-2 sont incontournables : tout le paradigme — un modèle déclaratif, une propagation qui élague — tient dans ces deux notebooks. Au-delà, trois chemins s'offrent selon votre objectif :

- **Applications industrielles** : CSP-3 puis CSP-4 (Scheduling) et/ou CSP-5 (Optimization)
- **Frontieres** : CSP-6 (Hybridization, le notebook le plus avance), puis CSP-7/8/9 (Soft/Temporal/Distributed)
- **Independants** : CSP-7, CSP-8 et CSP-9 sont accessibles apres CSP-1 + CSP-2

Les notebooks CSP presupposent les bases de la Partie 1 : formalisation en espace d'etats ([Search-1](../Part1-Foundations/Search-1-StateSpace.ipynb)) et backtracking ([Search-2](../Part1-Foundations/Search-2-Uninformed.ipynb)).

## Prerequis & environnement

| Besoin | Detail |
|--------|--------|
| Python | 3.10+, environnement virtuel recommande |
| `ortools` | Dependence principale de toute la serie (CP-SAT) |
| Cle API (optionnel) | CSP-6, section LLM+CSP uniquement ; le reste du notebook fonctionne sans |

Pour le setup complet, voir le [README de la serie Search](../README.md).

## FAQ

| Probleme | Solution |
|----------|----------|
| Solveur CP-SAT trop lent sur les grandes instances | Preferer les contraintes globales (AllDifferent, Cumulative) aux contraintes binaires equivalentes ; utiliser LNS (CSP-3) |
| Comment choisir entre CP-SAT et un solveur SAT ? | CP-SAT pour les contraintes globales et l'optimisation (objectif), SAT pour la decision pure ; CSP-6 detaille les compromis |
| CSP-9 : les algorithmes distribues ne convergent pas | Verifier que le reseau de contraintes est un arbre, ou utiliser AWC (Weak-Commitment) au lieu d'ABT |
| Ou sont les applications concretes ? | Voir [Applications](../Applications/README.md) : 21 notebooks (N-Queens, Nurse Scheduling, VRP, TSP...) |

## Ponts vers SymbolicAI

Les notebooks CSP nécessitent une compréhension préalable de :
- **[Search-1 (StateSpace)](../Part1-Foundations/Search-1-StateSpace.ipynb)** : formalisation des problèmes
- **[Search-2 (Uninformed)](../Part1-Foundations/Search-2-Uninformed.ipynb)** : backtracking = DFS avec retour arrière

## Progression recommandée

```text
CSP-1 (Fundamentals) ──> CSP-2 (Consistency) ──> CSP-3 (Advanced)
                                                    │
                                    ┌───────────────┼───────────────┐
                                    │               │               │
                              CSP-4           CSP-5           CSP-6
                            (Scheduling)   (Optimization)  (Hybridization)
                                    │               │
                                    └───────────────┘
                                            │
                              ┌─────────────┼─────────────┐
                              │             │             │
                         CSP-7         CSP-8         CSP-9
                         (Soft)      (Temporal)   (Distributed)
```

## Transition vers SymbolicAI

| CSP Concept | SymbolicAI Counterpart |
|-------------|------------------------|
| OR-Tools CP-SAT | Z3/01_Linq2Z3_Intro (SMT solving) |
| Scheduling/Planning | Planners (PDDL, HTN) |
| Constraint logic | Tweety (Formal Logic) |
| Temporal CSP | Temporal Planning, STP |

## Ponts inter-series

| Serie | Lien | Relation |
| ------- | ------ | ---------- |
| [Partie 1 : Search](../Part1-Foundations/README.md) | Fondamentaux | Prerequis : backtracking, heuristiques |
| [Applications](../Applications/README.md) | 21 notebooks d'application | Mise en pratique des CSP |
| [Search (parent)](../README.md) | Vue d'ensemble | Contexte et parcours global |
| [Sudoku](../../Sudoku/) | Resolution par contraintes | Application directe des CSP |
| [SymbolicAI/Z3](../../SymbolicAI/) | Solveur SMT | CSP-6 (LCG) et automates symboliques |
| [Probas/Infer](../../Probas/Infer/) | Infer.NET | Modeles graphiques et contraintes |

## Navigation

[<- Partie 1 : Search Fondamental](../Part1-Foundations/README.md) | [Retour a la serie Search](../README.md) | [Applications ->](../Applications/README.md)
