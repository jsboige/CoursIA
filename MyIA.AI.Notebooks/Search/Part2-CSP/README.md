# Partie 2 : Programmation par Contraintes

> **Pivot vers SymbolicAI** : Z3, Planning, Logic. Cette partie fait le pont entre les algorithmes de recherche et l'IA symbolique.

La programmation par contraintes (CSP) represente un **changement de paradigme** : au lieu de concevoir un algorithme d'exploration, on declare les contraintes du probleme et le solveur trouve les solutions. Ce modele declaratif est au coeur des outils industriels (ordonnancement, logistique, verification) et s'applique naturellement aux problemes NP-difficiles.

Le parcours va des fondamentaux du modele (X, D, C) et du backtracking (CSP-1) a la propagation de contraintes (AC-3, MAC en CSP-2), puis aux extensions avancees : contraintes globales (CSP-3), ordonnancement industriel (CSP-4), optimisation combinatoire (CSP-5), hybridation avec SAT/ML/LLM (CSP-6). Les trois derniers notebooks explorent les frontiers : contraintes souples, temporelles et distribuees.

**9 notebooks** | **~9h** | Python 3.10+ (`ortools`)

## Notebooks

| # | Notebook | Duree | Contenu | Prerequis |
|---|----------|-------|---------|-----------|
| 1 | [CSP-1-Fundamentals](CSP-1-Fundamentals.ipynb) | ~50 min | Variables, domaines, contraintes, backtracking, MRV, LCV | Search-1, Search-2 |
| 2 | [CSP-2-Consistency](CSP-2-Consistency.ipynb) | ~45 min | AC-3, Forward checking, MAC, propagation de contraintes | CSP-1 |
| 3 | [CSP-3-Advanced](CSP-3-Advanced.ipynb) | ~50 min | AllDifferent, cumulative, circuit, symetries, LNS | CSP-2 |
| 4 | [CSP-4-Scheduling](CSP-4-Scheduling.ipynb) | ~1h | Job-Shop (JSSP), RCPSP, Nurse Scheduling, IntervalVar, NoOverlap, Cumulative | CSP-3 |
| 5 | [CSP-5-Optimization](CSP-5-Optimization.ipynb) | ~1h | Bin Packing, Knapsack, Cutting Stock, Portfolio Optimization, cardinalite | CSP-3, Search-11 |
| 6 | [CSP-6-Hybridization](CSP-6-Hybridization.ipynb) | ~1h30 | Lazy Clause Generation (LCG), CP+SAT, CP+ML, LLM+CSP, parallelisation | CSP-4, CSP-5 |
| 7 | [CSP-7-Soft](CSP-7-Soft.ipynb) | ~1h | Contraintes souples, Fuzzy CSP, Weighted CSP, Semiring-based CSP | CSP-1, CSP-2 |
| 8 | [CSP-8-Temporal](CSP-8-Temporal.ipynb) | ~1h | Allen's Interval Algebra, STP, TCSP, raisonnement temporel | CSP-1, CSP-2 |
| 9 | [CSP-9-Distributed](CSP-9-Distributed.ipynb) | ~1h30 | Asynchronous Backtracking (ABT), AWC, Privacy-preserving CSP | CSP-1, CSP-2, CSP-6 |

## Prerequis

Les notebooks CSP necessitent une comprehension prealable de :
- **[Search-1 (StateSpace)](../Part1-Foundations/Search-1-StateSpace.ipynb)** : formalisation des problemes
- **[Search-2 (Uninformed)](../Part1-Foundations/Search-2-Uninformed.ipynb)** : backtracking = DFS avec retour arriere

## Progression recommandee

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
| OR-Tools CP-SAT | Linq2Z3 (SMT solving) |
| Scheduling/Planning | Planners (PDDL, HTN) |
| Constraint logic | Tweety (Formal Logic) |
| Temporal CSP | Temporal Planning, STP |

## Retour

[<- Retour a la serie Search](../README.md)
