# Partie 2 : Programmation par Contraintes

> **Pivot vers SymbolicAI** : Z3, Planning, Logic. Cette partie fait le pont entre les algorithmes de recherche et l'IA symbolique.

La programmation par contraintes (CSP) represente un **changement de paradigme** : au lieu de concevoir un algorithme d'exploration, on declare les contraintes du probleme et le solveur trouve les solutions. Ce modele declaratif est au coeur des outils industriels (ordonnancement, logistique, verification) et s'applique naturellement aux problemes NP-difficiles.

Le parcours va des fondamentaux du modele (X, D, C) et du backtracking (CSP-1) a la propagation de contraintes (AC-3, MAC en CSP-2), puis aux extensions avancees : contraintes globales (CSP-3), ordonnancement industriel (CSP-4), optimisation combinatoire (CSP-5), hybridation avec SAT/ML/LLM (CSP-6). Les trois derniers notebooks explorent les frontiers : contraintes souples, temporelles et distribuees.

**9 notebooks** | **~9h** | Python 3.10+ (`ortools`)

## Pourquoi cette sous-serie

La programmation par contraintes represente un **changement de paradigme** fondamental : au lieu de concevoir un algorithme d'exploration, on declare les contraintes du probleme et le solveur trouve les solutions. Ce modele declaratif est au coeur des outils industriels (ordonnancement, logistique, verification) et s'applique naturellement aux problemes NP-difficiles. Cette sous-serie fait le pont entre les algorithmes de recherche (Partie 1) et l'IA symbolique (SymbolicAI), avec des notebooks couvrant les applications industrielles et les frontieres de la recherche.

## Objectifs d'apprentissage

A l'issue de cette partie, vous serez capable de :

1. **Modeliser** un problemeNP-difficile comme un CSP (variables, domaines, contraintes) et le resoudre avec OR-Tools CP-SAT
2. **Maitriser** les techniques de propagation (AC-3, Forward Checking, MAC) pour reduire l'espace de recherche
3. **Exploiter** les contraintes globales (AllDifferent, Cumulative, Circuit) pour les problemes industriels
4. **Composer** CSP avec SAT, ML et LLM pour des solutions hybrides (LCG, CP+ML, LLM+CSP)
5. **Etendre** le cadre classique aux contraintes souples, temporelles et distribuees

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

### Ce que chaque notebook apporte

**CSP-1 (Fundamentals)** pose le cadre formel : un CSP = triplet (X, D, C) avec variables, domaines et contraintes. Vous implementerez le backtracking avec les heuristiques MRV (Minimum Remaining Values) et LCV (Least Constraining Value), et comparerez avec la recherche aveugle de Search-2.

**CSP-2 (Consistency)** introduit la propagation de contraintes -- la cle qui transforme un backtracking naif en solveur efficace. AC-3 (Arc Consistency), Forward Checking et MAC (Maintaining Arc Consistency) sont implementes et compares sur des instances croissantes.

**CSP-3 (Advanced)** entre dans le monde industriel avec les contraintes globales d'OR-Tools CP-SAT : AllDifferent, Cumulative, Circuit. Vous decouvrirez aussi la recherche dans les voisinages larges (LNS) pour les problemes a grande echelle.

**CSP-4 (Scheduling)** applique les contraintes globales aux problemes d'ordonnancement : Job-Shop (JSSP), RCPSP (Resource-Constrained Project Scheduling), et Nurse Scheduling. Les intervalles (IntervalVar), les contraintes NoOverlap et Cumulative deviennent vos outils quotidiens.

**CSP-5 (Optimization)** couvre les classiques de l'optimisation combinatoire : Bin Packing, Knapsack, Cutting Stock, Portfolio Optimization. Les contraintes de cardinalite et les objectifs multi-criteres completent la boite a outils.

**CSP-6 (Hybridization)** est le notebook le plus avance : Lazy Clause Generation (LCG) qui combine CP et SAT, l'hybridation CP+ML pour guider la recherche, et meme LLM+CSP pour la generation de contraintes a partir de langage naturel. Un pont vers la recherche contemporaine.

**CSP-7 (Soft Constraints)** etend le cadre aux problemes ou toutes les contraintes ne peuvent etre satisfaites simultanement : Fuzzy CSP, Weighted CSP, et le cadre theorique des Semirings. Essentiel pour les applications reelles ou les compromis sont inevitables.

**CSP-8 (Temporal)** specialise les CSP au raisonnement temporel : algebre d'intervalles d'Allen (13 relations), Simple Temporal Problems (STP), et Temporal CSP (TCSP). Applications en planification et diagnostic.

**CSP-9 (Distributed)** explore les CSP multi-agents : Asynchronous Backtracking (ABT), Asynchronous Weak-Commitment (AWC), et les approches preservant la confidentialite. Connecte avec les systemes multi-agents et la planification distribuee.

## FAQ / Troubleshooting

| Probleme | Solution |
|----------|----------|
| `ModuleNotFoundError: ortools` | `pip install ortools` — seul dependency externe de la serie |
| Solveur CP-SAT trop lent sur les grandes instances | Activer les contraintes globales (AllDifferent, Cumulative) plutot que des contraintes binaires. Utiliser LNS (CSP-3) |
| CSP-6 : LLM+CSP necessite une cle API | La section LLM est optionnelle. Les sections LCG et CP+ML fonctionnent sans API |
| CSP-9 : les algorithmes distribues ne convergent pas | Verifier que le reseau de contraintes est un arbre ou utiliser AWC (Weak-Commitment) au lieu d'ABT |
| Comment choisir entre CP-SAT et SAT solver ? | CP-SAT pour les contraintes globales et l'optimisation (objectif). SAT pour la decision pure (satisfiabilite). CSP-6 detaille les compromis |
| Ou sont les applications concretes ? | Voir [Applications/](../Applications/) pour 21 notebooks d'application (N-Queens, Nurse Scheduling, VRP, TSP, etc.) |

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
