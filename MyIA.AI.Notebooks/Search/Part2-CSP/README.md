# Partie 2 : Programmation par Contraintes

[← Partie 1 : Search](../Part1-Foundations/README.md) | [↑ Serie Search](../README.md) | [Applications →](../Applications/README.md)

Au lieu de concevoir un algorithme d'exploration, que se passe-t-il si l'on declare les contraintes du probleme et que l'on laisse le solveur trouver les solutions ? La programmation par contraintes (CSP) represente ce changement de paradigme : on ne cherche plus, on contraint. Ce modele declaratif est au coeur des outils industriels (ordonnancement, logistique, verification) et s'applique naturellement aux problemes NP-difficiles.

Le parcours va des fondamentaux du modele (X, D, C) et du backtracking (CSP-1) a la propagation de contraintes (AC-3, MAC en CSP-2), puis aux extensions avancees : contraintes globales (CSP-3), ordonnancement industriel (CSP-4), optimisation combinatoire (CSP-5), hybridation avec SAT/ML/LLM (CSP-6). Les trois derniers notebooks explorent les frontieres : contraintes souples, temporelles et distribuees.

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

CSP-1 et CSP-2 forment le socle (modele + propagation). A partir de CSP-3, le parcours se divise :

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

La programmation par contraintes est le passage naturel vers l'IA symbolique : OR-Tools CP-SAT rejoint Z3 (SMT solving) dans la serie [SymbolicAI](../../SymbolicAI/README.md), l'ordonnancement mene a la planification PDDL (SymbolicAI/Planning), et les contraintes temporelles (CSP-8) se retrouvent dans le planning temporel. Le notebook CSP-6 (LCG) detaille ces passerelles.
