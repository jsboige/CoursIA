# Partie 3 : Recherche heuristique avancée

[← Partie 2 : Programmation par contraintes](../Part2-CSP/README.md) | [↑ Série Search](../README.md) | [Partie 4 : Métaheuristiques composables →](../Part4-Metaheuristics/README.md)

La Partie 1 a posé les heuristiques *admissibles* (Manhattan pour A\*/IDA\*) et promis l'optimalité en échange. Mais que faire quand l'heuristique admissible reste trop faible pour résoudre à l'optimum un problème vraiment difficile ? Cette troisième partie explore les techniques qui repoussent ce plafond : les **bases de données de motifs** (Pattern Databases), où l'heuristique n'est plus *calculée* mais *précalculée* une fois pour toutes par retournement du problème, puis stockée dans une table consulted en temps constant. C'est l'art de payer un coût de mémoire pour gagner plusieurs ordres de grandeur en temps de recherche.

Le fil rouge est le **15-puzzle** (taquin 4×4) — le banc d'essai historique de la recherche heuristique depuis Korf (1985). Search-12 montre que l'heuristique de Manhattan, bien qu'admissible et donc optimale en théorie, explore des centaines de milliards de nœuds sur les instances difficiles (~50 coups optimaux) parce qu'elle ignore les interactions entre tuiles. La solution SOTA — les Pattern Databases additives de Korf & Felner (2002) — décompose le puzzle en sous-puzzles indépendants, précalcule l'optimum de chacun par recherche arrière (*backward search* depuis le but), et somme les contributions sans violer l'admissibilité. Le gain est spectaculaire et la leçon générale : pour la recherche à l'optimum, une heuristique *informer* (plus proche du vrai coût) vaut mieux qu'une heuristique *admissible mais myope*.

## Pourquoi cette partie

Cette partie occupe une position charnière. Elle **prolonge la Partie 1** (recherche heuristique : A\*, IDA\*, admissibilité vue en Search-3) en poussant la qualité de l'heuristique jusqu'à son extremum, **sans relever de la Partie 2** (programmation par contraintes : on explore toujours, on ne propage pas) **ni de la Partie 4** (métaheuristiques : on cherche ici l'optimalité garantie, pas une approximation). C'est le moment où la série pose la question de la **mémoire comme ressource algorithmique** : jusqu'où peut-on précalculer, et comment décomposer un problème pour que ce précalcul reste abordable ? Cette sensibilité — doser mémoire contre temps, décomposer pour régner — est exactement ce qui sépare un solveur qui termine d'un solveur qui explore jusqu'à l'épuisement.

## Objectifs d'apprentissage

À l'issue de cette partie, vous serez capable de :

1. **Diagnostiquer** les limites d'une heuristique admissible mais myope (Manhattan) sur un problème à interactions
2. **Construire** une Pattern Database par retournement du problème (recherche arrière depuis le but, BFS sur l'espace inversé)
3. **Combiner** plusieurs PDB partielles en une heuristique additive admissible (Korf & Felner 2002)
4. **Mesurer** le compromis mémoire/temps : coût du précalcul et de la table vs gain en nœuds explorés
5. **Situer** les PDB dans le paysage des heuristiques informées (entre Manhattan et une heuristique parfaite)

## Notebooks

| # | Notebook | Kernel | Contenu | Durée | Prérequis |
|---|----------|--------|---------|-------|-----------|
| 1 | [Search-12-PatternDatabases](Search-12-PatternDatabases.ipynb) | Python 3 | Pattern Databases (Culberson & Schaeffer 1996), PDB additives (Korf & Felner 2002), 15-puzzle optimal, IDA\* | ~1h30 | [Search-3](../Part1-Foundations/Search-3-Informed.ipynb) |
| 2 | [Search-13-LimitedDiscrepancySearch](Search-13-LimitedDiscrepancySearch.ipynb) | Python 3 | Limited Discrepancy Search (Harvey & Ginsberg 1995), sac à dos 0/1, greedy vs LDS(k) vs exhaustif | ~45min | [Search-3](../Part1-Foundations/Search-3-Informed.ipynb) |
| 3 | [Search-14-WeightedAstar](Search-14-WeightedAstar.ipynb) | Python 3 | Weighted A\* (Pohl 1970), recherche à sous-optimalité bornée, f=g+W·h, terrain pondéré, frontière coût/nœuds | ~50min | [Search-3](../Part1-Foundations/Search-3-Informed.ipynb) |
| 3 (.NET) | [Search-14-Weighted A\* (C#)](Search-14-WeightedAstar-Csharp.ipynb) | .NET (C#) | **Jumeau .NET** du notebook Python : même Weighted A\* (Pohl 1970), terrain pondéré, balayage de W — port C# (`PriorityQueue`, tuples value types), garantie $\\text{coût} \\leq W \\cdot \\text{optimal}$ | ~50min | [Search-3](../Part1-Foundations/Search-3-Informed.ipynb) |

Les trois notebooks répondent à la même question — « l'heuristique ne suffit pas à résoudre à l'optimum » — et forment un **triptyque** aux stratégies complémentaires : Search-12 *renforce* l'heuristique (précalcul d'une PDB plus informée, **en gardant l'optimalité**), Search-13 *borne les écarts* à l'heuristique dont on dispose (parier que l'optimum est un proche voisin du chemin greedy, **toujours optimal**), et Search-14 *relâche l'optimalité de façon contrôlée* (accepter une solution au plus $W$ fois l'optimal pour explorer bien moins de nœuds). Les deux premières relèvent la qualité de l'estimation ou de la recherche sans lâcher l'optimum ; la troisième change de contrat — une **borne de qualité paramétrable** contre un gain de vitesse, jusqu'à l'extrême non borné du Greedy.

## Prérequis & environnement

| Besoin | Détail |
|--------|--------|
| **Conceptuel** | [Search-3 (Informed)](../Part1-Foundations/Search-3-Informed.ipynb) : A\*, IDA\*, heuristiques admissibles et consistantes — prérequis obligatoire |
| Python | 3.10+, environnement virtuel recommandé |
| Bibliothèques | `heapq` (tas), standard library ; pas de dépendance lourde |

Pour le setup complet, voir le [README de la série Search](../README.md).

## Ponts vers les autres parties

| Direction | Lien | Relation |
|-----------|------|----------|
| ← Partie 1 (fondations) | [Search-3 — Informed](../Part1-Foundations/Search-3-Informed.ipynb) | Prérequis : A\*, IDA\*, admissibilité — Search-12 en est l'aboutissement heuristique |
| → Partie 4 (métaheuristiques) | [Partie 4 — Métaheuristiques composables](../Part4-Metaheuristics/README.md) | Contraste : Partie 3 cherche l'optimalité garantie (heuristique informée), Partie 4 l'approximation robuste (pas de garantie d'optimalité) |
| ↑ Série Search | [Sommaire Search](../README.md) | Cartographie les quatre parties et les applications |
| Sudoku | [Sudoku](../../Sudoku/README.md) | Même esprit de réduction d'espace, mais par contraintes plutôt que par heuristique |

## Références

Couverture par notebook des sources fondatrices mobilisées dans cette partie :

| Notebook(s) | Référence |
|-------------|-----------|
| Search-12 (15-puzzle optimal) | Korf, R. E. (1985) — « Depth-First Iterative-Deepening: An Optimal Admissible Tree Search », *Artificial Intelligence* 27(1). L'article fondateur d'IDA\*, établit le 15-puzzle comme banc d'essai de la recherche à l'optimum. |
| Search-12 (Pattern Databases) | Culberson, J. C., & Schaeffer, J. (1996) — « Searching with Pattern Databases », *Advances in Artificial Intelligence (AI'97)*. Origine des Pattern Databases par retournement du problème. |
| Search-12 (PDB additives) | Korf, R. E., & Felner, A. (2002) — « Disjoint Pattern Database Heuristics », *Artificial Intelligence* 134(1-2). Les PDB additives disjointes — l'heuristique SOTA qui résout le 15-puzzle (puis le 24-puzzle) à l'optimum. |
| Search-13 (Limited Discrepancy Search) | Harvey, W. D., & Ginsberg, M. L. (1995) — « Limited Discrepancy Search », *Proceedings of IJCAI*. Formalise le principe « l'optimum est un proche voisin du greedy » et l'algorithme LDS(k) qui énumère les chemins à au plus k écarts de l'heuristique. |

---

## Conclusion / Prochaines étapes

### Ce que vous avez appris

Cette troisième partie a poussé la recherche heuristique jusqu'à sa frontière : comment fabriquer une heuristique **assez informée pour résoudre à l'optimum** un problème que l'heuristique classique abandonne. L'arc pédagogique tient en une idée-force — **retourner le problème**. Plutôt que d'estimer le coût d'un état vers le but (Manhattan), on précalcule, une fois pour toutes et depuis le but lui-même, le coût exact de sous-structures indépendantes, puis on somme ces fragments sans jamais violer l'admissibilité. Les Pattern Databases additives (Korf & Felner 2002) incarnent ce principe : elles transforment un précalcul de mémoire en gains de plusieurs ordres de grandeur sur le nombre de nœuds explorés par IDA\*.

Le véritable enseignement est un **réflexe de dosage mémoire/temps** : pour la recherche à l'optimalité garantie, la qualité de l'heuristique est tout, et cette qualité peut s'acheter par une décomposition astucieuse et un précalcul retourné. C'est aussi le point de bascule de la série : ici s'arrête le domaine où l'on exige l'optimalité — au-delà, la Partie 4 relâchera cette exigence pour gagner en robustesse et en scalabilité.

### Prochaines étapes

- **Lâcher l'optimalité, gagner en scalabilité** : la [Partie 4 (métaheuristiques composables)](../Part4-Metaheuristics/README.md) abandonne la garantie d'optimalité pour traiter des espaces où même une PDB serait prohibitif — recuit simulé, algorithmes génétiques, optimisation par essaim, composés en bibliothèque (.NET GeneticSharp).
- **Retour aux fondations** : après avoir vu la puissance d'une heuristique informée, reprendre [Search-3 (Informed)](../Part1-Foundations/Search-3-Informed.ipynb) — IDA\* + Manhattan y apparaît comme le cas de base dont les PDB sont l'aboutissement.
- **La série dans son ensemble** : le [sommaire Search](../README.md) cartographie les quatre parties — celle-ci est la charnière entre les heuristiques fondatrices (Partie 1) et les métaheuristiques approchées (Partie 4).

### Le fil rouge

La recherche à l'optimum pose une question de degré : à quel point une heuristique admissible peut-elle *approcher le vrai coût restant* sans jamais le surestimer ? Manhattan, admissible mais aveugle aux interactions entre tuiles, est honnête mais myope ; les Pattern Databases additives, toujours admissibles mais *informatives*, précalculent par retournement la contribution exacte de sous-puzzles indépendants. Le saut n'est pas dans l'algorithme — IDA\* est le même — mais dans la **qualité de l'estimation**, achetée par de la mémoire et une décomposition qui préserve l'admissibilité. Comprendre cela, c'est comprendre que pour la recherche optimale, la ressource rare n'est pas seulement le temps : c'est aussi une heuristique assez fine, et que cette finesse se fabrique.

## Navigation

[← Partie 2 : Programmation par contraintes](../Part2-CSP/README.md) | [↑ Série Search](../README.md) | [Partie 4 : Métaheuristiques composables →](../Part4-Metaheuristics/README.md)
