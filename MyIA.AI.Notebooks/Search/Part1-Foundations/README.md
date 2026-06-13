# Partie 1 : Search Fondamental

[↑ Série Search](../README.md) | [Partie 2 : CSP →](../Part2-CSP/README.md)

Comment passer d'une énumération exhaustive à une exploration intelligemment guidée d'un espace d'états ? Cette première partie couvre les trois grands paradigmes de la recherche en IA : systématique (BFS, A*), locale (Hill Climbing, recuit simulé) et évolutive (algorithmes génétiques, PSO). Le fil rouge est la réduction progressive de l'espace de recherche, depuis la formalisation du problème jusqu'aux métaheuristiques comparées sur des benchmarks.

Le parcours s'ouvre sur une idée simple et étonnamment puissante : avant de résoudre un problème, il faut le poser. Search-1 montre qu'un taquin, un aspirateur-robot et une recherche d'itinéraire sont un seul et même objet mathématique — un espace d'états (S, A, T, G) — et que cette formalisation suffit à rendre le problème calculable. Search-2 lance alors l'exploration à l'aveugle : BFS garantit l'optimal mais explose en mémoire, DFS file droit mais peut se perdre, et leurs variantes (UCS, IDDFS) négocient chacune un compromis différent entre garantie et coût. Search-3 apporte la réponse classique à cette explosion : une heuristique — une estimation du chemin restant — et l'algorithme A*, dont l'optimalité tient à une propriété fine, l'admissibilité, que le notebook prend le temps d'éprouver plutôt que de la postuler.

La suite change deux fois de point de vue. Quand seule la destination compte — pas le chemin —, la recherche locale (Search-4) abandonne l'arbre d'exploration pour naviguer de voisin en voisin dans un paysage de fitness, quitte à accepter temporairement de moins bonnes solutions pour s'échapper des optima locaux (recuit simulé, recherche tabou). Les algorithmes génétiques (Search-5) généralisent le procédé : une population entière explore en parallèle, sélection et croisement faisant émerger les bonnes solutions. Et quand l'environnement riposte — un adversaire joue contre vous —, la recherche devient un jeu : Minimax et l'élagage Alpha-Beta (Search-6), puis Monte Carlo Tree Search (Search-7), qui remplace l'évaluation experte par la simulation statistique et mène jusqu'à l'architecture d'AlphaGo.

Trois extensions complètent le panorama. La couverture exacte et les Dancing Links de Knuth (Search-8), structure de données spectaculaire qui résout Sudoku, N-Queens et Pentominoes par simple manipulation de pointeurs. La programmation linéaire (Search-9), qui troque le discret pour le continu et résout en quelques lignes de PuLP des problèmes de transport et de régime alimentaire. Les automates symboliques (Search-10), où les transitions deviennent des prédicats Z3 — premier pont vers l'IA symbolique. Search-11 referme la partie en confrontant les métaheuristiques (PSO, ABC, recuit) sur des benchmarks communs : l'occasion de constater qu'aucune ne domine partout, et d'apprendre à choisir.

## Pourquoi cette partie

Cette partie est l'alphabet de toute la série : la formalisation en espace d'états, le backtracking et les heuristiques qu'on y construit sont réutilisés tels quels par la programmation par contraintes (Partie 2) et par les 21 notebooks d'application. Mais son véritable enseignement est un réflexe d'ingénieur : chaque algorithme y est présenté comme un compromis — complétude contre mémoire, garantie contre temps de calcul, exploration contre exploitation — et jamais comme une recette. C'est ce réflexe, plus que tel ou tel algorithme, qui distingue celui qui applique une bibliothèque de celui qui choisit une stratégie.

## Objectifs d'apprentissage

À l'issue de cette partie, vous serez capable de :

1. **Formaliser** un problème sous forme d'espace d'états (S, A, T, G) et l'implémenter en Python
2. **Choisir** l'algorithme de recherche adapté au problème : systématique (BFS, A*), locale (SA, Tabu), ou évolutive (GA, PSO)
3. **Concevoir et évaluer** des heuristiques admissibles et consistantes pour guider la recherche
4. **Appliquer** la recherche adversariale (Minimax, Alpha-Beta, MCTS) aux jeux à deux joueurs
5. **Comparer** les métaheuristiques sur des benchmarks réels et justifier le choix d'un algorithme

## Notebooks

| # | Notebook | Kernel | Contenu | Durée |
|---|----------|--------|---------|-------|
| 1 | [Search-1-StateSpace](Search-1-StateSpace.ipynb) | Python 3 | Espaces d'états, formalisation (S, A, T, G), taquin, aspirateur, recherche d'itinéraire | ~40 min |
| 2 | [Search-2-Uninformed](Search-2-Uninformed.ipynb) | Python 3 | BFS, DFS, UCS, IDDFS : comparaison des algorithmes non informés | ~50 min |
| 3 | [Search-3-Informed](Search-3-Informed.ipynb) | Python 3 | A*, Greedy, IDA*, heuristiques admissibles et consistantes | ~50 min |
| 4 | [Search-4-LocalSearch](Search-4-LocalSearch.ipynb) | Python 3 | Hill Climbing, Simulated Annealing, Tabu Search, paysages de fitness | ~45 min |
| 5 | [Search-5-GeneticAlgorithms](Search-5-GeneticAlgorithms.ipynb) | Python 3 | Sélection, crossover, mutation, DEAP/PyGAD, théorie unifiée | ~50 min |
| 6 | [Search-6-AdversarialSearch](Search-6-AdversarialSearch.ipynb) | Python 3 | Minimax, Alpha-Beta pruning, Null-window search, tables de transposition | ~1h |
| 7 | [Search-7-MCTS-And-Beyond](Search-7-MCTS-And-Beyond.ipynb) | Python 3 | Monte Carlo Tree Search, UCB1, OpenSpiel, architecture AlphaGo (DQN+MCTS) | ~1h30 |
| 8 | [Search-8-DancingLinks](Search-8-DancingLinks.ipynb) | Python 3 | Algorithme X de Knuth, Dancing Links (DLX), couverture exacte (Sudoku, N-Queens, Pentominoes) | ~1h30 |
| 9 | [Search-9-LinearProgramming](Search-9-LinearProgramming.ipynb) | Python 3 | Programmation linéaire avec PuLP, simplex, problème du transport, diet problem, PLNE | ~2h |
| 10 | [Search-10-SymbolicAutomata](Search-10-SymbolicAutomata.ipynb) | Python 3 | Automates finis (DFA/NFA) avec automata-lib, prédicats Z3, automates symboliques | ~2h |
| 11 | [Search-11-Metaheuristics](Search-11-Metaheuristics.ipynb) | Python 3 | PSO, ABC, SA, BRO avec MEALPy, benchmark comparatif de métaheuristiques | ~1h30 |

## Progression

Les trois premiers notebooks forment le socle commun — on y apprend à poser un problème, puis à l'explorer systématiquement — et tout le reste s'y greffe. Au-delà, le parcours n'est pas linéaire : quatre branches indépendantes s'ouvrent, à prendre dans l'ordre de vos curiosités :

- **Recherche locale et évolutive** : Search-4 (LocalSearch) puis Search-5 (GeneticAlgorithms) puis Search-11 (Metaheuristics)
- **Recherche dans les jeux** : Search-3 puis Search-6 (AdversarialSearch) puis Search-7 (MCTS)
- **Couverture exacte** : Search-2 puis Search-8 (DancingLinks)
- **Indépendants** : Search-9 (LinearProgramming, algèbre linéaire requise) et Search-10 (SymbolicAutomata, liens avec SymbolicAI/SMT/Z3)

Les fondamentaux de cette partie (formalisation, backtracking, heuristiques) sont le prérequis de la [Partie 2 (CSP)](../Part2-CSP/README.md).

## Prérequis & environnement

| Besoin | Détail |
|--------|--------|
| Python | 3.10+, environnement virtuel recommandé |
| `ortools` | Search-9 (Linear Programming) |
| `deap` | Search-5 (Genetic Algorithms) |
| `mealpy` | Search-11 (Métaheuristiques) |
| `z3-solver` | Search-10 (Symbolic Automata) |
| OpenSpiel | Search-7 (MCTS) : requiert WSL ou Linux |

Pour le setup complet, voir le [README de la série Search](../README.md).

## Ponts vers les autres séries

Cette partie irrigue le reste du dépôt : les Dancing Links de Search-8 sont à l'œuvre dans la série [Sudoku](../../Sudoku/README.md), Minimax et MCTS (Search-6/7) se prolongent dans [GameTheory](../../GameTheory/README.md) avec OpenSpiel puis dans [RL](../../RL/README.md) côté politiques apprises, et les prédicats Z3 de Search-10 ouvrent sur [SymbolicAI](../../SymbolicAI/README.md).

## FAQ

| Problème | Solution |
|----------|----------|
| A* trop lent sur les grands graphes | Vérifier que l'heuristique est admissible ET consistante ; essayer IDA* (Search-3), qui consomme moins de mémoire |
| GA stagne sans amélioration | Augmenter le taux de mutation ou la taille de la population ; comparer avec les métaheuristiques de Search-11 |
