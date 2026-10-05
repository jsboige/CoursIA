using System;
using System.Collections.Generic;
using System.Linq;
using MyIA.AI.Shared.Search.Graph;
using Xunit;
using Xunit.Abstractions;

namespace MyIA.AI.Shared.Tests.Search;

/// <summary>
/// Temoins adversariaux du moteur de recherche (EPIC #7265, pepite B2).
///
/// La carte de Roumanie est un probleme a couts structures : un echec d'elagage y
/// reste invisible. Chaque temoin ci-dessous est un graphe minimal ou une seule
/// arete fait diverger la strategie de son propre contrat -- nombre d'actions pour
/// la largeur, optimalite pour A*, absence de memoire globale pour le mode arbre,
/// pile interne pour l'approfondissement iteratif.
///
/// Les quatre defauts ont ete constates sur cette branche avant correction
/// (relecture de domaine du 04/10, #19142). Ces tests les pincent : chacun echoue
/// sur l'implementation d'avant, et le temoin inverse montre que le defaut etait
/// conditionnel, donc invisible sur la Roumanie.
/// </summary>
public sealed class GraphSearchWitnessTests
{
    private readonly ITestOutputHelper _output;

    public GraphSearchWitnessTests(ITestOutputHelper output) => _output = output;

    /// <summary>
    /// Graphe oriente pondere minimal. L'ordre du tableau d'aretes est l'ordre
    /// d'exploration des actions : il est significatif dans les temoins.
    /// </summary>
    private sealed class Digraph : ISearchProblem<string, string>
    {
        private readonly Dictionary<string, (string Next, double Cost)[]> _edges;
        private readonly Func<string, double>? _heuristic;

        public Digraph(
            string start,
            string goal,
            Dictionary<string, (string Next, double Cost)[]> edges,
            Func<string, double>? heuristic = null)
        {
            InitialState = start;
            Goal = goal;
            _edges = edges;
            _heuristic = heuristic;
        }

        public string InitialState { get; }

        public string Goal { get; }

        public IReadOnlyList<string> Actions(string state) =>
            _edges.TryGetValue(state, out (string Next, double Cost)[]? edges)
                ? edges.Select(edge => edge.Next).ToArray()
                : Array.Empty<string>();

        public string Result(string state, string action) => action;

        public bool IsGoal(string state) => state == Goal;

        public double StepCost(string state, string action, string nextState) =>
            _edges[state].First(edge => edge.Next == action).Cost;

        public double Heuristic(string state) => _heuristic?.Invoke(state) ?? 0d;
    }

    private static GraphSearch<string, string> Search(
        SearchStrategy strategy,
        Func<string, double>? heuristic = null,
        int depthLimit = 5,
        bool treeSearch = false) =>
        new()
        {
            Strategy = strategy,
            DepthLimit = depthLimit,
            TreeSearch = treeSearch,
            Heuristic = heuristic,
        };

    /// <summary>
    /// S -> A(1), S -> X(10), A -> X(1), X -> G(1) ; actions de S dans l'ordre [A, X].
    /// </summary>
    private static Digraph FewestActionsWitness(bool cheapestFirst) => new(
        "S",
        "G",
        new Dictionary<string, (string Next, double Cost)[]>
        {
            ["S"] = cheapestFirst
                ? new[] { ("X", 10d), ("A", 1d) }
                : new[] { ("A", 1d), ("X", 10d) },
            ["A"] = new[] { ("X", 1d) },
            ["X"] = new[] { ("G", 1d) },
        });

    /// <summary>
    /// Temoin 1 — la largeur perdait le chemin au plus petit nombre d'actions.
    ///
    /// X est atteint en 1 action (cout 10) puis en 2 actions (cout 2). L'elagage
    /// « entree perimee », qui compare des couts, jetait la premiere entree : la
    /// largeur rendait alors A -> X -> G, soit 3 actions, la ou son contrat est
    /// d'en rendre 2. Un elagage par le cout n'a de sens que si la file est
    /// ordonnee par le cout.
    /// </summary>
    [Fact]
    public void BreadthFirstShouldKeepTheFewestActionsWhenACostlierPathArrivesFirst()
    {
        SearchOutcome<string, string>? outcome = Search(SearchStrategy.BreadthFirst)
            .Solve(FewestActionsWitness(cheapestFirst: false));

        Assert.NotNull(outcome);
        Assert.Equal(new[] { "X", "G" }, outcome!.Actions);
        Assert.Equal(2, outcome.Actions.Count);
        Assert.Equal(11d, outcome.PathCost, 3);
        _output.WriteLine($"largeur : {string.Join(" -> ", outcome.Actions)} | {outcome}");
    }

    /// <summary>
    /// Temoin inverse du precedent : avec l'ordre [X, A], la largeur rendait deja
    /// 2 actions. Le defaut etait donc conditionnel a l'ordre des actions — ce qui
    /// explique qu'un probleme a couts structures comme la Roumanie ne le voie pas.
    /// </summary>
    [Fact]
    public void BreadthFirstShouldAlsoKeepTheFewestActionsWhenTheCheapestPathArrivesFirst()
    {
        SearchOutcome<string, string>? outcome = Search(SearchStrategy.BreadthFirst)
            .Solve(FewestActionsWitness(cheapestFirst: true));

        Assert.NotNull(outcome);
        Assert.Equal(new[] { "X", "G" }, outcome!.Actions);
        Assert.Equal(2, outcome.Actions.Count);
    }

    /// <summary>
    /// S -> A(3), S -> B(1), B -> A(1), A -> G(10) ; heuristique h.
    /// </summary>
    private static Digraph ReopeningWitness(Func<string, double> heuristic) => new(
        "S",
        "G",
        new Dictionary<string, (string Next, double Cost)[]>
        {
            ["S"] = new[] { ("A", 3d), ("B", 1d) },
            ["B"] = new[] { ("A", 1d) },
            ["A"] = new[] { ("G", 10d) },
        },
        heuristic);

    /// <summary>
    /// Temoin 2 — A* rendait un cout sous-optimal avec une heuristique ADMISSIBLE
    /// mais incoherente.
    ///
    /// h = { S: 0, A: 0, B: 11, G: 0 } : aucune valeur ne surestime le cout restant
    /// reel, donc l'heuristique est admissible. A, ferme a g = 3, n'etait jamais
    /// rouvert lorsque B offrait g = 2 : le resultat etait 13 au lieu de 12. Le
    /// contrat documente sur <c>Heuristic</c> (admissibilite seule) n'etait donc pas
    /// tenu — soit on rouvre, soit on restreint explicitement le contrat.
    /// </summary>
    [Fact]
    public void AStarShouldBeOptimalWithAnAdmissibleButInconsistentHeuristic()
    {
        Digraph problem = ReopeningWitness(state => state == "B" ? 11d : 0d);

        SearchOutcome<string, string>? outcome = Search(SearchStrategy.AStar, problem.Heuristic).Solve(problem);

        Assert.NotNull(outcome);
        Assert.Equal(12d, outcome!.PathCost, 3);
        Assert.Equal(new[] { "B", "A", "G" }, outcome.Actions);
        _output.WriteLine($"A* admissible-incoherente : {string.Join(" -> ", outcome.Actions)} | {outcome}");
    }

    /// <summary>
    /// Temoin inverse : avec h(B) = 1 l'heuristique devient coherente, et le resultat
    /// etait deja 12. C'est donc bien l'incoherence, et non l'admissibilite, qui
    /// faisait echouer le temoin precedent.
    /// </summary>
    [Fact]
    public void AStarShouldAlsoBeOptimalWhenTheHeuristicIsConsistent()
    {
        Digraph problem = ReopeningWitness(state => state == "B" ? 1d : 0d);

        SearchOutcome<string, string>? outcome = Search(SearchStrategy.AStar, problem.Heuristic).Solve(problem);

        Assert.NotNull(outcome);
        Assert.Equal(12d, outcome!.PathCost, 3);
    }

    /// <summary>
    /// Temoin 3 — le mode arbre conservait l'elagage global <c>bestKnown</c>.
    ///
    /// S -> { A, B } -> C -> G a couts unitaires : la recherche en graphe developpe
    /// 5 noeuds, une recherche en arbre doit en developper 6 — C y est atteint deux
    /// fois (par A puis par B) et developpe deux fois. Le mode arbre rendait 5, donc
    /// la semantique annoncee (« aucun ensemble des etats developpes ») n'etait pas
    /// celle rendue.
    /// </summary>
    [Fact]
    public void TreeSearchShouldNotKeepGlobalMemory()
    {
        Digraph problem = new(
            "S",
            "G",
            new Dictionary<string, (string Next, double Cost)[]>
            {
                ["S"] = new[] { ("A", 1d), ("B", 1d) },
                ["A"] = new[] { ("C", 1d) },
                ["B"] = new[] { ("C", 1d) },
                ["C"] = new[] { ("G", 1d) },
            });

        SearchOutcome<string, string> graph = Search(SearchStrategy.BreadthFirst).Solve(problem)!;
        SearchOutcome<string, string> tree =
            Search(SearchStrategy.BreadthFirst, treeSearch: true).Solve(problem)!;

        Assert.Equal(5, graph.ExpandedNodes);
        Assert.Equal(6, tree.ExpandedNodes);

        // Le meme ecart se lit sur le temoin 1 : sans memoire globale, la largeur en
        // arbre developpe X deux fois et atteint le but en 2 actions, pas en 3.
        SearchOutcome<string, string> treeFewest =
            Search(SearchStrategy.BreadthFirst, treeSearch: true).Solve(FewestActionsWitness(cheapestFirst: false))!;

        Assert.Equal(2, treeFewest.Actions.Count);
        _output.WriteLine($"graphe={graph.ExpandedNodes} arbre={tree.ExpandedNodes} "
                          + $"arbre-temoin1={treeFewest.ExpandedNodes}");
    }

    /// <summary>
    /// Residu du temoin 3 — le mode arbre doit primer sur la memoire par COUT.
    ///
    /// Sur le meme graphe S -> { A, B } -> C -> G a couts unitaires, le regime
    /// cout-ordonne consultait et remplissait <c>bestKnown</c> meme en mode
    /// arbre : cout uniforme et A* (h nulle) developpaient 5 noeuds comme le
    /// graphe, au lieu des 6 de la reference sans dedoublonnage (S, A, B, C,
    /// C', G — C developpe deux fois). Le cout du chemin reste optimal dans
    /// les deux modes ; c'est le contrat de memoire qui divergeait.
    /// </summary>
    [Fact]
    public void TreeSearchShouldPrimeOverCostMemoryForCostOrderedStrategies()
    {
        Digraph problem = new(
            "S",
            "G",
            new Dictionary<string, (string Next, double Cost)[]>
            {
                ["S"] = new[] { ("A", 1d), ("B", 1d) },
                ["A"] = new[] { ("C", 1d) },
                ["B"] = new[] { ("C", 1d) },
                ["C"] = new[] { ("G", 1d) },
            });

        foreach (SearchStrategy strategy in new[]
                 { SearchStrategy.UniformCost, SearchStrategy.AStar })
        {
            // h nulle pour A* : cout uniforme deguise, l'accent porte sur la memoire.
            Func<string, double>? h = strategy == SearchStrategy.AStar ? _ => 0d : null;
            SearchOutcome<string, string> graph = Search(strategy, h).Solve(problem)!;
            SearchOutcome<string, string> tree =
                Search(strategy, h, treeSearch: true).Solve(problem)!;

            Assert.Equal(5, graph.ExpandedNodes);
            Assert.Equal(6, tree.ExpandedNodes);
            // Le cout optimal ne depend pas du regime de memoire ici.
            Assert.Equal(graph.PathCost, tree.PathCost, 3);
            _output.WriteLine($"{strategy} : graphe={graph.ExpandedNodes} "
                              + $"arbre={tree.ExpandedNodes} cout={tree.PathCost:0}");
        }
    }

    /// <summary>
    /// Temoin 4 — l'approfondissement iteratif empilait en FIFO.
    ///
    /// <c>Push</c> lisait la strategie de l'<b>instance</b> (IterativeDeepening) au
    /// lieu de celle de l'<b>iteration</b> (profondeur limitee) : le rang etait
    /// croissant, donc chaque appel se comportait en largeur. S -> [A, B], A -> X,
    /// B -> G, X -> X2, couts unitaires, borne 2 : ID developpait 9 noeuds au lieu
    /// de 7, la somme de ses propres iterations.
    /// </summary>
    [Fact]
    public void IterativeDeepeningShouldStackWithinEachIteration()
    {
        Digraph problem = new(
            "S",
            "G",
            new Dictionary<string, (string Next, double Cost)[]>
            {
                ["S"] = new[] { ("A", 1d), ("B", 1d) },
                ["A"] = new[] { ("X", 1d) },
                ["B"] = new[] { ("G", 1d) },
                ["X"] = new[] { ("X2", 1d) },
            });

        int DepthLimited(int limit)
        {
            GraphSearch<string, string> search = Search(SearchStrategy.DepthLimited, depthLimit: limit);
            search.Solve(problem);
            return search.ExpandedNodes;
        }

        GraphSearch<string, string> deepening = Search(SearchStrategy.IterativeDeepening, depthLimit: 2);
        SearchOutcome<string, string>? outcome = deepening.Solve(problem);

        Assert.NotNull(outcome);
        Assert.Equal(new[] { "B", "G" }, outcome!.Actions);
        Assert.Equal(3, DepthLimited(1));

        // ID developpe exactement la somme de ses iterations : c'est cette egalite
        // qui distingue « la strategie coute ce qu'elle annonce » de « la strategie
        // fait autre chose que ce qu'elle annonce ».
        Assert.Equal(7, deepening.ExpandedNodes);
        Assert.Equal(deepening.ExpandedNodes,
                     DepthLimited(0) + DepthLimited(1) + DepthLimited(2));
        _output.WriteLine($"ID={deepening.ExpandedNodes} DLS(0,1,2)="
                          + $"{DepthLimited(0)},{DepthLimited(1)},{DepthLimited(2)}");
    }
}
