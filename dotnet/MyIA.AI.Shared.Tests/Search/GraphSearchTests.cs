using System;
using System.Collections.Generic;
using System.Linq;
using MyIA.AI.Shared.Search.Graph;
using Xunit;
using Xunit.Abstractions;

namespace MyIA.AI.Shared.Tests.Search;

/// <summary>
/// Tests du moteur de recherche porte depuis AIMA (EPIC #7265, pepite B2).
/// Probleme de reference : la carte de Roumanie (Russell et Norvig, figure 3.2),
/// le probleme canonique du chapitre « recherche ».
/// </summary>
public sealed class GraphSearchTests
{
    private readonly ITestOutputHelper _output;

    public GraphSearchTests(ITestOutputHelper output) => _output = output;

    /// <summary>
    /// Carte de Roumanie : vingt villes, routes symetriques ponderees, but Bucarest.
    /// Les distances a vol d'oiseau vers Bucarest sont celles d'AIMA et servent
    /// d'heuristique admissible au sens strict (aucune ne surestime la route reelle).
    /// </summary>
    private sealed class Romania : ISearchProblem<string, string>
    {
        private static readonly Dictionary<string, (string Neighbour, double Cost)[]> Roads = new()
        {
            ["Arad"] = new[] { ("Sibiu", 140d), ("Timisoara", 118d), ("Zerind", 75d) },
            ["Bucharest"] = new[] { ("Fagaras", 211d), ("Giurgiu", 90d), ("Pitesti", 101d), ("Urziceni", 85d) },
            ["Craiova"] = new[] { ("Dobreta", 120d), ("Pitesti", 138d), ("RimnicuVilcea", 146d) },
            ["Dobreta"] = new[] { ("Craiova", 120d), ("Mehadia", 75d) },
            ["Eforie"] = new[] { ("Hirsova", 86d) },
            ["Fagaras"] = new[] { ("Bucharest", 211d), ("Sibiu", 99d) },
            ["Giurgiu"] = new[] { ("Bucharest", 90d) },
            ["Hirsova"] = new[] { ("Eforie", 86d), ("Urziceni", 98d) },
            ["Iasi"] = new[] { ("Neamt", 87d), ("Vaslui", 92d) },
            ["Lugoj"] = new[] { ("Mehadia", 70d), ("Timisoara", 111d) },
            ["Mehadia"] = new[] { ("Dobreta", 75d), ("Lugoj", 70d) },
            ["Neamt"] = new[] { ("Iasi", 87d) },
            ["Oradea"] = new[] { ("Zerind", 71d) },
            ["Pitesti"] = new[] { ("Bucharest", 101d), ("Craiova", 138d), ("RimnicuVilcea", 97d) },
            ["RimnicuVilcea"] = new[] { ("Craiova", 146d), ("Pitesti", 97d), ("Sibiu", 80d) },
            ["Sibiu"] = new[] { ("Arad", 140d), ("Fagaras", 99d), ("Oradea", 151d), ("RimnicuVilcea", 80d) },
            ["Timisoara"] = new[] { ("Arad", 118d), ("Lugoj", 111d) },
            ["Urziceni"] = new[] { ("Bucharest", 85d), ("Hirsova", 98d), ("Vaslui", 142d) },
            ["Vaslui"] = new[] { ("Iasi", 92d), ("Urziceni", 142d) },
            ["Zerind"] = new[] { ("Arad", 75d), ("Oradea", 71d) },
        };

        private static readonly Dictionary<string, double> StraightLine = new()
        {
            ["Arad"] = 366d, ["Bucharest"] = 0d, ["Craiova"] = 160d, ["Dobreta"] = 242d,
            ["Eforie"] = 161d, ["Fagaras"] = 176d, ["Giurgiu"] = 77d, ["Hirsova"] = 151d,
            ["Iasi"] = 226d, ["Lugoj"] = 244d, ["Mehadia"] = 241d, ["Neamt"] = 234d,
            ["Oradea"] = 380d, ["Pitesti"] = 100d, ["RimnicuVilcea"] = 193d, ["Sibiu"] = 253d,
            ["Timisoara"] = 329d, ["Urziceni"] = 80d, ["Vaslui"] = 199d, ["Zerind"] = 374d,
        };

        public string InitialState => "Arad";

        public IReadOnlyList<string> Actions(string state) =>
            Roads[state].Select(road => road.Neighbour).ToArray();

        public string Result(string state, string action) => action;

        public bool IsGoal(string state) => state == "Bucharest";

        public double StepCost(string state, string action, string nextState) =>
            Roads[state].First(road => road.Neighbour == action).Cost;

        public static double Heuristic(string state) => StraightLine[state];
    }

    private static GraphSearch<string, string> Search(
        SearchStrategy strategy,
        bool informed = false,
        int depthLimit = 5,
        bool treeSearch = false)
    {
        GraphSearch<string, string> search = new()
        {
            Strategy = strategy,
            DepthLimit = depthLimit,
            TreeSearch = treeSearch,
            Heuristic = informed ? Romania.Heuristic : null,
        };
        return search;
    }

    [Fact]
    public void AStarShouldReachBucharestByTheCheapestRoute()
    {
        GraphSearch<string, string> search = Search(SearchStrategy.AStar, informed: true);

        SearchOutcome<string, string>? outcome = search.Solve(new Romania());

        Assert.NotNull(outcome);
        Assert.Equal("Bucharest", outcome!.FinalState);
        Assert.Equal(new[] { "Sibiu", "RimnicuVilcea", "Pitesti", "Bucharest" }, outcome.Actions);
        Assert.Equal(418d, outcome.PathCost, 3);
        _output.WriteLine($"A* : {string.Join(" -> ", outcome.Actions)} | {outcome}");
    }

    [Fact]
    public void UniformCostShouldReachBucharestByTheCheapestRoute()
    {
        GraphSearch<string, string> search = Search(SearchStrategy.UniformCost);

        SearchOutcome<string, string>? outcome = search.Solve(new Romania());

        Assert.NotNull(outcome);
        Assert.Equal(418d, outcome!.PathCost, 3);
        _output.WriteLine($"cout uniforme : {string.Join(" -> ", outcome.Actions)} | {outcome}");
    }

    /// <summary>
    /// La largeur d'abord rend le chemin au plus petit nombre d'actions, pas le moins
    /// cher : c'est la limite que le chapitre pose et que ce test fixe. Sans lui,
    /// l'ecart de cout avec A* serait attribue a une mauvaise implementation plutot
    /// qu'a la propriete de la strategie.
    /// </summary>
    [Fact]
    public void BreadthFirstShouldReturnTheFewestActionsEvenWhenCostlier()
    {
        GraphSearch<string, string> search = Search(SearchStrategy.BreadthFirst);

        SearchOutcome<string, string>? outcome = search.Solve(new Romania());

        Assert.NotNull(outcome);
        Assert.Equal(3, outcome!.Actions.Count);
        Assert.Equal(450d, outcome.PathCost, 3);
        _output.WriteLine($"largeur : {string.Join(" -> ", outcome.Actions)} | {outcome}");
    }

    /// <summary>
    /// A* avec une heuristique nulle a exactement la fonction d'evaluation du cout
    /// uniforme. Ce test etablit que l'heuristique est la <b>seule</b> difference entre
    /// les deux strategies : sans lui, l'ecart de noeuds developpes mesure plus bas
    /// pourrait venir d'un detail d'implementation du depart d'egalite.
    /// </summary>
    [Fact]
    public void AStarWithZeroHeuristicShouldExploreExactlyAsMuchAsUniformCost()
    {
        GraphSearch<string, string> uniformCost = Search(SearchStrategy.UniformCost);
        GraphSearch<string, string> aStar = new()
        {
            Strategy = SearchStrategy.AStar,
            Heuristic = _ => 0d,
        };

        Assert.NotNull(uniformCost.Solve(new Romania()));
        Assert.NotNull(aStar.Solve(new Romania()));

        _output.WriteLine($"sans heuristique : cout uniforme={uniformCost.ExpandedNodes} developpes ; A*={aStar.ExpandedNodes} developpes");
        Assert.Equal(uniformCost.ExpandedNodes, aStar.ExpandedNodes);
    }

    /// <summary>
    /// C'est la mesure qui rend l'heuristique falsifiable plutot qu'affirmee : sur la
    /// carte de Roumanie, A* doit developper strictement moins de noeuds que le cout
    /// uniforme, tout en rendant le meme cout de chemin.
    /// </summary>
    [Fact]
    public void AStarShouldExploreFewerNodesThanUniformCostWithAnAdmissibleHeuristic()
    {
        GraphSearch<string, string> uniformCost = Search(SearchStrategy.UniformCost);
        GraphSearch<string, string> aStar = Search(SearchStrategy.AStar, informed: true);

        SearchOutcome<string, string>? blind = uniformCost.Solve(new Romania());
        SearchOutcome<string, string>? guided = aStar.Solve(new Romania());

        Assert.NotNull(blind);
        Assert.NotNull(guided);
        Assert.Equal(blind!.PathCost, guided!.PathCost, 3);

        _output.WriteLine($"cout uniforme={uniformCost.ExpandedNodes} developpes ; A*={aStar.ExpandedNodes} developpes");
        Assert.True(
            aStar.ExpandedNodes < uniformCost.ExpandedNodes,
            $"A* a developpe {aStar.ExpandedNodes} noeuds contre {uniformCost.ExpandedNodes} pour le cout uniforme.");
    }

    [Fact]
    public void GreedyBestFirstShouldReachTheGoalWithoutGuaranteeingTheCheapestRoute()
    {
        GraphSearch<string, string> search = Search(SearchStrategy.GreedyBestFirst, informed: true);

        SearchOutcome<string, string>? outcome = search.Solve(new Romania());

        Assert.NotNull(outcome);
        Assert.Equal("Bucharest", outcome!.FinalState);
        // Greedy suit l'heuristique seule : il atteint le but, sans optimalite promise.
        Assert.True(outcome.PathCost >= 418d, $"greedy a rendu {outcome.PathCost}, moins que l'optimum 418.");
        _output.WriteLine($"greedy : {string.Join(" -> ", outcome.Actions)} | {outcome}");
    }

    /// <summary>
    /// La profondeur limitee a deux echoue sur la carte de Roumanie (Bucarest est a
    /// trois pas d'Arad) et reussit a trois : la borne est donc reellement appliquee,
    /// et non contournee par un retour a la recherche en graphe.
    /// </summary>
    [Fact]
    public void DepthLimitedShouldRespectItsBound()
    {
        Assert.Null(Search(SearchStrategy.DepthLimited, depthLimit: 2).Solve(new Romania()));

        SearchOutcome<string, string>? atThree = Search(SearchStrategy.DepthLimited, depthLimit: 3).Solve(new Romania());
        Assert.NotNull(atThree);
        Assert.Equal(3, atThree!.Actions.Count);
    }

    [Fact]
    public void IterativeDeepeningShouldFindTheShallowestGoal()
    {
        GraphSearch<string, string> search = Search(SearchStrategy.IterativeDeepening);

        SearchOutcome<string, string>? outcome = search.Solve(new Romania());

        Assert.NotNull(outcome);
        Assert.Equal(3, outcome!.Actions.Count);
        _output.WriteLine($"approfondissement iteratif : {outcome}");
    }

    /// <summary>
    /// La recherche en arbre ne tient pas d'ensemble des etats developpes : elle
    /// developpe donc au moins autant que la recherche en graphe sur le meme probleme.
    /// </summary>
    [Fact]
    public void TreeSearchShouldNotExploreFewerNodesThanGraphSearch()
    {
        GraphSearch<string, string> graph = Search(SearchStrategy.BreadthFirst);
        GraphSearch<string, string> tree = Search(SearchStrategy.BreadthFirst, treeSearch: true);

        Assert.NotNull(graph.Solve(new Romania()));
        Assert.NotNull(tree.Solve(new Romania()));

        _output.WriteLine($"largeur : graphe={graph.ExpandedNodes} developpes ; arbre={tree.ExpandedNodes} developpes");
        Assert.True(tree.ExpandedNodes >= graph.ExpandedNodes);
    }

    [Fact]
    public void SearchShouldBeDeterministic()
    {
        SearchOutcome<string, string> first = Search(SearchStrategy.AStar, informed: true).Solve(new Romania())!;
        SearchOutcome<string, string> second = Search(SearchStrategy.AStar, informed: true).Solve(new Romania())!;

        Assert.Equal(first.Actions, second.Actions);
        Assert.Equal(first.PathCost, second.PathCost, 3);
    }

    [Fact]
    public void InformedStrategyWithoutHeuristicShouldBeRejected()
    {
        GraphSearch<string, string> search = new() { Strategy = SearchStrategy.AStar };

        InvalidOperationException error = Assert.Throws<InvalidOperationException>(() => search.Solve(new Romania()));

        Assert.Contains("heuristique", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void SearchNodePathShouldWalkBackToTheRoot()
    {
        SearchOutcome<string, string> outcome = Search(SearchStrategy.AStar, informed: true).Solve(new Romania())!;

        Assert.Equal("Arad", new Romania().InitialState);
        Assert.Equal(4, outcome.Actions.Count);
        Assert.Contains("Pitesti", outcome.Actions, StringComparer.Ordinal);
        Assert.DoesNotContain("Arad", outcome.Actions, StringComparer.Ordinal);
    }
}
