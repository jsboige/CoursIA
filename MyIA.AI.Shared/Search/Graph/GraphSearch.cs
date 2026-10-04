using System;
using System.Collections.Generic;

namespace MyIA.AI.Shared.Search.Graph;

/// <summary>
/// Recherche en file sur un <see cref="ISearchProblem{TState, TAction}"/> : largeur,
/// profondeur, profondeur limitee, approfondissement iteratif, cout uniforme,
/// greedy best-first et A*.
/// </summary>
/// <remarks>
/// <para>
/// Port du patrimoine Aricie (EPIC #7265, pepite B2). La source d'origine
/// (<c>Libraries/AI/Search.cs</c>) construisait un <c>SearchAgent</c> au-dessus des
/// classes <c>aima.core.search.*</c>, une traduction IKVM de la bibliotheque Java
/// AIMA : elle n'est pas recompilable ici. Ceci est une reecriture C# des memes
/// algorithmes, sans dependance DNN ni Java.
/// </para>
/// <para>
/// La file est unique et porte une priorite <c>(cle, rang)</c> : le rang departage les
/// ex aequo par ordre d'insertion (croissant en largeur et en cout uniforme, decroissant
/// en profondeur). C'est ce qui rend les compteurs reproductibles d'une execution a
/// l'autre — sans lui, deux strategies a egalite de priorite exploreraient des arbres
/// differents et la comparaison des compteurs ne prouverait rien.
/// </para>
/// </remarks>
/// <typeparam name="TState">Type de l'etat.</typeparam>
/// <typeparam name="TAction">Type de l'action.</typeparam>
public sealed class GraphSearch<TState, TAction>
{
    private PriorityQueue<SearchNode<TState, TAction>, (double Priority, long Rank)> _frontier = new();
    private long _rank;

    /// <summary>Strategie de file ; largeur d'abord par defaut.</summary>
    public SearchStrategy Strategy { get; init; } = SearchStrategy.BreadthFirst;

    /// <summary>
    /// Borne de profondeur, utilisee par <see cref="SearchStrategy.DepthLimited"/> et comme
    /// plafond de <see cref="SearchStrategy.IterativeDeepening"/>. Cinq par defaut, comme le
    /// <c>DepthLimit</c> du patrimoine (<c>Libraries/AI/Search.cs</c>).
    /// </summary>
    public int DepthLimit { get; init; } = 5;

    /// <summary>
    /// Estimation du cout restant jusqu'au but. Obligatoire pour
    /// <see cref="SearchStrategy.GreedyBestFirst"/> et <see cref="SearchStrategy.AStar"/>,
    /// ignoree ailleurs. Admissible (jamais surestimee) pour que A* reste optimal.
    /// </summary>
    public Func<TState, double>? Heuristic { get; init; }

    /// <summary>
    /// Vrai pour une recherche en arbre (aucun ensemble des etats developpes) ; faux par
    /// defaut, c'est-a-dire recherche en graphe. Le patrimoine exposait ce choix via
    /// <c>QueueSearchType</c>.
    /// </summary>
    public bool TreeSearch { get; init; }

    /// <summary>Noeuds developpes lors du dernier <see cref="Solve"/>.</summary>
    public int ExpandedNodes { get; private set; }

    /// <summary>Noeuds engendres lors du dernier <see cref="Solve"/>.</summary>
    public int GeneratedNodes { get; private set; }

    /// <summary>Taille maximale de la file lors du dernier <see cref="Solve"/>.</summary>
    public int MaxFrontierSize { get; private set; }

    /// <summary>
    /// Cherche une solution. Rend <c>null</c> quand aucune n'existe dans le domaine
    /// explore (probleme insoluble, ou borne de profondeur atteinte).
    /// </summary>
    public SearchOutcome<TState, TAction>? Solve(ISearchProblem<TState, TAction> problem)
    {
        ArgumentNullException.ThrowIfNull(problem);
        RequireHeuristic();

        ExpandedNodes = 0;
        GeneratedNodes = 0;
        MaxFrontierSize = 0;

        if (Strategy == SearchStrategy.IterativeDeepening)
        {
            // Les compteurs s'accumulent sur les iterations : c'est le cout total reel
            // de la strategie, et c'est precisement ce qui la rend mesurable face a la
            // profondeur limitee jouee une seule fois.
            for (int limit = 0; limit <= DepthLimit; limit++)
            {
                SearchOutcome<TState, TAction>? outcome = Run(problem, SearchStrategy.DepthLimited, limit);
                if (outcome is not null)
                {
                    return outcome;
                }
            }

            return null;
        }

        int depthLimit = Strategy == SearchStrategy.DepthLimited ? DepthLimit : int.MaxValue;
        return Run(problem, Strategy, depthLimit);
    }

    private void RequireHeuristic()
    {
        bool informed = Strategy is SearchStrategy.GreedyBestFirst or SearchStrategy.AStar;
        if (informed && Heuristic is null)
        {
            throw new InvalidOperationException(
                $"La strategie {Strategy} exige une heuristique : renseigner {nameof(Heuristic)}.");
        }
    }

    private SearchOutcome<TState, TAction>? Run(
        ISearchProblem<TState, TAction> problem,
        SearchStrategy strategy,
        int depthLimit)
    {
        _frontier = new PriorityQueue<SearchNode<TState, TAction>, (double, long)>();
        _rank = 0;

        Dictionary<TState, double> bestKnown = new();
        HashSet<TState> explored = new();

        SearchNode<TState, TAction> root = new(problem.InitialState, null, default, 0.0, 0);
        bestKnown[problem.InitialState] = 0.0;
        Push(root, Priority(strategy, root));

        while (_frontier.Count > 0)
        {
            SearchNode<TState, TAction> node = _frontier.Dequeue();

            if (!TreeSearch && explored.Contains(node.State))
            {
                continue;
            }

            // Entree perimee : un chemin moins cher vers le meme etat a ete trouve
            // apres sa mise en file.
            if (bestKnown.TryGetValue(node.State, out double known) && known < node.PathCost)
            {
                continue;
            }

            ExpandedNodes++;

            if (problem.IsGoal(node.State))
            {
                return new SearchOutcome<TState, TAction>(node, ExpandedNodes, GeneratedNodes, MaxFrontierSize);
            }

            if (!TreeSearch)
            {
                explored.Add(node.State);
            }

            if (node.Depth >= depthLimit)
            {
                continue;
            }

            foreach (TAction action in problem.Actions(node.State))
            {
                TState next = problem.Result(node.State, action);
                double cost = node.PathCost + problem.StepCost(node.State, action, next);
                GeneratedNodes++;

                if (!TreeSearch && explored.Contains(next))
                {
                    continue;
                }

                if (bestKnown.TryGetValue(next, out double best) && best <= cost)
                {
                    continue;
                }

                bestKnown[next] = cost;
                SearchNode<TState, TAction> child = new(next, node, action, cost, node.Depth + 1);
                Push(child, Priority(strategy, child));
            }
        }

        return null;
    }

    private double Priority(SearchStrategy strategy, SearchNode<TState, TAction> node) => strategy switch
    {
        SearchStrategy.UniformCost => node.PathCost,
        SearchStrategy.GreedyBestFirst => Heuristic!(node.State),
        SearchStrategy.AStar => node.PathCost + Heuristic!(node.State),
        _ => 0.0,
    };

    private void Push(SearchNode<TState, TAction> node, double priority)
    {
        bool depthFirst = Strategy is SearchStrategy.DepthFirst or SearchStrategy.DepthLimited;
        _rank++;
        _frontier.Enqueue(node, (priority, depthFirst ? -_rank : _rank));

        if (_frontier.Count > MaxFrontierSize)
        {
            MaxFrontierSize = _frontier.Count;
        }
    }
}
