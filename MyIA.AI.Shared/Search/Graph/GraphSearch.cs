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
/// <para>
/// <b>Trois regimes de memoire</b>, et c'est leur confusion qui produisait les defauts
/// corriges en #19142 : une memoire <b>par cout</b> avec reouverture pour les strategies
/// dont la file est ordonnee par le cout (cout uniforme, A*) ; une memoire <b>par
/// ensemble d'etats vus</b> — developpes <i>et</i> en file — pour les autres strategies en
/// mode graphe ; <b>aucune memoire</b> en mode arbre. Un elagage par le cout n'a de sens
/// que dans le premier regime : applique a la largeur, il jette une entree au seul motif
/// qu'elle coute plus cher, alors que la largeur ne classe pas par cout.
/// </para>
/// </remarks>
/// <typeparam name="TState">Type de l'etat.</typeparam>
/// <typeparam name="TAction">Type de l'action.</typeparam>
public sealed class GraphSearch<TState, TAction>
{
    private PriorityQueue<SearchNode<TState, TAction>, (double Priority, long Rank)> _frontier = new();
    private long _rank;

    /// <summary>
    /// Strategie reellement jouee par le <see cref="Run"/> en cours. Elle differe de
    /// <see cref="Strategy"/> pendant l'approfondissement iteratif, dont chaque
    /// iteration joue une profondeur limitee : <see cref="Push"/> doit lire
    /// celle-ci, sinon le rang est croissant et chaque iteration se comporte en largeur.
    /// </summary>
    private SearchStrategy _effective;

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
    /// ignoree ailleurs.
    /// </summary>
    /// <remarks>
    /// <para>
    /// <b>Admissible</b> (jamais surestimee) suffit : A* rouvre un etat deja developpe
    /// lorsqu'un chemin strictement moins cher y mene, donc une heuristique admissible
    /// mais <b>incoherente</b> reste optimale. Exiger la coherence en plus serait une
    /// restriction du contrat, pas une consequence de l'algorithme.
    /// </para>
    /// <para>
    /// L'admissibilite n'est en revanche <b>pas verifiee</b> a l'execution : une
    /// heuristique qui surestime rend A* sous-optimal, y compris avec la reouverture.
    /// </para>
    /// </remarks>
    public Func<TState, double>? Heuristic { get; init; }

    /// <summary>
    /// Vrai pour une recherche en arbre ; faux par defaut, c'est-a-dire recherche en
    /// graphe. Le patrimoine exposait ce choix via <c>QueueSearchType</c>.
    /// </summary>
    /// <remarks>
    /// En mode arbre il n'y a <b>aucune memoire</b> : ni ensemble des etats developpes,
    /// ni tableau des couts connus. Un etat atteint par deux chemins est donc developpe
    /// deux fois, et les compteurs sont plus eleves qu'en mode graphe — c'est la
    /// semantique du mode, pas un surcout. Sur un graphe avec cycle, la recherche peut
    /// ne pas terminer : le mode arbre suppose un espace d'etats en arbre (AIMA §3.3).
    /// </remarks>
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
        _effective = strategy;
        _frontier = new PriorityQueue<SearchNode<TState, TAction>, (double, long)>();
        _rank = 0;

        // Regime de memoire. Les trois sont exclusifs et se lisaient autrefois l'un
        // dans l'autre :
        //   - cout-ordonne : la file classe par le cout, donc « entree perimee » et
        //     reouverture ont un sens (cout uniforme, A*) ;
        //   - graphe sans cout : la file ne classe pas par cout, on retient les etats
        //     VUS (developpes et en file) et le premier chemin rencontre gagne ;
        //   - arbre : aucune memoire, aucun elagage.
        bool costOrdered = strategy is SearchStrategy.UniformCost or SearchStrategy.AStar;
        bool remember = !TreeSearch;

        Dictionary<TState, double> bestKnown = new();
        HashSet<TState> explored = new();
        HashSet<TState> inFrontier = new();

        SearchNode<TState, TAction> root = new(problem.InitialState, null, default, 0.0, 0);
        if (costOrdered)
        {
            bestKnown[problem.InitialState] = 0.0;
        }

        Push(root, Priority(strategy, root));
        inFrontier.Add(problem.InitialState);

        while (_frontier.Count > 0)
        {
            SearchNode<TState, TAction> node = _frontier.Dequeue();
            inFrontier.Remove(node.State);

            if (remember && !costOrdered && explored.Contains(node.State))
            {
                continue;
            }

            // Entree perimee : un chemin MOINS CHER vers le meme etat a ete trouve
            // apres sa mise en file. Ce test n'a de sens que si la file est ordonnee
            // par le cout. Applique a la largeur (#19142), il jetait l'entree d'un
            // etat atteint en une action parce qu'un chemin plus cher... mais plus
            // court en actions existait derriere : la largeur rendait 3 actions la ou
            // son contrat en demande 2.
            if (costOrdered && bestKnown.TryGetValue(node.State, out double known) && known < node.PathCost)
            {
                continue;
            }

            ExpandedNodes++;

            if (problem.IsGoal(node.State))
            {
                return new SearchOutcome<TState, TAction>(node, ExpandedNodes, GeneratedNodes, MaxFrontierSize);
            }

            if (remember)
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

                if (costOrdered)
                {
                    // Memoire par cout : on ne repousse pas un successeur deja atteint
                    // aussi bien ou mieux. Un etat deja DEVELOPPE peut en revanche etre
                    // rouvert si le nouveau chemin est strictement moins cher -- c'est
                    // ce qui rend A* optimal sous admissibilite seule, sans exiger la
                    // coherence de l'heuristique (#19142, temoin a h incoherente).
                    if (bestKnown.TryGetValue(next, out double best) && best <= cost)
                    {
                        continue;
                    }

                    bestKnown[next] = cost;
                }
                else if (remember && (explored.Contains(next) || inFrontier.Contains(next)))
                {
                    // Sans cout dans la priorite, la file ne sait pas departager deux
                    // chemins vers le meme etat : on garde le PREMIER rencontre. C'est
                    // le contrat de la largeur (le minimum d'actions, car la file est
                    // depilee par profondeur croissante) et celui de la profondeur.
                    continue;
                }

                SearchNode<TState, TAction> child = new(next, node, action, cost, node.Depth + 1);
                Push(child, Priority(strategy, child));
                inFrontier.Add(next);
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
        // La strategie de l'ITERATION, pas celle de l'instance : pendant
        // l'approfondissement iteratif, `Strategy` vaut IterativeDeepening et le rang
        // serait croissant, donc chaque iteration se comporterait en largeur (#19142).
        bool depthFirst = _effective is SearchStrategy.DepthFirst or SearchStrategy.DepthLimited;
        _rank++;
        _frontier.Enqueue(node, (priority, depthFirst ? -_rank : _rank));

        if (_frontier.Count > MaxFrontierSize)
        {
            MaxFrontierSize = _frontier.Count;
        }
    }
}
