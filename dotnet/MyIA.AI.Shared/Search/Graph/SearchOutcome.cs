using System.Collections.Generic;

namespace MyIA.AI.Shared.Search.Graph;

/// <summary>
/// Resultat d'une recherche aboutie : le chemin, son cout et les compteurs qui
/// rendent la strategie falsifiable plutot qu'affirmee.
/// </summary>
/// <remarks>
/// Port du patrimoine Aricie (EPIC #7265, pepite B2) : reprend l'instrumentation que
/// <c>SearchAgentInfo.PrintInstrumentation</c> exposait (<c>nodesExpanded</c>,
/// <c>pathCost</c>), mais typee plutot que rendue sous forme de dictionnaire de chaines.
/// </remarks>
/// <typeparam name="TState">Type de l'etat.</typeparam>
/// <typeparam name="TAction">Type de l'action.</typeparam>
public sealed class SearchOutcome<TState, TAction>
{
    internal SearchOutcome(
        SearchNode<TState, TAction> goal,
        int expandedNodes,
        int generatedNodes,
        int maxFrontierSize)
    {
        Actions = goal.Path();
        PathCost = goal.PathCost;
        FinalState = goal.State;
        ExpandedNodes = expandedNodes;
        GeneratedNodes = generatedNodes;
        MaxFrontierSize = maxFrontierSize;
    }

    /// <summary>Actions du chemin solution, de l'etat initial au but.</summary>
    public IReadOnlyList<TAction> Actions { get; }

    /// <summary>Cout cumule du chemin solution.</summary>
    public double PathCost { get; }

    /// <summary>Etat but atteint.</summary>
    public TState FinalState { get; }

    /// <summary>Noeuds developpes (sortis de la file et passes au test de but).</summary>
    public int ExpandedNodes { get; }

    /// <summary>Noeuds engendres (successeurs crees), comptes meme s'ils sont elagues.</summary>
    public int GeneratedNodes { get; }

    /// <summary>
    /// Taille maximale atteinte par la file. Les entrees perimees (surclassees par un
    /// meilleur chemin avant leur sortie) y sont comptees : c'est une borne, pas un
    /// minimum exact.
    /// </summary>
    public int MaxFrontierSize { get; }

    /// <inheritdoc />
    public override string ToString() =>
        $"cout={PathCost}, actions={Actions.Count}, developpes={ExpandedNodes}, file max={MaxFrontierSize}";
}
