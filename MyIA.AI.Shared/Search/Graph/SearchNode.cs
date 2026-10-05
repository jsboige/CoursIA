using System.Collections.Generic;

namespace MyIA.AI.Shared.Search.Graph;

/// <summary>
/// Noeud de l'arbre de recherche : un etat, le chemin qui y mene et son cout.
/// </summary>
/// <remarks>Port du patrimoine Aricie (EPIC #7265, pepite B2) : equivalent C# de
/// <c>aima.core.search.framework.Node</c>, sans dependance Java.</remarks>
/// <typeparam name="TState">Type de l'etat.</typeparam>
/// <typeparam name="TAction">Type de l'action.</typeparam>
public sealed class SearchNode<TState, TAction>
{
    internal SearchNode(
        TState state,
        SearchNode<TState, TAction>? parent,
        TAction? action,
        double pathCost,
        int depth)
    {
        State = state;
        Parent = parent;
        Action = action;
        PathCost = pathCost;
        Depth = depth;
    }

    /// <summary>Etat porte par ce noeud.</summary>
    public TState State { get; }

    /// <summary>Noeud pere, <c>null</c> pour la racine.</summary>
    public SearchNode<TState, TAction>? Parent { get; }

    /// <summary>Action qui a mene a ce noeud ; valeur par defaut pour la racine.</summary>
    public TAction? Action { get; }

    /// <summary>Cout cumule depuis la racine.</summary>
    public double PathCost { get; }

    /// <summary>Nombre d'actions depuis la racine.</summary>
    public int Depth { get; }

    /// <summary>Vrai pour le noeud racine (aucun parent).</summary>
    public bool IsRoot => Parent is null;

    /// <summary>Actions du chemin, de la racine vers ce noeud.</summary>
    public IReadOnlyList<TAction> Path()
    {
        List<TAction> actions = new();
        SearchNode<TState, TAction>? current = this;

        while (current is { IsRoot: false })
        {
            actions.Add(current.Action!);
            current = current.Parent;
        }

        actions.Reverse();
        return actions;
    }

    /// <inheritdoc />
    public override string ToString() =>
        $"noeud(profondeur={Depth}, cout={PathCost}, actions={Path().Count})";
}
