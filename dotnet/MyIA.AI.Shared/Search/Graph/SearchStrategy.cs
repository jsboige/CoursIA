namespace MyIA.AI.Shared.Search.Graph;

/// <summary>
/// Strategies de recherche en file implementees par <see cref="GraphSearch{TState, TAction}"/>.
/// </summary>
/// <remarks>
/// <para>
/// Port du patrimoine Aricie (EPIC #7265, pepite B2) : l'enumeration reprend celle de
/// <c>Libraries/AI/Search.cs</c> (<c>KnownUninformedSearch</c> et <c>KnownInformedSearch</c>).
/// </para>
/// <para>
/// Hors de cette tranche, et declare tel quel : la recherche bidirectionnelle
/// (<c>Bidirectional</c>, qui exige un modele d'actions inverses), les strategies
/// recursives (<c>RecursiveAStar</c>, <c>RecursiveGreedyBestFirst</c> — RBFS) et les
/// strategies locales (<c>HillClimbing</c>, <c>SimulatedAnnealing</c>).
/// </para>
/// </remarks>
public enum SearchStrategy
{
    /// <summary>Largeur d'abord — file FIFO. Optimale en nombre d'actions, pas en cout.</summary>
    BreadthFirst,

    /// <summary>Profondeur d'abord — pile LIFO.</summary>
    DepthFirst,

    /// <summary>Profondeur limitee — comme la precedente, bornee par <see cref="GraphSearch{TState, TAction}.DepthLimit"/>.</summary>
    DepthLimited,

    /// <summary>Approfondissement iteratif — profondeur limitee, limite croissante depuis 0.</summary>
    IterativeDeepening,

    /// <summary>Cout uniforme — file de priorite sur le cout du chemin. Optimale.</summary>
    UniformCost,

    /// <summary>Greedy best-first — file de priorite sur l'heuristique seule.</summary>
    GreedyBestFirst,

    /// <summary>A* — file de priorite sur cout du chemin + heuristique.</summary>
    AStar,
}
