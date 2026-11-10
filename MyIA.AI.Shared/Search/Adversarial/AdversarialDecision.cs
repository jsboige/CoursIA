namespace MyIA.AI.Shared.Search.Adversarial;

/// <summary>
/// Decision rendue par un moteur adversarial : le coup choisi, la valeur minimax
/// associee, et les compteurs qui permettent de comparer les moteurs entre eux.
/// </summary>
/// <remarks>
/// Transcription du <c>GameMoveResult</c> du patrimoine : y survivent le coup
/// (<c>Action</c>) et les metriques (<c>Metrics</c>) ; la plomberie DNN/Flee
/// (<c>GameAgentInfo</c>, evaluation d'expressions) n'est pas portee -- c'est de
/// la configuration d'hote, pas de l'algorithme.
/// </remarks>
/// <typeparam name="TAction">Type d'un coup.</typeparam>
public sealed class AdversarialDecision<TAction>
{
    /// <summary>Coup choisi par le moteur.</summary>
    public TAction Action { get; }

    /// <summary>Valeur minimax du coup choisi, du point de vue du joueur qui decidait.</summary>
    public double Value { get; }

    /// <summary>Compteurs du moteur pour cette decision.</summary>
    public AdversarialMetrics Metrics { get; }

    /// <summary>Profondeur exacte a laquelle la decision a ete etablie.</summary>
    public int Depth { get; }

    public AdversarialDecision(TAction action, double value, AdversarialMetrics metrics, int depth)
    {
        Action = action;
        Value = value;
        Metrics = metrics;
        Depth = depth;
    }
}

/// <summary>
/// Compteurs communs aux moteurs adversariaux. Ils sont la preuve de travail des
/// temoins : l'egalite des decisions entre minimax et alpha-beta ne dit rien tant
/// que l'ecart de noeuds developpes n'est pas mesure a cote.
/// </summary>
public sealed class AdversarialMetrics
{
    /// <summary>Noeuds (etats) developpes, toutes profondeurs confondues.</summary>
    public int ExpandedNodes { get; internal set; }

    /// <summary>Coups engendes puis, pour alpha-beta, elagues sans etre developpes.</summary>
    public int GeneratedActions { get; internal set; }

    /// <summary>Branches coupees par l'elagage alpha-beta. Zero pour le minimax pur.</summary>
    public int PrunedBranches { get; internal set; }

    /// <summary>Profondeur maximale atteinte pendant la recherche.</summary>
    public int MaxDepthReached { get; internal set; }

    /// <summary>
    /// Transcription du <c>Metrics</c> AIMA : les cles portent les memes noms que
    /// la source Java (<c>nodesExpanded</c>, <c>maxDepth</c>), plus le compteur
    /// d'elagage propre au port.
    /// </summary>
    public IReadOnlyDictionary<string, string> AsMap() => new Dictionary<string, string>
    {
        ["nodesExpanded"] = ExpandedNodes.ToString(),
        ["maxDepth"] = MaxDepthReached.ToString(),
        ["actionsGenerated"] = GeneratedActions.ToString(),
        ["branchesPruned"] = PrunedBranches.ToString(),
    };
}
