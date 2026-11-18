namespace MyIA.AI.Shared.Search.Csp;

/// <summary>
/// Heuristique de choix de la variable a affecter.
/// </summary>
/// <remarks>
/// Port du noyau CSP d'AIMA (EPIC #7265, pepite B1) : les trois strategies du
/// patrimoine d'origine sont conservees.
/// </remarks>
public enum VariableSelection
{
    /// <summary>Ordre de declaration : la reference, sans heuristique.</summary>
    DefaultOrder,

    /// <summary>MRV — la variable au domaine restant le plus petit (fail-first).</summary>
    MinimumRemainingValues,

    /// <summary>MRV avec degre en depart d'egalite : brise les ex aequo par le nombre de contraintes.</summary>
    MinimumRemainingValuesDegree,
}

/// <summary>
/// Inference appliquee apres chaque affectation.
/// </summary>
/// <remarks>Port du noyau CSP d'AIMA (EPIC #7265, pepite B1).</remarks>
public enum InferenceStrategy
{
    /// <summary>Aucune propagation : le backtracking verifie seulement la coherence locale.</summary>
    None,

    /// <summary>Forward checking — les domaines des voisins perdent les valeurs incompatibles.</summary>
    ForwardChecking,

    /// <summary>AC-3 — coherence d'arc sur tout le reseau, par revision des arcs binaires.</summary>
    Ac3,
}
