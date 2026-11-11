using System.Collections.Generic;

namespace MyIA.AI.Shared.Search.Csp;

/// <summary>
/// Contrainte CSP portant sur une affectation PARTIELLE : une contrainte dont
/// une variable du scope n'est pas encore affectee est consideree satisfaite.
/// C'est ce qui rend la verification utilisable pendant la recherche, ou l'on
/// teste la coherence avant d'avoir une affectation complete.
/// </summary>
/// <remarks>Port du noyau CSP d'AIMA (EPIC #7265, pepite B1).</remarks>
public interface IConstraint
{
    /// <summary>Variables impliquees par la contrainte.</summary>
    IReadOnlyList<Variable> Scope { get; }

    /// <summary>Vrai si la contrainte tient pour cette affectation partielle.</summary>
    bool IsSatisfied(Assignment assignment);
}
