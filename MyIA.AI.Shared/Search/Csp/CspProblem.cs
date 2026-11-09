using System;
using System.Collections.Generic;
using System.Linq;

namespace MyIA.AI.Shared.Search.Csp;

/// <summary>
/// Probleme CSP : un ensemble de variables et de contraintes.
/// La fabrique <see cref="CreateCsp"/> conserve la forme fluide du patrimoine
/// d'origine (<c>CSP.CreateCSP(...)</c> puis <c>AddConstraint(...)</c>).
/// </summary>
/// <remarks>Port du noyau CSP d'AIMA (EPIC #7265, pepite B1).</remarks>
public sealed class CspProblem
{
    private readonly List<Variable> _variables;
    private readonly List<IConstraint> _constraints = new();

    private CspProblem(IEnumerable<Variable> variables) => _variables = new List<Variable>(variables);

    /// <summary>Cree un probleme a partir de ses variables.</summary>
    public static CspProblem CreateCsp(params Variable[] variables)
    {
        ArgumentNullException.ThrowIfNull(variables);

        HashSet<Variable> seen = new();
        foreach (Variable variable in variables)
        {
            if (!seen.Add(variable))
            {
                throw new ArgumentException($"Variable dupliquee dans le probleme : {variable.Name}", nameof(variables));
            }
        }

        return new CspProblem(variables);
    }

    /// <summary>Variables du probleme, dans l'ordre de declaration.</summary>
    public IReadOnlyList<Variable> Variables => _variables;

    /// <summary>Contraintes du probleme, dans l'ordre d'ajout.</summary>
    public IReadOnlyList<IConstraint> Constraints => _constraints;

    /// <summary>
    /// Ajoute une contrainte ; toutes les variables de son scope doivent etre
    /// declarees dans le probleme (garde explicite : une variable orpheline
    /// rendrait la recherche silencieusement fausse).
    /// </summary>
    public CspProblem AddConstraint(IConstraint constraint)
    {
        ArgumentNullException.ThrowIfNull(constraint);

        foreach (Variable variable in constraint.Scope)
        {
            if (!_variables.Contains(variable))
            {
                throw new ArgumentException(
                    $"La contrainte '{constraint}' porte sur la variable '{variable.Name}', absente du probleme.",
                    nameof(constraint));
            }
        }

        _constraints.Add(constraint);
        return this;
    }

    /// <summary>Ajoute une contrainte binaire definie par un predicat.</summary>
    public CspProblem AddConstraint(
        Variable left,
        Variable right,
        Func<object?, object?, bool> predicate,
        string? name = null) => AddConstraint(new BinaryConstraint(left, right, predicate, name));

    /// <summary>Contraintes impliquant une variable donnee.</summary>
    public IEnumerable<IConstraint> GetConstraints(Variable variable) =>
        _constraints.Where(constraint => constraint.Scope.Contains(variable));

    /// <summary>Voisins d'une variable, deduits des contraintes.</summary>
    public IEnumerable<Variable> GetNeighbors(Variable variable) =>
        GetConstraints(variable)
            .SelectMany(constraint => constraint.Scope)
            .Where(neighbor => !ReferenceEquals(neighbor, variable))
            .Distinct();

    /// <summary>Contraintes binaires liant deux variables donnees, dans un sens ou dans l'autre.</summary>
    public IEnumerable<BinaryConstraint> GetBinaryConstraints(Variable first, Variable second) =>
        _constraints.OfType<BinaryConstraint>().Where(constraint =>
            (ReferenceEquals(constraint.Left, first) && ReferenceEquals(constraint.Right, second)) ||
            (ReferenceEquals(constraint.Left, second) && ReferenceEquals(constraint.Right, first)));
}
