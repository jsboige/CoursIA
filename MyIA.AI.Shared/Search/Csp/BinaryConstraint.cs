using System;
using System.Collections.Generic;

namespace MyIA.AI.Shared.Search.Csp;

/// <summary>
/// Contrainte binaire generique : deux variables et un predicat.
/// C'est la brique dont les problemes de coloration, de n-dames et de
/// planification se composent.
/// </summary>
/// <remarks>
/// Port du noyau CSP d'AIMA (EPIC #7265, pepite B1). Le predicat est oriente
/// (<see cref="Left"/> puis <see cref="Right"/>) : une contrainte asymetrique
/// comme <c>Left &lt; Right</c> reste donc exprimable, et la propagation de
/// contraintes respecte cette orientation.
/// </remarks>
public sealed class BinaryConstraint : IConstraint
{
    private readonly Func<object?, object?, bool> _predicate;

    public BinaryConstraint(Variable left, Variable right, Func<object?, object?, bool> predicate, string? name = null)
    {
        Left = left ?? throw new ArgumentNullException(nameof(left));
        Right = right ?? throw new ArgumentNullException(nameof(right));
        _predicate = predicate ?? throw new ArgumentNullException(nameof(predicate));
        Name = name ?? $"{left.Name}-{right.Name}";
        Scope = new List<Variable> { left, right }.AsReadOnly();
    }

    /// <summary>Nom de la contrainte, utilise dans les traces.</summary>
    public string Name { get; }

    /// <summary>Premiere variable du predicat.</summary>
    public Variable Left { get; }

    /// <summary>Seconde variable du predicat.</summary>
    public Variable Right { get; }

    public IReadOnlyList<Variable> Scope { get; }

    public bool IsSatisfied(Assignment assignment)
    {
        ArgumentNullException.ThrowIfNull(assignment);

        bool hasLeft = assignment.TryGetValue(Left, out object? leftValue);
        bool hasRight = assignment.TryGetValue(Right, out object? rightValue);
        if (!hasLeft || !hasRight)
        {
            return true;
        }

        return _predicate(leftValue, rightValue);
    }

    /// <summary>
    /// Test du predicat sur un couple de valeurs, dans l'ordre
    /// (<paramref name="leftValue"/>, <paramref name="rightValue"/>).
    /// Sert a la propagation de contraintes, qui raisonne sur les domaines
    /// et non sur une affectation.
    /// </summary>
    public bool IsSatisfiedByValues(object? leftValue, object? rightValue) => _predicate(leftValue, rightValue);

    public override string ToString() => Name;
}

/// <summary>Fabriques des contraintes binaires usuelles.</summary>
public static class Constraints
{
    /// <summary>Contrainte de difference : les deux variables ne peuvent pas porter la meme valeur.</summary>
    public static BinaryConstraint NotEqual(Variable left, Variable right) =>
        new(left, right, (x, y) => !Equals(x, y), $"{left.Name}!={right.Name}");

    /// <summary>Contrainte d'egalite.</summary>
    public static BinaryConstraint Equal(Variable left, Variable right) =>
        new(left, right, (x, y) => Equals(x, y), $"{left.Name}={right.Name}");

    /// <summary>Contrainte binaire quelconque, sur le predicat fourni.</summary>
    public static BinaryConstraint Binary(
        Variable left,
        Variable right,
        Func<object?, object?, bool> predicate,
        string? name = null) => new(left, right, predicate, name);
}
