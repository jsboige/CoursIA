using System;

namespace MyIA.AI.Shared.Search.Csp;

/// <summary>
/// Variable CSP : un nom et un domaine de valeurs possibles.
/// </summary>
/// <remarks>Port du noyau CSP d'AIMA (EPIC #7265, pepite B1).</remarks>
public sealed class Variable
{
    public Variable(string name, Domain domain)
    {
        if (string.IsNullOrWhiteSpace(name))
        {
            throw new ArgumentException("Le nom d'une variable CSP ne peut pas etre vide.", nameof(name));
        }

        Name = name;
        Domain = domain ?? throw new ArgumentNullException(nameof(domain));
    }

    /// <summary>Nom lisible, utilise dans les traces et les tests.</summary>
    public string Name { get; }

    /// <summary>Domaine initial ; le domaine de travail vit dans le solveur.</summary>
    public Domain Domain { get; }

    public override string ToString() => Name;
}
