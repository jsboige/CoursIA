using System;
using System.Collections.Generic;
using System.Linq;

namespace MyIA.AI.Shared.Search.Csp;

/// <summary>
/// Affectation partielle variable -&gt; valeur. Un <c>Assignment</c> est le
/// support mutable de la recherche : le solveur l'augmente puis le defait
/// en remontant l'arbre.
/// </summary>
/// <remarks>Port du noyau CSP d'AIMA (EPIC #7265, pepite B1).</remarks>
public sealed class Assignment
{
    private readonly Dictionary<Variable, object?> _values = new();

    /// <summary>Nombre de variables affectees.</summary>
    public int Count => _values.Count;

    /// <summary>Variables affectees, dans l'ordre d'affectation.</summary>
    public IEnumerable<Variable> Variables => _values.Keys;

    /// <summary>Affecte (ou reaffecte) une variable.</summary>
    public void Add(Variable variable, object? value)
    {
        ArgumentNullException.ThrowIfNull(variable);
        _values[variable] = value;
    }

    /// <summary>Defait l'affectation d'une variable.</summary>
    public void Remove(Variable variable) => _values.Remove(variable);

    /// <summary>Vrai si la variable porte une valeur.</summary>
    public bool Contains(Variable variable) => _values.ContainsKey(variable);

    /// <summary>Lecture d'une valeur ; leve si la variable n'est pas affectee.</summary>
    public object? Get(Variable variable) =>
        _values.TryGetValue(variable, out object? value)
            ? value
            : throw new KeyNotFoundException($"La variable '{variable.Name}' n'est pas affectee.");

    /// <summary>Lecture non leveuse.</summary>
    public bool TryGetValue(Variable variable, out object? value) => _values.TryGetValue(variable, out value);

    /// <summary>Vrai si toutes les variables du probleme portent une valeur.</summary>
    public bool IsComplete(IEnumerable<Variable> variables) => variables.All(Contains);

    /// <summary>Vrai si toutes les contraintes du probleme tiennent pour cette affectation.</summary>
    public bool IsConsistent(IEnumerable<IConstraint> constraints) => constraints.All(c => c.IsSatisfied(this));

    /// <summary>Copie independante.</summary>
    public Assignment Copy()
    {
        Assignment clone = new();
        foreach (KeyValuePair<Variable, object?> entry in _values)
        {
            clone._values[entry.Key] = entry.Value;
        }

        return clone;
    }

    public override string ToString() =>
        string.Join(", ", _values.Select(entry => $"{entry.Key.Name}={entry.Value ?? "null"}"));
}
