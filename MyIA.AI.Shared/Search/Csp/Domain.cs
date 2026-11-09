using System;
using System.Collections.Generic;

namespace MyIA.AI.Shared.Search.Csp;

/// <summary>
/// Domaine d'une variable CSP : ensemble fini de valeurs, sans doublon.
/// L'ordre d'insertion est conserve, ce qui rend la recherche deterministe :
/// deux executions du meme probleme rendent la meme solution.
/// </summary>
/// <remarks>
/// Port du noyau CSP d'AIMA (<c>aima.core.search.csp.Domain</c>), recupere du
/// patrimoine Aricie (EPIC #7265, pepite B1). La version d'origine etait
/// consommee a travers un wrapper DNN + IKVM non portable ; ce type est la
/// version C# nue, sans dependance DNN ni Java.
/// </remarks>
public sealed class Domain
{
    private readonly List<object?> _values;

    /// <summary>Construit un domaine en eliminant les doublons, ordre d'entree conserve.</summary>
    public Domain(IEnumerable<object?> values)
    {
        ArgumentNullException.ThrowIfNull(values);

        _values = new List<object?>();
        foreach (object? value in values)
        {
            if (!_values.Contains(value))
            {
                _values.Add(value);
            }
        }
    }

    private Domain(List<object?> values) => _values = values;

    /// <summary>Fabrique courte : <c>Domain.Of("rouge", "vert")</c>.</summary>
    public static Domain Of(params object?[] values) => new(values);

    /// <summary>Nombre de valeurs restantes.</summary>
    public int Size => _values.Count;

    /// <summary>Vrai quand le domaine est vide : la branche courante est un echec.</summary>
    public bool IsEmpty => _values.Count == 0;

    /// <summary>Valeurs du domaine, dans l'ordre d'insertion.</summary>
    public IReadOnlyList<object?> Values => _values;

    /// <summary>Appartenance d'une valeur au domaine.</summary>
    public bool Contains(object? value) => _values.Contains(value);

    /// <summary>Retire une valeur ; rend <c>true</c> si elle etait presente.</summary>
    public bool Remove(object? value) => _values.Remove(value);

    /// <summary>Copie independante : la propagation de contraintes ne mute jamais le domaine d'origine.</summary>
    public Domain Copy() => new(new List<object?>(_values));

    public override string ToString() => "{" + string.Join(", ", _values) + "}";
}
