using System.CodeDom;
using System.Collections;

namespace MyIA.AI.ComponentModel.Filters;

/// <summary>How a <see cref="ListFilter{T}"/> aggregates its inner filter over a list property.</summary>
public enum ScopeOperator
{
    /// <summary>At least one element matches.</summary>
    Any,

    /// <summary>All elements match.</summary>
    All
}

/// <summary>
/// <see cref="IFilter"/> applying an inner filter to each element of a list property of the
/// content object, aggregated with a <see cref="ScopeOperator"/>. Modernized port of
/// Aricie.Shared ListFilter (EPIC #7265, pépite A3, T1).
/// </summary>
/// <typeparam name="T">Element type of the list property.</typeparam>
/// <remarks>
/// Measured deviations from the VB source (see PR body): the original read the list
/// property from the filter itself (<c>GetValue(Me)</c>) instead of the content object, and
/// matched the inner filter against the content object instead of each list element — both
/// restored to the evident intent here. The sentinel loop is rewritten as LINQ
/// All/Any (same observable semantics); the empty-list case is fixed so that an empty list
/// satisfies <see cref="ScopeOperator.All"/> (vacuous truth) instead of returning the VB
/// default false.
/// </remarks>
public class ListFilter<T> : IFilter
{
    public ListFilter(IConvertible propName, IFilter innerFilter, ScopeOperator scope)
    {
        PropertyName = propName;
        Scope = scope;
        InnerFilter = innerFilter;
    }

    /// <summary>Name of the list property on the content object.</summary>
    public IConvertible PropertyName { get; set; } = "";

    /// <summary>Aggregation over the list elements.</summary>
    public ScopeOperator Scope { get; set; }

    /// <summary>Filter applied to each element.</summary>
    public IFilter InnerFilter { get; set; } = default!;

    /// <inheritdoc />
    public bool IsSimpleMatch => true;

    /// <inheritdoc />
    public bool Match<T1>(T1 content) => GetSimpleMatch(content);

    protected bool GetSimpleMatch<Y>(Y content)
    {
        var myProperty = ReflectionCache.Properties(typeof(Y))[PropertyName.ToString(null)];
        var innerList = (IEnumerable)myProperty.GetValue(content)!;
        // Iterate with the element type T so the inner filter resolves properties on
        // typeof(T) — the VB original iterated As T (matching on the runtime element type,
        // not the static list type).
        return Scope == ScopeOperator.All
            ? innerList.Cast<T>().All(e => InnerFilter.Match(e))
            : innerList.Cast<T>().Any(e => InnerFilter.Match(e));
    }

    /// <inheritdoc />
    public CodeExpression GetCodeExpression()
        => throw new NotSupportedException(
            "scope \"All\" is not supported in complex expressions with list filters nor complex inner filters");

    /// <inheritdoc />
    public string GetArgs() => $"f{Scope}-{InnerFilter.GetArgs()}";
}
