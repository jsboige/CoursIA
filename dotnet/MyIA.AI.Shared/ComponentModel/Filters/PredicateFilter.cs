using System.CodeDom;
using System.Reflection;

namespace MyIA.AI.ComponentModel.Filters;

/// <summary>
/// <see cref="IFilter"/> applying a <see cref="Predicate{T}"/> to a property of the content
/// object resolved by reflection. Modernized port of Aricie.Shared PredicateFilter
/// (EPIC #7265, pépite A3, T1).
/// </summary>
/// <typeparam name="T">Type the predicate receives (the property value is cast to it).</typeparam>
public class PredicateFilter<T> : IFilter
{
    public PredicateFilter(IConvertible propName, Predicate<T> objPredicate)
    {
        PropertyName = propName;
        Predicate = objPredicate;
    }

    /// <summary>Name of the content property fed to the predicate.</summary>
    public IConvertible PropertyName { get; set; } = "";

    /// <summary>Predicate applied to the property value.</summary>
    public Predicate<T> Predicate { get; set; } = default!;

    /// <inheritdoc />
    public bool IsSimpleMatch => true;

    protected virtual bool GetSimpleMatch<Y>(Y content)
    {
        PropertyInfo myProperty = ReflectionCache.Properties(typeof(Y))[PropertyName.ToString(null)];
        return Predicate.Invoke((T)myProperty.GetValue(content)!);
    }

    /// <inheritdoc />
    /// <remarks>Port note: the VB guard on <see cref="IsSimpleMatch"/> had a dead else-branch
    /// (the property is constant true); the port calls the simple match directly.</remarks>
    public bool Match<Y>(Y content) => GetSimpleMatch(content);

    /// <inheritdoc />
    /// <remarks>A delegate has no CodeDom representation — the VB original threw
    /// NotImplementedException; the port uses the standard
    /// <see cref="NotSupportedException"/> idiom for an unsupported operation.</remarks>
    public virtual CodeExpression GetCodeExpression()
        => throw new NotSupportedException("No CodeDom expression for predicate filters: a delegate has no CodeDom representation.");

    public virtual string GetTempArgs() => $"f{PropertyName.ToString(null)}-{Predicate}";

    /// <inheritdoc />
    public string GetArgs() => GetTempArgs();
}
