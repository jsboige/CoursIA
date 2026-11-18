namespace MyIA.AI.ComponentModel.Filters;

/// <summary>
/// A filter paired with the operator combining it with the previous entry of a
/// <see cref="FilterExpression"/>.
/// </summary>
public readonly struct FilterInExpression
{
    /// <summary>Filter to apply, combined with <see cref="OperatorFilterExp"/>.</summary>
    public FilterInExpression(IFilter filter, OperatorFilterExp op)
    {
        Filter = filter;
        OperatorFilterExp = op;
    }

    /// <summary>The wrapped filter.</summary>
    public IFilter Filter { get; }

    /// <summary>Operator combining this filter with the rest of the expression.</summary>
    public OperatorFilterExp OperatorFilterExp { get; }
}
