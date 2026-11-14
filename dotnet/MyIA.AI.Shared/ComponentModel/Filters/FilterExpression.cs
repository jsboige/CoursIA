using System.CodeDom;

namespace MyIA.AI.ComponentModel.Filters;

/// <summary>
/// Compound boolean expression of <see cref="IFilter"/> instances: an ordered list of
/// <see cref="FilterInExpression"/> evaluated left to right, where an <see cref="OperatorFilterExp.And"/>
/// entry that fails settles the expression to false and an <see cref="OperatorFilterExp.Or"/>
/// entry that succeeds settles it to true. Modernized port of Aricie.Shared FilterExpression
/// (EPIC #7265, pépite A3, T1).
/// </summary>
public class FilterExpression : List<FilterInExpression>, IFilter
{
    public FilterExpression()
    {
    }

    public FilterExpression(IFilter left) : this()
    {
        Add(left, OperatorFilterExp.And);
    }

    public FilterExpression(OperatorFilterExp objOperator, params IFilter[] filters) : this()
    {
        foreach (var filter in filters)
        {
            Add(new FilterInExpression(filter, objOperator));
        }
    }

    public FilterExpression(List<FilterInExpression> subFilter) : base(subFilter)
    {
    }

    /// <inheritdoc />
    public bool IsSimpleMatch => TrueForAll(IsSimpleMatchFilter);

    public static bool IsSimpleMatchFilter(FilterInExpression inFilter) => inFilter.Filter.IsSimpleMatch;

    public void Add(IFilter filter, OperatorFilterExp op) => Add(new FilterInExpression(filter, op));

    /// <inheritdoc />
    public virtual bool Match<T>(T content)
    {
        var toReturn = false;
        for (var i = 0; i < Count; i++)
        {
            var inFilter = this[i];
            if (inFilter.OperatorFilterExp == OperatorFilterExp.And)
            {
                if (!inFilter.Filter.Match(content))
                {
                    return false;
                }

                toReturn = true;
            }
            else
            {
                if (inFilter.Filter.Match(content))
                {
                    return true;
                }
            }
        }

        return toReturn;
    }

    /// <inheritdoc />
    /// <remarks>
    /// Port note (measured deviation, see PR body): the VB original inverted its
    /// edge branches — <c>Count = 0</c> indexed <c>this(0)</c> (always out of range) and
    /// <c>Count = 1</c> returned <c>True</c>. The port restores the evident intent:
    /// empty expression => <c>true</c>, single filter => that filter's own expression.
    /// The original's global CodeDom cache (GetGlobal/SetGlobal) is not carried over.
    /// </remarks>
    public virtual CodeExpression GetCodeExpression()
    {
        if (Count > 1)
        {
            var left = this[0].Filter.GetCodeExpression();
            var op = this[1].OperatorFilterExp == OperatorFilterExp.And
                ? CodeBinaryOperatorType.BooleanAnd
                : CodeBinaryOperatorType.BooleanOr;
            var right = new FilterExpression(GetRange(1, Count - 1)).GetCodeExpression();
            return new CodeBinaryOperatorExpression(left, op, right);
        }

        if (Count == 1)
        {
            return this[0].Filter.GetCodeExpression();
        }

        return new CodePrimitiveExpression(true);
    }

    /// <inheritdoc />
    public string GetArgs()
    {
        var toReturn = "fe";
        for (var i = 0; i < Count; i++)
        {
            toReturn += $"-f-{i}-{this[i].OperatorFilterExp}-{this[i].Filter.GetArgs()}";
        }

        return toReturn + "-fe";
    }
}
