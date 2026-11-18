using System.CodeDom;

namespace MyIA.AI.ComponentModel.Filters;

/// <summary>
/// Reflection-based <see cref="IFilter"/> comparing a property of the content object
/// against a value with a <see cref="CodeBinaryOperatorType"/> operator. Modernized port
/// of Aricie.Shared SimpleFilter (EPIC #7265, pépite A3, T1).
/// </summary>
/// <typeparam name="T">Value type compared through <see cref="IComparable"/>.</typeparam>
/// <remarks>
/// Measured deviations from the VB source (see PR body): (1) the Workflow Foundation
/// <c>Evaluate</c> path (<c>System.Workflow.Activities.Rules</c>) is dropped — the
/// namespace does not exist on net9 and the method was unreachable from
/// <see cref="Match{Y}"/>; (2) the global CodeDom expression cache and its in-place
/// mutation of the cached <see cref="CodePrimitiveExpression"/> are dropped — the cached
/// Right operand was shared mutable state (two filters with same property+operator but
/// different values corrupted each other); (3) the fallback throw for an unsupported
/// operator is <see cref="NotSupportedException"/> instead of NotImplementedException.
/// </remarks>
public class SimpleFilter<T> : IFilter where T : IComparable
{
    public SimpleFilter(IConvertible propName, CodeBinaryOperatorType op, T objValue)
    {
        PropertyName = propName;
        Operator = op;
        Value = objValue;
    }

    /// <summary>Name of the content property to compare.</summary>
    public IConvertible PropertyName { get; set; } = "";

    /// <summary>Comparison operator (CodeDom binary operator).</summary>
    public CodeBinaryOperatorType Operator { get; set; } = CodeBinaryOperatorType.ValueEquality;

    /// <summary>Value the property is compared against.</summary>
    public T Value { get; set; } = default!;

    /// <inheritdoc />
    public bool IsSimpleMatch => true;

    protected virtual bool GetSimpleMatch<Y>(Y content)
    {
        var myProperty = ReflectionCache.Properties(typeof(Y))[PropertyName.ToString(null)];
        var comparable = (T)myProperty.GetValue(content)!;
        return Operator switch
        {
            CodeBinaryOperatorType.ValueEquality => comparable.CompareTo(Value) == 0,
            CodeBinaryOperatorType.GreaterThan => comparable.CompareTo(Value) > 0,
            CodeBinaryOperatorType.GreaterThanOrEqual => comparable.CompareTo(Value) >= 0,
            CodeBinaryOperatorType.LessThan => comparable.CompareTo(Value) < 0,
            CodeBinaryOperatorType.LessThanOrEqual => comparable.CompareTo(Value) <= 0,
            CodeBinaryOperatorType.IdentityEquality => comparable.Equals(Value),
            _ => throw new NotSupportedException(
                $"Operator {Operator} is not supported by {nameof(SimpleFilter<T>)}"),
        };
    }

    /// <inheritdoc />
    public bool Match<Y>(Y content) => GetSimpleMatch(content);

    /// <inheritdoc />
    public virtual CodeExpression GetCodeExpression()
    {
        var primCodeDomExp = new CodePrimitiveExpression(Value);
        var thisCodeDomExp = new CodeThisReferenceExpression();
        var propCodeDomExp = new CodePropertyReferenceExpression(thisCodeDomExp, PropertyName.ToString(null));
        return new CodeBinaryOperatorExpression(propCodeDomExp, Operator, primCodeDomExp);
    }

    public virtual string GetTempArgs() => $"f{PropertyName.ToString(null)}-{Operator}";

    /// <inheritdoc />
    public string GetArgs() => $"{GetTempArgs()}-{Value}";
}
