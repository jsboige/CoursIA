namespace MyIA.AI.ComponentModel.Filters;

/// <summary>
/// Boolean combination operator between filters inside a <see cref="FilterExpression"/>.
/// </summary>
public enum OperatorFilterExp
{
    /// <summary>Logical OR.</summary>
    Or,

    /// <summary>Logical AND.</summary>
    And
}
