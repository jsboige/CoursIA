namespace MyIA.AI.ComponentModel.PropertyEditor;

/// <summary>Declares the condition under which the decorated member is visible. Repeatable.
/// Modernized port of Aricie.Shared ConditionalVisibleAttribute (EPIC #7265, A3 T2a).</summary>
[AttributeUsage(AttributeTargets.Property | AttributeTargets.Method, AllowMultiple = true)]
public sealed class ConditionalVisibleAttribute : Attribute
{
    public ConditionalVisibleAttribute(string masterPropertyName)
        => Value = new ConditionalVisibleInfo(masterPropertyName, false, true);

    public ConditionalVisibleAttribute(string masterPropertyName, bool negate)
        => Value = new ConditionalVisibleInfo(masterPropertyName, negate, true);

    public ConditionalVisibleAttribute(string masterPropertyName, bool negate, bool enforcePostBack)
        => Value = new ConditionalVisibleInfo(masterPropertyName, negate, enforcePostBack);

    public ConditionalVisibleAttribute(string masterPropertyName, bool negate, bool enforcePostBack, params object?[] matchingValues)
        => Value = new ConditionalVisibleInfo(masterPropertyName, negate, enforcePostBack, matchingValues);

    public ConditionalVisibleAttribute(string masterPropertyName, bool negate, bool enforcePostBack, Predicate<object> matchingPredicate)
        => Value = new ConditionalVisibleInfo(masterPropertyName, negate, enforcePostBack, matchingPredicate);

    public ConditionalVisibleAttribute(
        bool enforcePostBack,
        string masterPropertyName,
        bool masterNegate,
        object? masterValue,
        string secondaryPropertyName,
        bool secondaryNegate,
        object? secondaryValue)
        => Value = new ConditionalVisibleInfo(
            enforcePostBack, masterPropertyName, masterNegate, masterValue, secondaryPropertyName, secondaryNegate, secondaryValue);

    /// <summary>Visibility condition carried by the attribute.</summary>
    public ConditionalVisibleInfo Value { get; set; }
}
