using System.Reflection;

namespace MyIA.AI.ComponentModel.PropertyEditor;

/// <summary>Describes when a member is visible: either the boolean truth of a master
/// property (optionally negated), or the equality of a master property against a set of
/// accepted values — optionally combined with a secondary property/value pair. Modernized
/// port of Aricie.Shared ConditionalVisibleInfo (EPIC #7265, A3 T2a).</summary>
/// <remarks>
/// <para>Measured deviations from the VB source, restored to the evident intent:</para>
/// <list type="number">
/// <item>the seven-argument constructor accepts <c>secondaryPropertyName</c>,
/// <c>secondaryNegate</c> and <c>secondaryValue</c> but the VB body only stores the master
/// value — the three fields, the <see cref="SecondaryPropertyName"/> property and
/// <see cref="MatchSecondary"/> all exist and are read, so the omission left the secondary
/// condition permanently inert. The port stores all three.</item>
/// <item>the default predicate converted the raw value with VB <c>CType(..., Boolean)</c>,
/// which applies a conversion (parsing "True"/"False") rather than a cast; the port uses
/// <see cref="Convert.ToBoolean(object)"/>, which has those semantics.</item>
/// <item>the DNN <c>IEnabled</c> unwrapping is dropped: the type belongs to the WebForms
/// editor layer this tranche does not carry. A caller needing the old behavior passes an
/// explicit <see cref="Predicate{T}"/>.</item>
/// <item><see cref="HasMatchingValue"/> compared through <c>objValue.Equals(value)</c>, which
/// throws on a null entry of the accepted-values array; the port uses null-safe equality.</item>
/// <item>the source <c>XmlIgnore</c> markers are not carried — the A2+ XML round-trip goes
/// through its own surrogates, and the predicate is non-serializable by nature.</item>
/// </list>
/// </remarks>
public class ConditionalVisibleInfo
{
    private readonly object?[]? _matchingValues;
    private readonly bool _masterNegate;
    private readonly object? _secondaryMatchingValue;
    private readonly bool _secondaryNegate;

    public ConditionalVisibleInfo()
    {
    }

    public ConditionalVisibleInfo(string masterPropertyName, bool negate, bool enforcePostBack)
    {
        MasterPropertyName = masterPropertyName;
        _masterNegate = negate;
        MatchValue = DefaultPredicate;
        EnforceAutoPostBack = enforcePostBack;
    }

    public ConditionalVisibleInfo(string masterPropertyName, bool negate, bool enforcePostBack, params object?[] matchingValues)
        : this(masterPropertyName, negate, enforcePostBack)
    {
        _matchingValues = matchingValues;
        MatchValue = HasMatchingValue;
    }

    public ConditionalVisibleInfo(string masterPropertyName, bool negate, bool enforcePostBack, Predicate<object> matchingPredicate)
        : this(masterPropertyName, negate, enforcePostBack)
    {
        MatchValue = matchingPredicate;
    }

    /// <remarks>Port note: see deviation 1 — the three secondary arguments are stored here,
    /// the VB original dropped them.</remarks>
    public ConditionalVisibleInfo(
        bool enforcePostBack,
        string masterPropertyName,
        bool masterNegate,
        object? masterValue,
        string secondaryPropertyName,
        bool secondaryNegate,
        object? secondaryValue)
        : this(masterPropertyName, masterNegate, enforcePostBack)
    {
        _matchingValues = new[] { masterValue };
        MatchValue = HasMatchingValue;
        SecondaryPropertyName = secondaryPropertyName;
        _secondaryMatchingValue = secondaryValue;
        _secondaryNegate = secondaryNegate;
    }

    /// <summary>Name of the property driving visibility.</summary>
    public string? MasterPropertyName { get; }

    /// <summary>Optional name of a secondary property that must also match.</summary>
    public string? SecondaryPropertyName { get; }

    /// <summary>Predicate deciding visibility; null when the instance was built with the
    /// parameterless constructor.</summary>
    public Predicate<object>? MatchValue { get; }

    /// <summary>Whether the editor must post back for the condition to be re-evaluated.</summary>
    public bool EnforceAutoPostBack { get; }

    /// <summary>Evaluates the secondary condition against <paramref name="secondaryValue"/>.</summary>
    public bool MatchSecondary(object? secondaryValue)
    {
        var toReturn = secondaryValue is null
            ? _secondaryMatchingValue is null
            : secondaryValue.Equals(_secondaryMatchingValue);
        return toReturn ^ _secondaryNegate;
    }

    private bool DefaultPredicate(object value)
    {
        object? evaluated = value;
        if (evaluated is not null && evaluated.ToString() == string.Empty)
        {
            evaluated = null;
        }

        var baseResult = Convert.ToBoolean(evaluated);
        return baseResult ^ _masterNegate;
    }

    private bool HasMatchingValue(object? value)
    {
        if (_matchingValues is not null && _matchingValues.Any(objValue =>
                Equals(objValue, value)
                || (value is not null
                    && value.GetType().IsEnum
                    && Convert.ToInt32(objValue) != 0
                    && value.GetType().IsDefined(typeof(FlagsAttribute), false)
                    && (Convert.ToInt32(value) & Convert.ToInt32(objValue)) == Convert.ToInt32(objValue))))
        {
            return !_masterNegate;
        }

        return _masterNegate;
    }

    /// <summary>Visibility conditions declared on a member (empty when it declares none).</summary>
    public static List<ConditionalVisibleInfo> FromMember(MemberInfo member)
    {
        var toReturn = new List<ConditionalVisibleInfo>();
        foreach (var condAttribute in member.GetCustomAttributes(true).OfType<ConditionalVisibleAttribute>())
        {
            toReturn.Add(condAttribute.Value);
        }

        return toReturn;
    }
}
