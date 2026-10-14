namespace MyIA.AI.ComponentModel.PropertyEditor;

/// <summary>Declares that a property edits through a selector (drop-down style) editor and
/// configures it through a <see cref="SelectorInfo"/>: option source (a selector type, or the
/// property's own <c>ISelector</c> implementation), text/value fields, exclusivity, null item
/// and localization. Modernized port of Aricie.Shared SelectorAttribute
/// (EPIC #7265, A3 T2b).</summary>
/// <remarks>
/// <para>Measured defect of the VB source, restored to the evident intent: the constructor
/// taking <c>localizeText</c> assigned <c>Me._SelectorInfo.LocalizeText = True</c> — the hard-coded
/// literal instead of the parameter — so passing <see langword="false"/> silently behaved as
/// <see langword="true"/>. The port assigns the parameter.</para>
/// <para>Deviation on type names: the <see cref="SelectorAttribute(Type, string, string, bool,
/// bool, string, string, bool, bool)"/> constructor resolved the selector type through
/// Aricie's <c>ReflectionHelper.GetSafeTypeName</c>, a legacy-tolerance shim (null guards,
/// generic-parameter names, .NET 2.0/4.0 <c>System</c> assembly version fallbacks, resolution
/// cache) for GAC type-name churn that does not exist on net9. The port stores
/// <see cref="Type.AssemblyQualifiedName"/>, the round-trippable name on a single-runtime
/// target; a null argument yields the empty string, as the shim did.</para>
/// </remarks>
[AttributeUsage(AttributeTargets.Property)]
public class SelectorAttribute : Attribute
{
    public SelectorAttribute()
    {
    }

    public SelectorAttribute(string selectorTypeName, string dataTextField, string dataValueField, bool exclusive, bool addNullItem)
    {
        SelectorInfo.SelectorTypeName = selectorTypeName;
        SelectorInfo.DataTextField = dataTextField;
        SelectorInfo.DataValueField = dataValueField;
        SelectorInfo.IsExclusive = exclusive;
        SelectorInfo.InsertNullItem = addNullItem;
    }

    public SelectorAttribute(
        string selectorTypeName,
        string dataTextField,
        string dataValueField,
        bool exclusive,
        bool addNullItem,
        string nullItemName,
        string nullItemValue,
        bool localizeItems,
        bool localizeNull)
        : this(selectorTypeName, dataTextField, dataValueField, exclusive, addNullItem)
    {
        SelectorInfo.NullItemText = nullItemName;
        SelectorInfo.NullItemValue = nullItemValue;
        SelectorInfo.LocalizeItems = localizeItems;
        SelectorInfo.LocalizeNull = localizeNull;
    }

    public SelectorAttribute(
        Type selectorType,
        string dataTextField,
        string dataValueField,
        bool exclusive,
        bool addNullItem,
        string nullItemName,
        string nullItemValue,
        bool localizeItems,
        bool localizeNull)
        : this(
            selectorType?.AssemblyQualifiedName ?? string.Empty,
            dataTextField,
            dataValueField,
            exclusive,
            addNullItem,
            nullItemName,
            nullItemValue,
            localizeItems,
            localizeNull)
    {
    }

    public SelectorAttribute(
        string dataTextField,
        string dataValueField,
        bool exclusive,
        bool addNullItem,
        string nullItemName,
        string nullItemValue,
        bool localizeItems,
        bool localizeNull)
        : this(string.Empty, dataTextField, dataValueField, exclusive, addNullItem, nullItemName, nullItemValue, localizeItems, localizeNull)
    {
        // Explicit re-assertion of the SelectorInfo default, as in the VB source: the
        // dataField-based constructors select through the property's own ISelector.
        SelectorInfo.IsIselector = true;
    }

    /// <remarks>Port note: the VB source assigned a hard-coded <see langword="true"/> where
    /// this constructor receives <paramref name="localizeText"/> — see the class remarks.</remarks>
    public SelectorAttribute(
        string dataTextField,
        string dataValueField,
        bool exclusive,
        bool addNullItem,
        string nullItemName,
        string nullItemValue,
        bool localizeItems,
        bool localizeNull,
        bool localizeText)
        : this(dataTextField, dataValueField, exclusive, addNullItem, nullItemName, nullItemValue, localizeItems, localizeNull)
    {
        SelectorInfo.LocalizeText = localizeText;
    }

    /// <summary>Configuration of the selector editor.</summary>
    public SelectorInfo SelectorInfo { get; set; } = new();
}

/// <summary>Selector fed by a provider collection: options are the providers of the edited
/// property's provider model, keyed by name. Modernized port of Aricie.Shared
/// ProvidersSelectorAttribute (EPIC #7265, A3 T2b).</summary>
/// <remarks>The VB source chained to the eight-argument base constructor with
/// <see langword="false"/> for both localization flags, empty null-item text and value, and
/// <see cref="SelectorInfo.IsIselector"/> left at its <see langword="true"/> default; the port
/// reproduces that state exactly.</remarks>
[AttributeUsage(AttributeTargets.Property)]
public sealed class ProvidersSelectorAttribute : SelectorAttribute
{
    public ProvidersSelectorAttribute(string nameFieldName, string valueFieldName)
        : base(nameFieldName, valueFieldName, false, false, string.Empty, string.Empty, false, false)
    {
    }

    public ProvidersSelectorAttribute(string nameFieldName)
        : this(nameFieldName, nameFieldName)
    {
    }

    public ProvidersSelectorAttribute()
        : this("Name")
    {
    }
}
