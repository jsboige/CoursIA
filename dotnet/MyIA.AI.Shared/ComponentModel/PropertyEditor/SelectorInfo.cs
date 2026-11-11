namespace MyIA.AI.ComponentModel.PropertyEditor;

/// <summary>Declarative configuration of a selector editor: which selector control builds the
/// options (by type name, or through the property's own <c>ISelector</c> implementation), which
/// members of the option items feed the text and value fields, whether the selection is
/// exclusive, and the null-item and localization behavior. Modernized port of Aricie.Shared
/// SelectorInfo (EPIC #7265, A3 T2b).</summary>
/// <remarks>
/// <para>Deviation from the VB source: the original's <c>BuildSelector(parentField)</c> method
/// instantiated DNN web controls (<c>SelectorControl</c>, <c>AutoSelectorControl</c>) against a
/// <c>FieldEditorControl</c> parent and threw <c>HttpException</c> on misconfiguration. That
/// method belongs to the WebForms editor layer this tranche does not carry: the port keeps the
/// full declarative surface — everything a renderer needs to build the selector later — and the
/// control-construction itself is deferred to the T3 rendering design-gate (same gesture as the
/// T2a <c>ConditionalVisibleInfo</c> dropping its DNN <c>IEnabled</c> unwrapping).</para>
/// <para>Field defaults measured on the source: <see cref="IsIselector"/> starts
/// <see langword="true"/> (an unconfigured selector falls back to the property's own
/// implementation), <see cref="NullItemText"/> starts <c>"---"</c>.</para>
/// </remarks>
public class SelectorInfo
{
    /// <summary>Whether the selector options come from the edited property's own
    /// <c>ISelector</c> implementation (true) or from the type named by
    /// <see cref="SelectorTypeName"/> (false).</summary>
    public bool IsIselector { get; set; } = true;

    /// <summary>Type name of the selector control providing the options; empty when
    /// <see cref="IsIselector"/> is true.</summary>
    public string? SelectorTypeName { get; set; }

    /// <summary>Member of an option item feeding its display text.</summary>
    public string? DataTextField { get; set; }

    /// <summary>Member of an option item feeding its value.</summary>
    public string? DataValueField { get; set; }

    /// <summary>Whether the selector refuses values outside its options.</summary>
    public bool IsExclusive { get; set; }

    /// <summary>Whether the selector offers an explicit null item.</summary>
    public bool InsertNullItem { get; set; }

    /// <summary>Display text of the null item.</summary>
    public string NullItemText { get; set; } = "---";

    /// <summary>Value of the null item.</summary>
    public string? NullItemValue { get; set; }

    /// <summary>Whether the option texts are localized.</summary>
    public bool LocalizeItems { get; set; }

    /// <summary>Whether the selected text is localized.</summary>
    public bool LocalizeText { get; set; }

    /// <summary>Whether the null item's text is localized.</summary>
    public bool LocalizeNull { get; set; }
}
