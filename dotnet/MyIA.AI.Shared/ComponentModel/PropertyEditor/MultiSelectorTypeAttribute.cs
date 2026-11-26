namespace MyIA.AI.ComponentModel.PropertyEditor;

/// <summary>Selects the multi-selection editor style for a collection property.
/// Modernized port of Aricie.Shared MultiSelectorTypeAttribute (EPIC #7265, A3 T2a).</summary>
public sealed class MultiSelectorTypeAttribute : Attribute
{
    public MultiSelectorTypeAttribute(MultiSelectionType selectionType) => SelectionType = selectionType;

    /// <summary>Selection style of the editor.</summary>
    public MultiSelectionType SelectionType { get; }
}

/// <summary>Multi-selection editor styles (companion enum of
/// <see cref="MultiSelectorTypeAttribute"/>).</summary>
public enum MultiSelectionType
{
    /// <summary>Multiple check-boxes.</summary>
    CheckBoxes,

    /// <summary>Multiple drop-downs.</summary>
    MultipleDropDown,

    /// <summary>Single drop-down.</summary>
    DropDown,

    /// <summary>List box.</summary>
    ListBox
}
