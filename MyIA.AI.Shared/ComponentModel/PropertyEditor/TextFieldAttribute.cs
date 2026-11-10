namespace MyIA.AI.ComponentModel.PropertyEditor;

/// <summary>Names the display-text property of a bound item. Modernized port of
/// Aricie.Shared TextFieldAttribute (EPIC #7265, A3 T2a).</summary>
[AttributeUsage(AttributeTargets.Property)]
public sealed class TextFieldAttribute : Attribute
{
    public TextFieldAttribute(string textField) => TextField = textField;

    /// <summary>Name of the property providing display text.</summary>
    public string TextField { get; }
}
