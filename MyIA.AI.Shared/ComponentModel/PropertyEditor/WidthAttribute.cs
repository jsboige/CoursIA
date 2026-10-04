namespace MyIA.AI.ComponentModel.PropertyEditor;

/// <summary>Width hint for the decorated property's editor. Modernized port of
/// Aricie.Shared WidthAttribute (EPIC #7265, A3 T2a).</summary>
[AttributeUsage(AttributeTargets.Property)]
public sealed class WidthAttribute : Attribute
{
    public WidthAttribute(int width) => Width = width;

    /// <summary>Width hint.</summary>
    public int Width { get; }
}
