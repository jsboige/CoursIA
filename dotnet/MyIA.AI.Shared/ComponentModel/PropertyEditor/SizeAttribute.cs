namespace MyIA.AI.ComponentModel.PropertyEditor;

/// <summary>Size hint (rows) for the decorated property's editor. Modernized port of
/// Aricie.Shared SizeAttribute (EPIC #7265, A3 T2a).</summary>
[AttributeUsage(AttributeTargets.Property)]
public sealed class SizeAttribute : Attribute
{
    public SizeAttribute(int size) => Size = size;

    /// <summary>Size hint.</summary>
    public int Size { get; }
}
