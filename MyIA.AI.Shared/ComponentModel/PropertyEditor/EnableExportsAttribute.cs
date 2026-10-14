namespace MyIA.AI.ComponentModel.PropertyEditor;

/// <summary>Enables (or disables) export on the decorated property. Modernized port of
/// Aricie.Shared EnableExportsAttribute (EPIC #7265, A3 T2a).</summary>
public sealed class EnableExportsAttribute : Attribute
{
    public EnableExportsAttribute()
    {
    }

    public EnableExportsAttribute(bool enable) => Enabled = enable;

    public bool Enabled { get; set; }
}
