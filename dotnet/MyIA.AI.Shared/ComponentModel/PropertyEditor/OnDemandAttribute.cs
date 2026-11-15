namespace MyIA.AI.ComponentModel.PropertyEditor;

/// <summary>Marks a property to be loaded on demand (lazy), optionally off. Modernized
/// port of Aricie.Shared OnDemandAttribute (EPIC #7265, A3 T2a).</summary>
[AttributeUsage(AttributeTargets.Property)]
public sealed class OnDemandAttribute : Attribute
{
    public OnDemandAttribute()
    {
    }

    public OnDemandAttribute(bool onDemand) => Enabled = onDemand;

    public bool Enabled { get; set; }
}
