namespace MyIA.AI.ComponentModel.PropertyEditor;

/// <summary>Marks the decorated property as view-only (never editable).
/// Modernized port of Aricie.Shared ViewOnlyAttribute (EPIC #7265, A3 T2b).</summary>
[AttributeUsage(AttributeTargets.Property)]
public sealed class ViewOnlyAttribute : SingleEditorModeAttribute
{
    public ViewOnlyAttribute()
        : base(PropertyEditorMode.View)
    {
    }
}
