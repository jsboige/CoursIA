namespace MyIA.AI.ComponentModel.PropertyEditor;

/// <summary>Marks the decorated property as editable only (hidden in view mode).
/// Modernized port of Aricie.Shared EditOnlyAttribute (EPIC #7265, A3 T2b).</summary>
[AttributeUsage(AttributeTargets.Property)]
public sealed class EditOnlyAttribute : SingleEditorModeAttribute
{
    public EditOnlyAttribute()
        : base(PropertyEditorMode.Edit)
    {
    }
}
