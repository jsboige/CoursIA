namespace MyIA.AI.ComponentModel.PropertyEditor;

/// <summary>Restricts the decorated property to a single editor mode (edit or view).
/// Modernized port of Aricie.Shared SingleEditorModeAttribute (EPIC #7265, A3 T2b).</summary>
/// <remarks>Deviation from the VB source: the original typed <paramref name="editMode"/> with
/// <c>DotNetNuke.UI.WebControls.PropertyEditorMode</c>, which does not exist on net9. The port
/// defines the renderer-agnostic <see cref="PropertyEditorMode"/> enum in this namespace,
/// carrying the two values the DNN enum exposed (same gesture as the T2a
/// <c>OrientationAttribute</c> for its WebForms enum).</remarks>
[AttributeUsage(AttributeTargets.Property)]
public class SingleEditorModeAttribute : Attribute
{
    public SingleEditorModeAttribute()
    {
    }

    public SingleEditorModeAttribute(PropertyEditorMode editMode) => EditorMode = editMode;

    /// <summary>The only mode in which the decorated property is editable.</summary>
    public PropertyEditorMode EditorMode { get; set; }
}

/// <summary>Editing mode of a property editor (renderer-agnostic replacement for
/// <c>DotNetNuke.UI.WebControls.PropertyEditorMode</c>).</summary>
public enum PropertyEditorMode
{
    /// <summary>The property can be edited.</summary>
    Edit,

    /// <summary>The property is read-only display.</summary>
    View
}
