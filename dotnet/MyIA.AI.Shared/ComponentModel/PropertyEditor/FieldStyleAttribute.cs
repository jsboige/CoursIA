namespace MyIA.AI.ComponentModel.PropertyEditor;

/// <summary>Widths of the three parts of a rendered property row (field, label, edit
/// control). Modernized port of Aricie.Shared FieldStyleAttribute (EPIC #7265, A3 T2a).</summary>
/// <remarks>Deviation from the VB source: the original converted the three widths to
/// <c>System.Web.UI.WebControls.Unit</c> (CSS-adjacent WebForms type, absent on net9). The
/// port exposes the raw CSS width strings the constructor receives — the renderer applies
/// its own unit semantics. No information is lost: the source only ever wrapped the string
/// in <c>Unit</c> and never read it back as anything else.</remarks>
[AttributeUsage(AttributeTargets.Property)]
public sealed class FieldStyleAttribute : Attribute
{
    private readonly string _width;
    private readonly string _labelWidth;
    private readonly string _editControlWidth;

    public FieldStyleAttribute(string width, string labelWidth, string editControlWidth)
    {
        _width = width;
        _labelWidth = labelWidth;
        _editControlWidth = editControlWidth;
    }

    /// <summary>CSS width of the whole field row.</summary>
    public string Width => _width;

    /// <summary>CSS width of the label part.</summary>
    public string LabelWidth => _labelWidth;

    /// <summary>CSS width of the edit-control part.</summary>
    public string EditControlWidth => _editControlWidth;
}
