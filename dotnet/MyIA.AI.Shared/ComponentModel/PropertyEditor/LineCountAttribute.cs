namespace MyIA.AI.ComponentModel.PropertyEditor;

/// <summary>Row-count hint for a text editor, with an auto-resize option. Modernized
/// port of Aricie.Shared LineCountAttribute (EPIC #7265, A3 T2a).</summary>
public sealed class LineCountAttribute : Attribute
{
    public LineCountAttribute(int lines) => Lines = lines;

    /// <summary>Number of lines the editor should display.</summary>
    public int Lines { get; }

    /// <summary>Whether the editor auto-resizes to its content.</summary>
    public bool AutoResize { get; set; }
}
