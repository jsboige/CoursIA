namespace MyIA.AI.ComponentModel.PropertyEditor;

/// <summary>Base path for a path-editing property. Modernized port of Aricie.Shared
/// PathAttribute (EPIC #7265, A3 T2a).</summary>
[AttributeUsage(AttributeTargets.Property)]
public sealed class PathAttribute : Attribute
{
    public PathAttribute(string path) => Path = path;

    /// <summary>Base path.</summary>
    public string Path { get; } = string.Empty;
}
