namespace MyIA.AI.ComponentModel.PropertyEditor;

/// <summary>Restricts a file-editing property to a comma-separated list of extensions.
/// Modernized port of Aricie.Shared FileExtensionsAttribute (EPIC #7265, A3 T2a).</summary>
public sealed class FileExtensionsAttribute : Attribute
{
    public FileExtensionsAttribute(string extensions) => Extensions = extensions;

    /// <summary>Allowed extensions, comma-separated.</summary>
    public string Extensions { get; }
}
