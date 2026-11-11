namespace MyIA.AI.ComponentModel.PropertyEditor;

/// <summary>Points a property's editor at an external control (user control path).
/// Modernized port of Aricie.Shared UserControlAttribute (EPIC #7265, A3 T2a).</summary>
[AttributeUsage(AttributeTargets.Property)]
public sealed class UserControlAttribute : Attribute
{
    public UserControlAttribute(string controlPath) => ControlPath = controlPath;

    /// <summary>Path of the control used as editor.</summary>
    public string ControlPath { get; }
}
