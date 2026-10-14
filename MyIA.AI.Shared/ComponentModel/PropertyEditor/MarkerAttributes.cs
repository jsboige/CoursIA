namespace MyIA.AI.ComponentModel.PropertyEditor;

/// <summary>Marks a property for auto-erase behavior in the editor. Marker attribute,
/// no payload. Modernized port of Aricie.Shared AutoEraseAttribute (EPIC #7265, A3 T2a).</summary>
[AttributeUsage(AttributeTargets.Property)]
public sealed class AutoEraseAttribute : Attribute { }

/// <summary>Marks a property to trigger a post-back on change. Marker attribute, no
/// payload. Modernized port of Aricie.Shared AutoPostBackAttribute (EPIC #7265, A3 T2a).</summary>
[AttributeUsage(AttributeTargets.Property)]
public sealed class AutoPostBackAttribute : Attribute { }

/// <summary>Opts a property out of the flag-style rendering. Marker attribute, no
/// payload. Modernized port of Aricie.Shared NoFlagAttribute (EPIC #7265, A3 T2a).</summary>
[AttributeUsage(AttributeTargets.Property)]
public sealed class NoFlagAttribute : Attribute { }

/// <summary>Marks a string property to render as a password field. Marker attribute, no
/// payload. Modernized port of Aricie.Shared PasswordModeAttribute (EPIC #7265, A3 T2a).</summary>
[AttributeUsage(AttributeTargets.Property)]
public sealed class PasswordModeAttribute : Attribute { }
