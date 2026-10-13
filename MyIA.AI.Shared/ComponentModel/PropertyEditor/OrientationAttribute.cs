namespace MyIA.AI.ComponentModel.PropertyEditor;

/// <summary>Layout orientation requested for the decorated property's editor. Modernized
/// port of Aricie.Shared OrientationAttribute (EPIC #7265, A3 T2a).</summary>
/// <remarks>Deviation from the VB source: the original typed both the constructor and the
/// property as <c>System.Web.UI.WebControls.Orientation</c>, which does not exist on net9.
/// The port defines a renderer-agnostic <see cref="Orientation"/> enum in this namespace
/// carrying the two values the WebForms enum exposed.</remarks>
public sealed class OrientationAttribute : Attribute
{
    public OrientationAttribute(Orientation orientation) => Orientation = orientation;

    /// <summary>Requested orientation.</summary>
    public Orientation Orientation { get; }
}

/// <summary>Layout orientation of an editor (renderer-agnostic replacement for
/// <c>System.Web.UI.WebControls.Orientation</c>).</summary>
public enum Orientation
{
    /// <summary>Horizontal layout.</summary>
    Horizontal,

    /// <summary>Vertical layout.</summary>
    Vertical
}
