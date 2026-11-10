namespace MyIA.AI.ComponentModel.PropertyEditor;

/// <summary>Declares the tab/section/column placement of the decorated member. Modernized
/// port of Aricie.Shared ExtendedCategoryAttribute (EPIC #7265, A3 T2a).</summary>
/// <remarks>The VB source carries no <see cref="AttributeUsageAttribute"/> (C# default:
/// <see cref="AttributeTargets.All"/>); the port keeps that default rather than narrowing
/// it to properties, so a member method can still be placed.</remarks>
public class ExtendedCategoryAttribute : Attribute
{
    public ExtendedCategoryAttribute(string tabName) => ExtendedCategory = new ExtendedCategory(tabName);

    public ExtendedCategoryAttribute(string sectionName, int column)
        => ExtendedCategory = new ExtendedCategory(sectionName, column);

    public ExtendedCategoryAttribute(string tabName, string sectionName)
        => ExtendedCategory = new ExtendedCategory(tabName, sectionName);

    public ExtendedCategoryAttribute(string tabName, string sectionName, int column)
        => ExtendedCategory = new ExtendedCategory(tabName, sectionName, column);

    /// <summary>Category descriptor carried by the attribute.</summary>
    public ExtendedCategory ExtendedCategory { get; set; }
}
