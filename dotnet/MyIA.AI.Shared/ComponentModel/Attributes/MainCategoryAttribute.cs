namespace MyIA.AI.ComponentModel.Attributes;

/// <summary>
/// Decorates a type with a primary category used for grouping and reflection-driven
/// introspection. Modernized port of <c>Aricie.Shared</c>'s
/// <c>MainCategoryAttribute</c> (EPIC #7265, ancre A1).
/// </summary>
/// <remarks>
/// The category name is what a <see cref="MyIA.AI.ComponentModel.Providers.ReflectedProviderContainer"/>
/// groups types by: decorating a class with <c>[MainCategory("Payment")]</c> makes it
/// discoverable as <c>provider["Payment"]</c> without any registration call. This is the
/// metadata-driven decoration foundation (decoration -> introspection) that the rest of
/// the Aricie.Shared socle (serialization, object explorer) builds upon.
/// </remarks>
[AttributeUsage(AttributeTargets.Class | AttributeTargets.Interface | AttributeTargets.Struct,
    AllowMultiple = false, Inherited = true)]
public sealed class MainCategoryAttribute : Attribute
{
    /// <summary>Category name. Drives grouping in <c>ReflectedProviderContainer</c>.</summary>
    public string Name { get; }

    /// <summary>Display/grouping order inside the category (lower sorts first). Default 0.</summary>
    public int Order { get; set; }

    public MainCategoryAttribute(string name)
    {
        if (string.IsNullOrWhiteSpace(name))
        {
            throw new ArgumentException(
                "Main category name cannot be null, empty, or whitespace.", nameof(name));
        }

        Name = name;
    }
}
