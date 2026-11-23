using System.Collections.Generic;
using System.Reflection;

namespace MyIA.AI.ComponentModel.Providers;

/// <summary>
/// Convention-driven provider: discovers types across assemblies by a caller-supplied
/// convention function rather than by decoration. This is the third strategy of the
/// <c>Aricie.Shared</c> provider hierarchy (EPIC #7265, ancre A1+): where
/// <see cref="ReflectedProviderContainer"/> needs <c>[MainCategory]</c> and
/// <see cref="SimpleProviderContainer"/> needs explicit registration, this container
/// categorizes from the type's own shape — namespace segment, name suffix, or any rule
/// expressible as <c>Func&lt;Type, string?&gt;</c>. A convention returning <c>null</c>
/// excludes the type. Marker-interface buckets are derived from the discovered types,
/// keeping the read surface uniform across the three strategies.
/// </summary>
/// <remarks>
/// Typical conventions: the last segment of the namespace
/// (<c>t.Namespace?.Split('.').LastOrDefault()</c>), a name suffix (<c>t.Name.EndsWith("Gateway") ? "Payment" : null</c>),
/// or an attribute other than <c>MainCategory</c>. The convention is opaque to the
/// container: it only cares that a non-null string assigns the type to a category.
/// </remarks>
public sealed class AutoProviderContainer : IProviderContainer
{
    private readonly ProviderModel _model;

    private AutoProviderContainer(ProviderModel model) => _model = model;

    /// <summary>
    /// Scans the assembly that declares <typeparamref name="TMarker"/>, categorizing each
    /// public type via <paramref name="categoryByConvention"/>.
    /// </summary>
    public static AutoProviderContainer FromAssembly<TMarker>(Func<Type, string?> categoryByConvention)
        => FromAssemblies(categoryByConvention, typeof(TMarker).Assembly);

    /// <summary>
    /// Scans <paramref name="assemblies"/>, categorizing each public type via
    /// <paramref name="categoryByConvention"/> (null return = excluded).
    /// </summary>
    public static AutoProviderContainer FromAssemblies(
        Func<Type, string?> categoryByConvention,
        params Assembly[] assemblies)
        => FromTypes(ProviderModel.GatherTypes(assemblies), categoryByConvention);

    /// <summary>Builds a container from an explicit type set (test seam + controlled scope).</summary>
    public static AutoProviderContainer FromTypes(
        IEnumerable<Type> types,
        Func<Type, string?> categoryByConvention)
    {
        ArgumentNullException.ThrowIfNull(categoryByConvention);

        var model = ProviderModel.Build(
            types,
            type => categoryByConvention(type) is { } category && !string.IsNullOrWhiteSpace(category)
                ? new[] { category }
                : Array.Empty<string>());

        return new AutoProviderContainer(model);
    }

    /// <summary>Categories assigned by the convention, in first-seen order.</summary>
    public IEnumerable<string> Categories => _model.Categories;

    /// <summary>Types the convention placed under <paramref name="category"/>, or empty if unknown.</summary>
    public IReadOnlyList<Type> this[string category] => _model[category];

    /// <summary>Discovered types marked with <c>AttributeContainerAttribute</c>.</summary>
    public IReadOnlyList<Type> Containers => _model.Containers;

    /// <summary>Discovered types implementing <c>IChildEntity</c>.</summary>
    public IReadOnlyList<Type> ChildEntities => _model.ChildEntities;

    /// <summary>Discovered types implementing <c>ISimpleEntity</c>.</summary>
    public IReadOnlyList<Type> SimpleEntities => _model.SimpleEntities;

    /// <summary>Discovered types implementing <c>IMergeable</c>.</summary>
    public IReadOnlyList<Type> Mergeables => _model.Mergeables;
}
