using System.Reflection;
using MyIA.AI.ComponentModel.Attributes;

namespace MyIA.AI.ComponentModel.Providers;

/// <summary>
/// Reflection-driven provider that discovers decorated/marker types across a set of
/// assemblies and exposes them for introspection. This is the metadata-driven
/// decoration -> introspection bridge: decorate a class with
/// <see cref="MainCategoryAttribute"/> / <see cref="AttributeContainerAttribute"/> or have
/// it implement <c>IChildEntity</c> / <c>ISimpleEntity</c> / <c>IMergeable</c>, and the
/// container surfaces it with no explicit registration.
/// </summary>
/// <remarks>
/// Decoration-driven discovery (this class) is one of three strategies in the
/// <c>Aricie.Shared</c> provider hierarchy (EPIC #7265): <see cref="SimpleProviderContainer"/>
/// (explicit flat registration) and <see cref="AutoProviderContainer"/> (naming/namespace
/// convention scan) are the other two; all share the <see cref="IProviderContainer"/> read
/// contract and the <see cref="ProviderModel"/> classifier.
/// </remarks>
public sealed class ReflectedProviderContainer : IProviderContainer
{
    private readonly ProviderModel _model;

    private ReflectedProviderContainer(ProviderModel model) => _model = model;

    /// <summary>Builds a container by scanning the assembly that declares <typeparamref name="TMarker"/>.</summary>
    public static ReflectedProviderContainer FromAssembly<TMarker>() =>
        FromAssembly(typeof(TMarker).Assembly);

    /// <summary>Builds a container by scanning a single assembly.</summary>
    public static ReflectedProviderContainer FromAssembly(Assembly assembly) =>
        FromAssemblies(assembly);

    /// <summary>Builds a container by scanning several assemblies (union of their types).</summary>
    public static ReflectedProviderContainer FromAssemblies(params Assembly[] assemblies) =>
        FromTypes(ProviderModel.GatherTypes(assemblies));

    /// <summary>Builds a container from an explicit type set (test seam + controlled scope).</summary>
    public static ReflectedProviderContainer FromTypes(IEnumerable<Type> types)
    {
        ArgumentNullException.ThrowIfNull(types);

        // Category comes from the [MainCategory] decoration (0 or 1 per type); the marker
        // buckets are filled by the shared classifier from the implemented interfaces.
        var model = ProviderModel.Build(
            types,
            type => type.GetCustomAttribute<MainCategoryAttribute>() is { } category
                ? new[] { category.Name }
                : Array.Empty<string>());

        return new ReflectedProviderContainer(model);
    }

    /// <summary>Categories discovered, in first-seen order.</summary>
    public IEnumerable<string> Categories => _model.Categories;

    /// <summary>Types registered under <paramref name="category"/>, or empty if unknown.</summary>
    public IReadOnlyList<Type> this[string category] => _model[category];

    /// <summary>Types decorated with <see cref="AttributeContainerAttribute"/>.</summary>
    public IReadOnlyList<Type> Containers => _model.Containers;

    /// <summary>Types implementing <c>IChildEntity</c> (hierarchical nodes).</summary>
    public IReadOnlyList<Type> ChildEntities => _model.ChildEntities;

    /// <summary>Types implementing <c>ISimpleEntity</c> (flat leaves).</summary>
    public IReadOnlyList<Type> SimpleEntities => _model.SimpleEntities;

    /// <summary>Types implementing <c>IMergeable</c>.</summary>
    public IReadOnlyList<Type> Mergeables => _model.Mergeables;
}
