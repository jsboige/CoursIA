using System.Reflection;
using MyIA.AI.ComponentModel.Attributes;
using MyIA.AI.ComponentModel.Entities;

namespace MyIA.AI.ComponentModel.Providers;

/// <summary>
/// Reflection-driven provider that discovers decorated/marker types across a set of
/// assemblies and exposes them for introspection. This is the metadata-driven
/// decoration -> introspection bridge: decorate a class with
/// <see cref="MainCategoryAttribute"/> / <see cref="AttributeContainerAttribute"/> or have
/// it implement <see cref="IChildEntity"/> / <see cref="ISimpleEntity"/> / <see cref="IMergeable"/>,
/// and the container surfaces it with no explicit registration.
/// </summary>
/// <remarks>
/// Minimal first anchor of <c>Aricie.Shared</c>'s provider family (EPIC #7265, ancre A1).
/// <c>AutoProviderContainer</c> (assembly-scan conventions) and <c>SimpleProviderContainer</c>
/// (flat lookup) are deferred to follow-up tranches.
/// </remarks>
public sealed class ReflectedProviderContainer
{
    private readonly IReadOnlyDictionary<string, List<Type>> _byCategory;
    private readonly List<Type> _containers;
    private readonly List<Type> _childEntities;
    private readonly List<Type> _simpleEntities;
    private readonly List<Type> _mergeables;

    private ReflectedProviderContainer(
        IReadOnlyDictionary<string, List<Type>> byCategory,
        List<Type> containers,
        List<Type> childEntities,
        List<Type> simpleEntities,
        List<Type> mergeables)
    {
        _byCategory = byCategory;
        _containers = containers;
        _childEntities = childEntities;
        _simpleEntities = simpleEntities;
        _mergeables = mergeables;
    }

    /// <summary>Builds a container by scanning the assembly that declares <typeparamref name="TMarker"/>.</summary>
    public static ReflectedProviderContainer FromAssembly<TMarker>() =>
        FromAssembly(typeof(TMarker).Assembly);

    /// <summary>Builds a container by scanning a single assembly.</summary>
    public static ReflectedProviderContainer FromAssembly(Assembly assembly) =>
        FromAssemblies(assembly);

    /// <summary>Builds a container by scanning several assemblies (union of their types).</summary>
    public static ReflectedProviderContainer FromAssemblies(params Assembly[] assemblies)
    {
        ArgumentNullException.ThrowIfNull(assemblies);

        var types = new List<Type>();
        foreach (var assembly in assemblies)
        {
            ArgumentNullException.ThrowIfNull(assembly);
            Type[] declared;
            try
            {
                declared = assembly.GetTypes();
            }
            catch (ReflectionTypeLoadException ex)
            {
                // Keep the types that did load; a single unloadable type must not poison the container.
                declared = ex.Types.Where(t => t is not null).ToArray()!;
            }

            types.AddRange(declared.Where(t => t is { IsClass: true } || (t.IsInterface && !t.IsSpecialName)));
        }

        return FromTypes(types);
    }

    /// <summary>Builds a container from an explicit type set (test seam + controlled scope).</summary>
    public static ReflectedProviderContainer FromTypes(IEnumerable<Type> types)
    {
        ArgumentNullException.ThrowIfNull(types);

        var byCategory = new Dictionary<string, List<Type>>(StringComparer.Ordinal);
        var containers = new List<Type>();
        var childEntities = new List<Type>();
        var simpleEntities = new List<Type>();
        var mergeables = new List<Type>();

        foreach (var type in types)
        {
            ArgumentNullException.ThrowIfNull(type);

            if (type.GetCustomAttribute<MainCategoryAttribute>() is { } category)
            {
                if (!byCategory.TryGetValue(category.Name, out var bucket))
                {
                    bucket = new List<Type>();
                    byCategory[category.Name] = bucket;
                }

                bucket.Add(type);
            }

            if (type.GetCustomAttribute<AttributeContainerAttribute>() is not null)
            {
                containers.Add(type);
            }

            if (typeof(IChildEntity).IsAssignableFrom(type) && type != typeof(IChildEntity))
            {
                childEntities.Add(type);
            }

            if (typeof(ISimpleEntity).IsAssignableFrom(type) && type != typeof(ISimpleEntity))
            {
                simpleEntities.Add(type);
            }

            if (typeof(IMergeable).IsAssignableFrom(type) && type != typeof(IMergeable))
            {
                mergeables.Add(type);
            }
        }

        return new ReflectedProviderContainer(byCategory, containers, childEntities, simpleEntities, mergeables);
    }

    /// <summary>Categories discovered, in first-seen order.</summary>
    public IEnumerable<string> Categories => _byCategory.Keys;

    /// <summary>Types registered under <paramref name="category"/>, or empty if unknown.</summary>
    public IReadOnlyList<Type> this[string category] =>
        _byCategory.TryGetValue(category, out var bucket) ? bucket : Array.Empty<Type>();

    /// <summary>Types decorated with <see cref="AttributeContainerAttribute"/>.</summary>
    public IReadOnlyList<Type> Containers => _containers;

    /// <summary>Types implementing <see cref="IChildEntity"/> (hierarchical nodes).</summary>
    public IReadOnlyList<Type> ChildEntities => _childEntities;

    /// <summary>Types implementing <see cref="ISimpleEntity"/> (flat leaves).</summary>
    public IReadOnlyList<Type> SimpleEntities => _simpleEntities;

    /// <summary>Types implementing <see cref="IMergeable"/>.</summary>
    public IReadOnlyList<Type> Mergeables => _mergeables;
}
