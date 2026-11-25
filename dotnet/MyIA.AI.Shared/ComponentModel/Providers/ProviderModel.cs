using System.Collections.Generic;
using System.Reflection;
using MyIA.AI.ComponentModel.Attributes;
using MyIA.AI.ComponentModel.Entities;

namespace MyIA.AI.ComponentModel.Providers;

/// <summary>
/// Shared read-model + classification for the provider hierarchy. Centralizes how a set
/// of types is partitioned into categories / containers / marker-interface buckets so the
/// three discovery strategies (decoration, explicit registration, naming convention) reuse
/// one classifier instead of duplicating the reflection loop. Modernized port of
/// <c>Aricie.Shared</c>'s shared provider indexing (EPIC #7265, ancre A1+).
/// </summary>
internal sealed class ProviderModel
{
    private readonly IReadOnlyDictionary<string, List<Type>> _byCategory;
    private readonly List<Type> _containers;
    private readonly List<Type> _childEntities;
    private readonly List<Type> _simpleEntities;
    private readonly List<Type> _mergeables;

    private ProviderModel(
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

    /// <summary>
    /// Loads the public, non-system types declared in <paramref name="assemblies"/>,
    /// tolerating unloadable types (a single broken type must not poison the container).
    /// Shared by <see cref="ReflectedProviderContainer"/> and
    /// <see cref="AutoProviderContainer"/> so assembly scanning is identical across both.
    /// </summary>
    public static List<Type> GatherTypes(params Assembly[] assemblies)
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

        return types;
    }

    /// <summary>
    /// Builds the read-model from a set of types, assigning each type to zero or more
    /// categories via <paramref name="categoryFor"/>. Containers and marker-interface
    /// buckets are always derived from the type itself (decoration + implemented
    /// interfaces), independent of the discovery strategy — so a convention- or
    /// registration-discovered <c>ISimpleEntity</c> lands in <see cref="SimpleEntities"/>
    /// exactly like a decoration-discovered one.
    /// </summary>
    public static ProviderModel Build(IEnumerable<Type> types, Func<Type, IEnumerable<string>> categoryFor)
    {
        ArgumentNullException.ThrowIfNull(types);
        ArgumentNullException.ThrowIfNull(categoryFor);

        var byCategory = new Dictionary<string, List<Type>>(StringComparer.Ordinal);
        var containers = new List<Type>();
        var childEntities = new List<Type>();
        var simpleEntities = new List<Type>();
        var mergeables = new List<Type>();
        var seenCategoryKeys = new HashSet<(Type Type, string Category)>();

        foreach (var type in types)
        {
            ArgumentNullException.ThrowIfNull(type);

            foreach (var category in categoryFor(type))
            {
                // A discovery strategy may yield the same (type, category) pair more than
                // once (e.g. a type registered twice under the same key); keep one entry.
                if (!seenCategoryKeys.Add((type, category)))
                {
                    continue;
                }

                if (!byCategory.TryGetValue(category, out var bucket))
                {
                    bucket = new List<Type>();
                    byCategory[category] = bucket;
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

        return new ProviderModel(byCategory, containers, childEntities, simpleEntities, mergeables);
    }

    public IEnumerable<string> Categories => _byCategory.Keys;

    public IReadOnlyList<Type> this[string category] =>
        _byCategory.TryGetValue(category, out var bucket) ? bucket : Array.Empty<Type>();

    public IReadOnlyList<Type> Containers => _containers;
    public IReadOnlyList<Type> ChildEntities => _childEntities;
    public IReadOnlyList<Type> SimpleEntities => _simpleEntities;
    public IReadOnlyList<Type> Mergeables => _mergeables;
}
