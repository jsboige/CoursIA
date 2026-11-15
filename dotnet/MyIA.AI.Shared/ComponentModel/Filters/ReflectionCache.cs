using System.Collections.Concurrent;
using System.Reflection;

namespace MyIA.AI.ComponentModel.Filters;

/// <summary>
/// Process-wide cache of <see cref="PropertyInfo"/> per type — modern stand-in for the
/// Aricie.Services ReflectionHelper.GetPropertiesDictionary dependency (EPIC #7265, A3 T1).
/// A missing property name raises <see cref="KeyNotFoundException"/>, mirroring the VB
/// dictionary-indexer behavior of the original.
/// </summary>
internal static class ReflectionCache
{
    private static readonly ConcurrentDictionary<Type, IReadOnlyDictionary<string, PropertyInfo>> Cache = new();

    public static IReadOnlyDictionary<string, PropertyInfo> Properties(Type type)
        => Cache.GetOrAdd(type, static t => t.GetProperties().ToDictionary(p => p.Name));
}
