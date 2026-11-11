using System.Reflection;
using MyIA.AI.ComponentModel.Entities;

namespace MyIA.AI.ComponentModel.Serialization;

/// <summary>
/// Decoration-driven contract resolver for XML serialization. It inspects the A1
/// marker/decoration model and produces the serialization plan that drives
/// <see cref="MetadataXmlSerializer"/>: a stable type discriminator per concrete type
/// (so polymorphic children are reconstructed by their concrete type, not the
/// <see cref="IChildEntity"/> interface) and the set of round-trippable properties per
/// type (public read-write value properties, excluding <see cref="IChildEntity.Parent"/>
/// — the parent/child cycle is rebuilt on load, not serialized).
/// </summary>
/// <remarks>
/// This is the XML half of the A2 "lego serialization" tranche (EPIC #7265, ancre A2),
/// described in the A1 README as <c>XmlAwareContractResolver</c>. It is the sibling of
/// the A2 JSON contract resolver: where Newtonsoft.Json drives serialization through a
/// <c>IContractResolver</c>, <c>System.Xml</c> has no equivalent hook, so this resolver
/// instead feeds a <see cref="NodeSurrogate"/> (DynamicSurrogate) tree —
/// <c>XmlSerializer</c> cannot round-trip <c>IReadOnlyList&lt;IChildEntity&gt;</c>
/// (read-only, polymorphic) directly, so the live graph is projected to a serializable
/// surrogate shape and rebuilt on load.
/// </remarks>
public sealed class XmlAwareContractResolver
{
    private readonly Dictionary<string, Type> _typeByKey = new(StringComparer.Ordinal);
    private readonly Dictionary<Type, IReadOnlyList<PropertyInfo>> _writablePropsByType = new();

    /// <summary>Builds a resolver over the concrete <paramref name="knownTypes"/> that may appear in a graph.</summary>
    public XmlAwareContractResolver(IEnumerable<Type> knownTypes)
    {
        ArgumentNullException.ThrowIfNull(knownTypes);
        foreach (var type in knownTypes)
            Register(type);
    }

    private void Register(Type type)
    {
        // Only concrete classes are instantiable graph nodes.
        if (!type.IsClass || type.IsAbstract)
            return;

        // Stable discriminator: the type's simple name. Collisions are the caller's
        // responsibility (register distinct simple names, like the A2 JSON $type).
        _typeByKey.TryAdd(type.Name, type);

        // Round-trippable properties: public get+set value types (string/primitive/decimal).
        // Parent is excluded on purpose — it is the back-reference that would recurse the
        // root through every child; MetadataXmlSerializer rebuilds it via AddChild on load.
        var writable = type
            .GetProperties(BindingFlags.Public | BindingFlags.Instance)
            .Where(p => p.CanRead && p.CanWrite && p.Name != nameof(IChildEntity.Parent))
            .Where(IsSimpleSerializable)
            .ToList();

        _writablePropsByType[type] = writable;
    }

    private static bool IsSimpleSerializable(PropertyInfo p)
    {
        var t = Nullable.GetUnderlyingType(p.PropertyType) ?? p.PropertyType;
        return t.IsPrimitive || t == typeof(string) || t == typeof(decimal);
    }

    /// <summary>The discriminator written as <c>type="..."</c> on a serialized node.</summary>
    public string TypeKey(Type type) => type.Name;

    /// <summary>The concrete type registered under <paramref name="key"/>, or null if unknown.</summary>
    public Type? ResolveType(string key) =>
        _typeByKey.TryGetValue(key, out var type) ? type : null;

    /// <summary>The value properties to serialize for <paramref name="type"/> (empty for containers with only children).</summary>
    public IReadOnlyList<PropertyInfo> WritableProperties(Type type) =>
        _writablePropsByType.TryGetValue(type, out var props) ? props : Array.Empty<PropertyInfo>();
}
