using System.IO;
using System.Reflection;
using System.Xml;
using System.Xml.Serialization;
using MyIA.AI.ComponentModel.Entities;

namespace MyIA.AI.ComponentModel.Serialization;

/// <summary>
/// Decoration-driven XML serializer that round-trips the A1 metadata graph through a
/// <see cref="NodeSurrogate"/> (DynamicSurrogate) tree. Serialize a decorated
/// <see cref="IChildEntity"/> root to XML and rebuild an equivalent graph on load, with
/// concrete child types, round-trippable value properties, and the parent/child
/// hierarchy intact (the <see cref="IChildEntity.Parent"/> cycle is broken on serialize
/// by the contract resolver and rebuilt on load via <c>AddChild</c>).
/// </summary>
/// <remarks>
/// XML half of the A2 "lego serialization" tranche (EPIC #7265, ancre A2). It is the
/// sibling of the A2 JSON serializer: both round-trip the same A1 metadata model, but
/// through different engines (<c>System.Xml</c> vs <c>Newtonsoft.Json</c>) and different
/// cycle/polymorphism strategies (DynamicSurrogate + <c>AddChild</c> relink vs
/// contract-resolver Parent drop + <c>TypeNameHandling.Auto</c>). The two halves are
/// independent: A2+ builds on the A1 primitives, not on the A2 JSON code.
/// </remarks>
public sealed class MetadataXmlSerializer
{
    private readonly XmlAwareContractResolver _resolver;
    private readonly XmlSerializer _serializer;

    /// <summary>Builds a serializer driven by <paramref name="resolver"/>'s decoration plan.</summary>
    public MetadataXmlSerializer(XmlAwareContractResolver resolver)
    {
        _resolver = resolver ?? throw new ArgumentNullException(nameof(resolver));
        _serializer = new XmlSerializer(typeof(NodeSurrogate));
    }

    /// <summary>Serializes the <paramref name="root"/> graph to indented XML (Parent cycle excluded).</summary>
    public string Serialize(IChildEntity root)
    {
        ArgumentNullException.ThrowIfNull(root);
        var surrogate = ToSurrogate(root);
        using var writer = new StringWriter();
        using var xml = XmlWriter.Create(writer, new XmlWriterSettings
        {
            Indent = true,
            OmitXmlDeclaration = false,
        });
        _serializer.Serialize(xml, surrogate);
        return writer.ToString();
    }

    /// <summary>Rebuilds the graph from XML as a concrete <typeparamref name="T"/> root.</summary>
    public T Deserialize<T>(string xml) where T : class, IChildEntity
    {
        ArgumentNullException.ThrowIfNull(xml);
        using var reader = new StringReader(xml);
        var surrogate = (NodeSurrogate)_serializer.Deserialize(reader)!;
        return (T)FromSurrogate(surrogate);
    }

    private NodeSurrogate ToSurrogate(IChildEntity node)
    {
        var type = node.GetType();
        var surrogate = new NodeSurrogate { TypeKey = _resolver.TypeKey(type) };

        foreach (var property in _resolver.WritableProperties(type))
        {
            var value = property.GetValue(node);
            surrogate.Properties.Add(new PropertySurrogate
            {
                Name = property.Name,
                Value = value?.ToString() ?? string.Empty,
            });
        }

        foreach (var child in node.Children)
            surrogate.Children.Add(ToSurrogate(child));

        return surrogate;
    }

    private IChildEntity FromSurrogate(NodeSurrogate surrogate)
    {
        var type = _resolver.ResolveType(surrogate.TypeKey)
                   ?? throw new InvalidOperationException(
                       $"Unknown type discriminator '{surrogate.TypeKey}'. Register it in the XmlAwareContractResolver.");

        var node = (IChildEntity)Activator.CreateInstance(type)!;

        // Restore round-trippable value properties.
        var writable = _resolver.WritableProperties(type);
        foreach (var entry in surrogate.Properties)
        {
            var property = writable.FirstOrDefault(p => p.Name == entry.Name);
            if (property is null)
                continue;
            var converted = ConvertValue(entry.Value, property.PropertyType);
            if (converted is not null)
                property.SetValue(node, converted);
        }

        // Rebuild children + the Parent cycle. Prefer a public AddChild (the container
        // pattern: it sets child.Parent and appends to the backing list atomically); fall
        // back to a direct Parent link for nodes that expose children without AddChild.
        foreach (var childSurrogate in surrogate.Children)
        {
            var child = FromSurrogate(childSurrogate);
            var addChild = type.GetMethod("AddChild", new[] { typeof(IChildEntity) });
            if (addChild is not null)
                addChild.Invoke(node, new object[] { child });
            else
                child.Parent = node;
        }

        return node;
    }

    private static object? ConvertValue(string value, Type target)
    {
        if (target == typeof(string))
            return value;
        var underlying = Nullable.GetUnderlyingType(target) ?? target;
        try
        {
            return Convert.ChangeType(value, underlying);
        }
        catch
        {
            return null;
        }
    }
}
