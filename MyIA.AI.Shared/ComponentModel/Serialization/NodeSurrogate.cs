using System.Xml.Serialization;

namespace MyIA.AI.ComponentModel.Serialization;

/// <summary>
/// XML-serializable surrogate for a single node of the metadata graph (the
/// <c>DynamicSurrogate</c> of the A2+ XML tranche, EPIC #7265).
/// <see cref="System.Xml.Serialization.XmlSerializer"/> cannot round-trip an
/// <see cref="MyIA.AI.ComponentModel.Entities.IChildEntity"/> directly: its
/// <c>Children</c> is <c>IReadOnlyList&lt;IChildEntity&gt;</c> (read-only + polymorphic)
/// and <c>Parent</c> is a back-reference cycle. This surrogate captures the tree in an
/// XML-friendly shape — a type discriminator (the concrete type name, so polymorphic
/// children reconstruct to their concrete type), a property bag (round-trippable value
/// properties), and a recursive list of child surrogates.
/// <see cref="MetadataXmlSerializer"/> projects the live graph to this shape on
/// serialize and rebuilds the concrete <c>IChildEntity</c> tree (instantiating the
/// concrete type, restoring properties, re-linking <c>Parent</c> via <c>AddChild</c>)
/// on load.
/// </summary>
public sealed class NodeSurrogate
{
    /// <summary>Concrete type discriminator (the <see cref="XmlAwareContractResolver.TypeKey"/>).</summary>
    [XmlAttribute("type")]
    public string TypeKey { get; set; } = string.Empty;

    /// <summary>Round-trippable value properties of the node (name/value pairs).</summary>
    [XmlElement("property")]
    public List<PropertySurrogate> Properties { get; set; } = new();

    /// <summary>Child nodes, recursively (the polymorphic Children projected to a serializable list).</summary>
    [XmlElement("child")]
    public List<NodeSurrogate> Children { get; set; } = new();
}

/// <summary>
/// A single name/value property entry in a <see cref="NodeSurrogate"/> property bag.
/// Only simple value types are carried (string/primitive/decimal); complex state and
/// the <c>Parent</c> cycle are rebuilt, not serialized.
/// </summary>
public sealed class PropertySurrogate
{
    /// <summary>The property name on the concrete type.</summary>
    [XmlAttribute("name")]
    public string Name { get; set; } = string.Empty;

    /// <summary>The property value as a string (parsed back to the target type on load).</summary>
    [XmlAttribute("value")]
    public string Value { get; set; } = string.Empty;
}
