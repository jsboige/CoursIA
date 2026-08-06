using Newtonsoft.Json;
using Newtonsoft.Json.Serialization;
using MyIA.AI.ComponentModel.Entities;

namespace MyIA.AI.ComponentModel.Serialization;

/// <summary>
/// Decoration-driven JSON contract resolver: drives Newtonsoft.Json serialization from the
/// A1 metadata model rather than from hand-written serialization attributes. It is the
/// contract half of the <c>Aricie.Shared</c> "lego serialization" ancre (EPIC #7265, A2).
/// </summary>
/// <remarks>
/// <para>
/// The single rule it enforces today is breaking the <see cref="IChildEntity"/> parent/child
/// cycle: the <c>Parent</c> back-reference is <em>dropped on serialize</em> and
/// <em>rebuilt on load</em> by <see cref="MetadataJsonSerializer"/> (which walks the
/// deserialized tree and re-links parents). A naive serialize of an
/// <see cref="IChildEntity"/> tree would otherwise recurse through <c>child.Parent</c> back
/// into the root and either stack-overflow or emit a duplicated subtree on every node.
/// </para>
/// <para>
/// Categories (<see cref="MainCategoryAttribute"/>) and container markers
/// (<see cref="AttributeContainerAttribute"/>) are decoration on the <em>type</em>, not
/// instance state: they are preserved across a round-trip as long as the concrete runtime
/// type is reconstructed, which <see cref="MetadataJsonSerializer"/> guarantees via
/// <see cref="Newtonsoft.Json.TypeNameHandling.Auto"/> on the polymorphic
/// <see cref="IChildEntity.Children"/> collection. No category state is serialized — the
/// type <em>is</em> the category carrier.
/// </para>
/// </remarks>
public sealed class MetadataContractResolver : DefaultContractResolver
{
    /// <summary>
    /// Builds the property set for a type, dropping the <see cref="IChildEntity.Parent"/>
    /// back-reference for hierarchical entities so the tree serializes without recursion.
    /// </summary>
    protected override IList<JsonProperty> CreateProperties(Type type, MemberSerialization memberSerialization)
    {
        var properties = base.CreateProperties(type, memberSerialization);

        if (typeof(IChildEntity).IsAssignableFrom(type) && type != typeof(IChildEntity))
        {
            properties = properties
                .Where(p => !IsParentBackReference(p))
                .ToList();
        }

        return properties;
    }

    private static bool IsParentBackReference(JsonProperty property)
    {
        return string.Equals(property.PropertyName, "Parent", StringComparison.Ordinal)
               && property.PropertyType is not null
               && typeof(IChildEntity).IsAssignableFrom(property.PropertyType);
    }
}
