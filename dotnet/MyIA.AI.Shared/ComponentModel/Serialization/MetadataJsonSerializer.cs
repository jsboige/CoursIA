using Newtonsoft.Json;
using MyIA.AI.ComponentModel.Entities;

namespace MyIA.AI.ComponentModel.Serialization;

/// <summary>
/// Decoration-driven JSON facade that round-trips the A1 metadata model: serialize any
/// decorated/marked graph to JSON and rebuild an equivalent graph on load, with the
/// <see cref="IChildEntity"/> hierarchy (concrete child types, parent back-references,
/// discoverable categories) intact. Modernized port of <c>Aricie.Shared</c>'s lego
/// serialization entry point (EPIC #7265, A2).
/// </summary>
/// <remarks>
/// <para>
/// <b>What round-trips.</b> Concrete child types are reconstructed via
/// <see cref="TypeNameHandling.Auto"/> on the polymorphic
/// <see cref="IChildEntity.Children"/> collection; the <c>Parent</c> back-reference is
/// rebuilt post-load (see <see cref="MetadataContractResolver"/>); categories and container
/// markers ride on the reconstructed type, so a deserialized graph is introspectable by a
/// <see cref="Providers.ReflectedProviderContainer"/> exactly like the original.
/// </para>
/// <para>
/// <b>Security caveat.</b> <see cref="TypeNameHandling.Auto"/> embeds runtime type names in
/// the payload and binds them on deserialize. This is appropriate for an internal socle
/// serializing <em>trusted</em> graphs (own configuration, own entity trees). Do NOT feed
/// this serializer untrusted input: craft a <see cref="JsonSerializerSettings"/> with
/// <see cref="TypeNameHandling.None"/> and a custom binding strategy instead.
/// </para>
/// <para>
/// <b>Out of scope (deferred to A2+).</b> XML decoration-driven contract
/// (<c>XmlAwareContractResolver</c> over <c>System.Xml.Serialization</c>) and
/// <c>DynamicSurrogate</c> for non-default-ctor entities — documented in the README, landed
/// as a separate tranche to keep this anchor bounded to JSON.
/// </para>
/// </remarks>
public static class MetadataJsonSerializer
{
    /// <summary>
    /// Default settings used by the facade. Exposed so a caller can clone, tweak (e.g.
    /// formatting), and still benefit from the decoration-driven contract.
    /// </summary>
    public static JsonSerializerSettings CreateDefaultSettings() => new()
    {
        ContractResolver = new MetadataContractResolver(),
        // Auto emits $type only where the runtime type differs from the declared member type
        // (the polymorphic IChildEntity.Children elements) — enough to rebuild the concrete
        // tree, no noisier than necessary.
        TypeNameHandling = TypeNameHandling.Auto,
        Formatting = Formatting.Indented,
        NullValueHandling = NullValueHandling.Include,
    };

    private static readonly JsonSerializerSettings DefaultSettings = CreateDefaultSettings();

    /// <summary>Serializes a metadata graph to indented JSON.</summary>
    public static string Serialize(object? value) =>
        JsonConvert.SerializeObject(value, DefaultSettings);

    /// <summary>
    /// Deserializes a JSON graph and rebuilds the <see cref="IChildEntity"/> parent
    /// back-references that were dropped on serialize.
    /// </summary>
    public static T Deserialize<T>(string json)
    {
        ArgumentNullException.ThrowIfNull(json);
        var value = JsonConvert.DeserializeObject<T>(json, DefaultSettings)
                    ?? throw new JsonSerializationException(
                        $"Deserialization returned null for {typeof(T)}.");
        RelinkParents(value);
        return value;
    }

    /// <summary>
    /// Walks any <see cref="IChildEntity"/> reachable from the root and re-establishes
    /// <c>Parent</c> to match the deserialized child topology.
    /// </summary>
    private static void RelinkParents(object? root)
    {
        switch (root)
        {
            case IChildEntity childRoot:
                RelinkRecursive(childRoot, parent: null);
                break;
            // Non-hierarchical payloads (ISimpleEntity leaves, scalars) have no Parent to
                // rebuild — nothing to do.
        }
    }

    private static void RelinkRecursive(IChildEntity node, IChildEntity? parent)
    {
        node.Parent = parent;
        foreach (var child in node.Children)
        {
            RelinkRecursive(child, node);
        }
    }
}
