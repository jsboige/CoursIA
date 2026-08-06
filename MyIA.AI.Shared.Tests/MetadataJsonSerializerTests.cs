using MyIA.AI.ComponentModel.Attributes;
using MyIA.AI.ComponentModel.Entities;
using MyIA.AI.ComponentModel.Providers;
using MyIA.AI.ComponentModel.Serialization;
using Newtonsoft.Json;
using Newtonsoft.Json.Linq;
using Xunit;

namespace MyIA.AI.Shared.Tests;

/// <summary>
/// Proves the A2 decoration-driven JSON round-trip: an A1 metadata graph (hierarchical
/// containers, polymorphic children, mergeable leaves, categorized types) serializes to
/// JSON and rebuilds into an equivalent, introspectable graph.
/// </summary>
public class MetadataJsonSerializerTests
{
    // Root -> sub-folder -> item: a 3-level tree to prove the infinite IChildEntity
    // hierarchy round-trips (not just a flat root).
    private static ContentFolder BuildTree()
    {
        var root = new ContentFolder();
        var sub = new ContentFolder();
        var leaf = new ContentItem { Title = "release-notes" };
        root.AddChild(sub);
        sub.AddChild(leaf);
        return root;
    }

    [Fact]
    public void RoundTrip_Preserves_Children_And_Concrete_Types()
    {
        var original = BuildTree();

        var json = MetadataJsonSerializer.Serialize(original);
        var loaded = MetadataJsonSerializer.Deserialize<ContentFolder>(json);

        Assert.Single(loaded.Children);
        var loadedSub = Assert.IsType<ContentFolder>(loaded.Children[0]);
        Assert.Single(loadedSub.Children);
        var loadedLeaf = Assert.IsType<ContentItem>(loadedSub.Children[0]);
        Assert.Equal("release-notes", loadedLeaf.Title);
    }

    [Fact]
    public void RoundTrip_Rebuilds_Parent_Back_References()
    {
        // Parent is dropped on serialize (cycle break) and must be reconstructed on load.
        var json = MetadataJsonSerializer.Serialize(BuildTree());
        var loaded = MetadataJsonSerializer.Deserialize<ContentFolder>(json);

        Assert.Null(loaded.Parent);

        var loadedSub = (ContentFolder)loaded.Children[0];
        Assert.Same(loaded, loadedSub.Parent);

        var loadedLeaf = (ContentItem)loadedSub.Children[0];
        Assert.Same(loadedSub, loadedLeaf.Parent);
    }

    [Fact]
    public void Serialized_Payload_Drops_The_Parent_Back_Reference()
    {
        // The contract resolver must strip Parent so the tree does not recurse / duplicate.
        var json = MetadataJsonSerializer.Serialize(BuildTree());

        Assert.DoesNotContain("\"Parent\"", json);
        // Sanity: the payload still carries the child topology it was asked to serialize.
        Assert.Contains("release-notes", json);
    }

    [Fact]
    public void Serialized_Payload_Emits_TypeName_For_Polymorphic_Children()
    {
        // Without $type on the IReadOnlyList<IChildEntity> elements, deserialization could
        // not reconstruct the concrete ContentFolder / ContentItem. Auto emits it. The
        // collection itself may be wrapped ($type + $values) when IReadOnlyList resolves to a
        // different runtime type, so descend to the first element regardless of wrapper.
        var json = MetadataJsonSerializer.Serialize(BuildTree());
        var parsed = JObject.Parse(json);

        var childrenToken = parsed["Children"]!;
        JObject firstChild = childrenToken.Type == JTokenType.Array
            ? (JObject)((JArray)childrenToken)[0]!
            : (JObject)((JObject)childrenToken).Property("$values")!.Value[0]!;

        Assert.Contains("ContentFolder", firstChild.Property("$type")!.Value.ToString());
    }

    [Fact]
    public void RoundTrip_Preserves_Categories_Post_Load()
    {
        // Categories ride on the reconstructed type, so a deserialized graph is introspectable
        // by ReflectedProviderContainer exactly like the original — the type IS the carrier.
        var loaded = MetadataJsonSerializer.Deserialize<ContentFolder>(
            MetadataJsonSerializer.Serialize(BuildTree()));

        var provider = ReflectedProviderContainer.FromAssembly<ReflectedProviderContainerTests>();

        // The concrete types that came back from JSON are still in the Content category.
        Assert.Contains(loaded.GetType(), provider["Content"]);
        Assert.Contains(((ContentFolder)loaded.Children[0]).GetType(), provider["Content"]);
    }

    [Fact]
    public void RoundTrip_Simple_Entity_Leaf()
    {
        // ISimpleEntity (flat leaf, no hierarchy) round-trips as a plain object.
        var gateway = new PaymentGateway();
        var json = MetadataJsonSerializer.Serialize(gateway);
        var loaded = MetadataJsonSerializer.Deserialize<PaymentGateway>(json);

        Assert.NotNull(loaded);
        Assert.Equal(gateway.Name, loaded.Name);
    }

    [Fact]
    public void RoundTrip_Supports_Merge_On_Deserialized_Instances()
    {
        // IMergeable on instances reconstituted from JSON: load a base with an empty title,
        // load an overlay carrying the title, merge — the socle's merge semantics survive the
        // round-trip (the serialization lego composes with the merge primitive).
        var baseItem = MetadataJsonSerializer.Deserialize<ContentItem>(
            MetadataJsonSerializer.Serialize(new ContentItem { Title = "" }));
        var overlay = MetadataJsonSerializer.Deserialize<ContentItem>(
            MetadataJsonSerializer.Serialize(new ContentItem { Title = "merged-title" }));

        var applied = baseItem.Merge(overlay);

        Assert.True(applied);
        Assert.Equal("merged-title", baseItem.Title);
    }

    [Fact]
    public void Deserialize_Null_Payload_Throws()
    {
        Assert.Throws<ArgumentNullException>(() => MetadataJsonSerializer.Deserialize<ContentFolder>(null!));
    }

    [Fact]
    public void CreateDefaultSettings_CanBe_Clone_Tuned()
    {
        // A caller can clone the default settings (same contract resolver) and still tweak
        // formatting without losing the decoration-driven contract.
        var settings = MetadataJsonSerializer.CreateDefaultSettings();
        settings.Formatting = Formatting.None;

        Assert.Same(typeof(MetadataContractResolver), settings.ContractResolver!.GetType());
        Assert.Equal(Formatting.None, settings.Formatting);
    }
}
