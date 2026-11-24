using MyIA.AI.ComponentModel.Serialization;
using Xunit;

namespace MyIA.AI.Shared.Tests;

/// <summary>
/// Proves the A2+ XML serialization contract (the XML half of the A2 lego-serialization
/// tranche, EPIC #7265): a decorated IChildEntity graph round-trips through XML with
/// concrete child types, value properties, and the parent/child hierarchy intact.
/// </summary>
public class MetadataXmlSerializerTests
{
    // The two concrete hierarchical fixtures: ContentFolder (container, no value props)
    // and ContentItem (leaf, carries Title). Both are registered so the discriminator
    // can reconstruct each to its concrete type.
    private static MetadataXmlSerializer NewSerializer() =>
        new(new XmlAwareContractResolver(new[] { typeof(ContentFolder), typeof(ContentItem) }));

    private static ContentFolder NewFolder(params ContentItem[] items)
    {
        var folder = new ContentFolder();
        foreach (var item in items)
            folder.AddChild(item);
        return folder;
    }

    [Fact]
    public void RoundTrip_RootFolderWithLeaf_RestoresHierarchyAndTitle()
    {
        var ser = NewSerializer();
        var original = NewFolder(new ContentItem { Title = "Intro" });

        var xml = ser.Serialize(original);
        var round = ser.Deserialize<ContentFolder>(xml);

        var restored = Assert.Single(round.Children);
        var item = Assert.IsType<ContentItem>(restored);
        Assert.Equal("Intro", item.Title);
    }

    [Fact]
    public void RoundTrip_ParentCycleRebuilt_ChildParentIsTheRestoredRoot()
    {
        var ser = NewSerializer();
        var original = NewFolder(new ContentItem { Title = "Child" });

        var round = ser.Deserialize<ContentFolder>(ser.Serialize(original));

        // Parent was excluded from serialization (cycle break) and rebuilt on load.
        var restoredChild = Assert.Single(round.Children);
        Assert.Same(round, restoredChild.Parent);
    }

    [Fact]
    public void RoundTrip_PolymorphicChildren_ReconstructsConcreteTypes()
    {
        // A folder containing a nested folder + a leaf exercises polymorphism: Children
        // is IReadOnlyList<IChildEntity>, and both ContentFolder and ContentItem must
        // come back as their concrete types (not a shared base).
        var ser = new MetadataXmlSerializer(
            new XmlAwareContractResolver(new[] { typeof(ContentFolder), typeof(ContentItem) }));

        var root = new ContentFolder();
        var sub = new ContentFolder();
        sub.AddChild(new ContentItem { Title = "Deep" });
        root.AddChild(sub);
        root.AddChild(new ContentItem { Title = "Shallow" });

        var round = ser.Deserialize<ContentFolder>(ser.Serialize(root));

        Assert.Equal(2, round.Children.Count);
        var roundSub = Assert.IsType<ContentFolder>(round.Children[0]);
        var roundLeaf = Assert.IsType<ContentItem>(round.Children[1]);
        Assert.Equal("Shallow", roundLeaf.Title);
        var deep = Assert.IsType<ContentItem>(Assert.Single(roundSub.Children));
        Assert.Equal("Deep", deep.Title);
    }

    [Fact]
    public void RoundTrip_EmptyTitle_PreservedAsEmpty()
    {
        var ser = NewSerializer();
        var original = NewFolder(new ContentItem { Title = "" });

        var round = ser.Deserialize<ContentFolder>(ser.Serialize(original));

        var item = Assert.IsType<ContentItem>(Assert.Single(round.Children));
        Assert.Equal("", item.Title);
    }

    [Fact]
    public void Serialize_ProducesWellFormedXml_WithTypeDiscriminator()
    {
        var ser = NewSerializer();
        var folder = NewFolder(new ContentItem { Title = "X" });

        var xml = ser.Serialize(folder);

        Assert.Contains("<?xml", xml);
        Assert.Contains("type=\"ContentFolder\"", xml);
        Assert.Contains("type=\"ContentItem\"", xml);
        Assert.Contains("name=\"Title\" value=\"X\"", xml);
        Assert.DoesNotContain("Parent", xml); // cycle-break: Parent never serialized
    }

    [Fact]
    public void Serialize_LeafWithNoChildren_EmitsEmptyChildList()
    {
        var ser = NewSerializer();
        var leaf = new ContentItem { Title = "Solo" };

        // A leaf serialized directly: no children element, its Title carried.
        var xml = ser.Serialize(leaf);

        Assert.Contains("type=\"ContentItem\"", xml);
        Assert.Contains("name=\"Title\" value=\"Solo\"", xml);
    }

    [Fact]
    public void RoundTrip_DeepNestedGraph_PreservesDepthAndLinks()
    {
        var ser = NewSerializer();
        var root = new ContentFolder();
        var level1 = new ContentFolder();
        var level2 = new ContentFolder();
        level2.AddChild(new ContentItem { Title = "Bottom" });
        level1.AddChild(level2);
        root.AddChild(level1);

        var round = ser.Deserialize<ContentFolder>(ser.Serialize(root));

        var l1 = Assert.IsType<ContentFolder>(Assert.Single(round.Children));
        var l2 = Assert.IsType<ContentFolder>(Assert.Single(l1.Children));
        var bottom = Assert.IsType<ContentItem>(Assert.Single(l2.Children));
        Assert.Equal("Bottom", bottom.Title);
        // Parent relink holds at every depth.
        Assert.Same(l2, bottom.Parent);
        Assert.Same(l1, l2.Parent);
        Assert.Same(round, l1.Parent);
    }

    [Fact]
    public void Constructor_NullResolver_Throws()
    {
        Assert.Throws<ArgumentNullException>(() => new MetadataXmlSerializer(null!));
    }

    [Fact]
    public void Deserialize_UnknownTypeDiscriminator_Throws()
    {
        // A resolver that knows ContentFolder but not ContentItem: the item's discriminator
        // is unresolvable, so load fails explicitly rather than silently dropping the child.
        var ser = new MetadataXmlSerializer(
            new XmlAwareContractResolver(new[] { typeof(ContentFolder) }));
        var xml = ser.Serialize(NewFolder(new ContentItem { Title = "Ghost" }));

        // Tamper: rewrite the item discriminator to something the resolver never saw.
        var tampered = xml.Replace("type=\"ContentItem\"", "type=\"NeverRegistered\"");

        Assert.Throws<InvalidOperationException>(() => ser.Deserialize<ContentFolder>(tampered));
    }
}
