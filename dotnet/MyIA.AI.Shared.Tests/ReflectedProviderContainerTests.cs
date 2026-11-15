using System.Reflection;
using MyIA.AI.ComponentModel.Attributes;
using MyIA.AI.ComponentModel.Providers;
using Xunit;

namespace MyIA.AI.Shared.Tests;

/// <summary>
/// Proves the A1 metadata-driven decoration -> introspection contract: decorate a type
/// (or have it implement a marker interface) and a ReflectedProviderContainer surfaces it
/// with no explicit registration.
/// </summary>
public class ReflectedProviderContainerTests
{
    // Controlled, exhaustive scope: every A1 primitive is exercised by exactly one fixture.
    private static readonly Type[] FixtureTypes =
    {
        typeof(PaymentGateway), // [MainCategory("Payment")] + ISimpleEntity
        typeof(ContentFolder),  // [MainCategory("Content")] + [AttributeContainer] + IChildEntity
        typeof(ContentItem),    // [MainCategory("Content")] + IChildEntity + IMergeable
        typeof(PlainLeaf),      // ISimpleEntity only, no category
    };

    private static ReflectedProviderContainer Sut => ReflectedProviderContainer.FromTypes(FixtureTypes);

    [Fact]
    public void Indexer_DecoratedCategory_ExposesItsTypes()
    {
        var provider = Sut;

        var payment = provider["Payment"];
        var content = provider["Content"];

        Assert.Single(payment);
        Assert.Equal(typeof(PaymentGateway), payment[0]);

        Assert.Equal(2, content.Count);
        Assert.Contains(typeof(ContentFolder), content);
        Assert.Contains(typeof(ContentItem), content);
    }

    [Fact]
    public void Categories_ListsAllMainCategoryNames_WithoutDuplicates()
    {
        var categories = Sut.Categories.ToArray();

        Assert.Equal(2, categories.Length);
        Assert.Contains("Payment", categories);
        Assert.Contains("Content", categories);
    }

    [Fact]
    public void Indexer_UnknownCategory_ReturnsEmpty_NoThrow()
    {
        var unknown = Sut["DoesNotExist"];

        Assert.NotNull(unknown);
        Assert.Empty(unknown);
    }

    [Fact]
    public void Containers_ExposesOnlyAttributeContainerDecoratedTypes()
    {
        var containers = Sut.Containers;

        Assert.Single(containers);
        Assert.Equal(typeof(ContentFolder), containers[0]);
    }

    [Fact]
    public void ChildEntities_ExposesIChildEntityImplementers()
    {
        var children = Sut.ChildEntities;

        Assert.Equal(2, children.Count);
        Assert.Contains(typeof(ContentFolder), children);
        Assert.Contains(typeof(ContentItem), children);
    }

    [Fact]
    public void SimpleEntities_ExposesISimpleEntityImplementers_IncludingUndecorated()
    {
        var simples = Sut.SimpleEntities;

        Assert.Equal(2, simples.Count);
        Assert.Contains(typeof(PaymentGateway), simples);
        Assert.Contains(typeof(PlainLeaf), simples);
    }

    [Fact]
    public void Mergeables_ExposesIMergeableImplementers()
    {
        var mergeables = Sut.Mergeables;

        Assert.Single(mergeables);
        Assert.Equal(typeof(ContentItem), mergeables[0]);
    }

    [Fact]
    public void DecorationAndMarkers_Combine_OnTheSameType()
    {
        // ContentFolder carries a category, is a container, AND is a child entity:
        // the three primitives compose, the type appears in all three views.
        var provider = Sut;

        Assert.Contains(typeof(ContentFolder), provider["Content"]);
        Assert.Contains(typeof(ContentFolder), provider.Containers);
        Assert.Contains(typeof(ContentFolder), provider.ChildEntities);
    }

    [Fact]
    public void FromAssembly_TMarker_ScansAssembly_AndFindsKnownFixture()
    {
        // Marker = a type declared in this test assembly, so the scan covers the fixtures above.
        var provider = ReflectedProviderContainer.FromAssembly<ReflectedProviderContainerTests>();

        Assert.Contains("Content", provider.Categories);
        Assert.Contains(typeof(ContentFolder), provider["Content"]);
    }

    [Fact]
    public void AttributeContainer_ChildType_ReadBack()
    {
        var attr = typeof(ContentFolder).GetCustomAttribute<AttributeContainerAttribute>();

        Assert.NotNull(attr);
        Assert.Equal(typeof(ContentItem), attr!.ChildType);
    }

    [Fact]
    public void MainCategoryAttribute_RejectsWhitespaceName()
    {
        Assert.Throws<ArgumentException>(() => new MainCategoryAttribute("   "));
    }

    [Fact]
    public void MainCategoryAttribute_AcceptsValidName_AndDefaultOrder()
    {
        var attr = new MainCategoryAttribute("Demo");
        Assert.Equal("Demo", attr.Name);
        Assert.Equal(0, attr.Order);
    }
}
