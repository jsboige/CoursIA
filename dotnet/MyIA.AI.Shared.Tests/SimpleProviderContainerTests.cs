using MyIA.AI.ComponentModel.Providers;
using Xunit;

namespace MyIA.AI.Shared.Tests;

/// <summary>
/// Proves the A1+ flat-registration contract: types added by hand under a category key are
/// exposed exactly like a decoration-discovered set, with marker-interface buckets derived
/// from the registered types and no reflection on the source.
/// </summary>
public class SimpleProviderContainerTests
{
    [Fact]
    public void Register_ExposesTypeUnderItsCategory()
    {
        var provider = new SimpleProviderContainer()
            .Register<PaymentGateway>("Payment");

        var payment = provider["Payment"];

        Assert.Single(payment);
        Assert.Equal(typeof(PaymentGateway), payment[0]);
    }

    [Fact]
    public void Register_SameTypeUnderSeveralCategories_AppearsInEach()
    {
        // A flat container may file one type under several keys (decoration cannot: [MainCategory] is single).
        var provider = new SimpleProviderContainer()
            .Register<PaymentGateway>("Payment")
            .Register<PaymentGateway>("Checkout");

        Assert.Contains(typeof(PaymentGateway), provider["Payment"]);
        Assert.Contains(typeof(PaymentGateway), provider["Checkout"]);
    }

    [Fact]
    public void Register_DuplicateTypeUnderSameCategory_DoesNotDouble()
    {
        var provider = new SimpleProviderContainer()
            .Register<PaymentGateway>("Payment")
            .Register<PaymentGateway>("Payment");

        Assert.Single(provider["Payment"]);
    }

    [Fact]
    public void Categories_ListsRegisteredKeys_InRegistrationOrder()
    {
        var provider = new SimpleProviderContainer()
            .Register<PaymentGateway>("Payment")
            .Register<ContentFolder>("Content");

        var categories = provider.Categories.ToArray();

        Assert.Equal(new[] { "Payment", "Content" }, categories);
    }

    [Fact]
    public void Indexer_UnknownCategory_ReturnsEmpty_NoThrow()
    {
        var provider = new SimpleProviderContainer().Register<PaymentGateway>("Payment");

        Assert.Empty(provider["DoesNotExist"]);
    }

    [Fact]
    public void MarkerBuckets_DerivedFromRegisteredTypes_EvenWithoutDecoration()
    {
        // PlainLeaf is undecorated but implements ISimpleEntity — registering it surfaces it
        // in SimpleEntities exactly like ReflectedProviderContainer would.
        var provider = new SimpleProviderContainer()
            .Register<PlainLeaf>("Misc");

        Assert.Contains(typeof(PlainLeaf), provider.SimpleEntities);
        Assert.Contains(typeof(PlainLeaf), provider["Misc"]);
    }

    [Fact]
    public void ContainersAndChildEntities_DerivedFromRegisteredHierarchyTypes()
    {
        var provider = new SimpleProviderContainer()
            .Register<ContentFolder>("Content")
            .Register<ContentItem>("Content");

        // ContentFolder carries [AttributeContainer] + IChildEntity; ContentItem is IChildEntity + IMergeable.
        Assert.Contains(typeof(ContentFolder), provider.Containers);
        Assert.Contains(typeof(ContentFolder), provider.ChildEntities);
        Assert.Contains(typeof(ContentItem), provider.ChildEntities);
        Assert.Contains(typeof(ContentItem), provider.Mergeables);
    }

    [Fact]
    public void EmptyContainer_ExposesNothing_WithoutThrowing()
    {
        var provider = new SimpleProviderContainer();

        Assert.Empty(provider.Categories);
        Assert.Empty(provider["Anything"]);
        Assert.Empty(provider.SimpleEntities);
    }

    [Fact]
    public void Register_RejectsWhitespaceCategory()
    {
        var provider = new SimpleProviderContainer();

        Assert.Throws<ArgumentException>(() => provider.Register<PaymentGateway>("   "));
    }

    [Fact]
    public void Register_AfterRead_InvalidatesCache_SoLaterTypeAppears()
    {
        // The lazy read-model is rebuilt on each mutation, so reads are always fresh.
        var provider = new SimpleProviderContainer().Register<PaymentGateway>("Payment");
        _ = provider.Categories; // force a build

        provider.Register<ContentFolder>("Content");

        Assert.Contains("Content", provider.Categories.ToArray());
        Assert.Contains(typeof(ContentFolder), provider["Content"]);
    }
}
