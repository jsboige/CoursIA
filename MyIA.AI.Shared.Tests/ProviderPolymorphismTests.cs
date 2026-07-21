using MyIA.AI.ComponentModel.Providers;
using Xunit;

namespace MyIA.AI.Shared.Tests;

/// <summary>
/// Proves the three discovery strategies (decoration, explicit registration, convention)
/// are interchangeable through the shared <see cref="IProviderContainer"/> read contract:
/// a consumer can ask for types without coupling to how they were discovered.
/// </summary>
public class ProviderPolymorphismTests
{
    private static readonly Type[] FixtureTypes =
    {
        typeof(PaymentGateway),
        typeof(ContentFolder),
        typeof(ContentItem),
    };

    [Fact]
    public void AllThreeStrategies_ImplementIProviderContainer()
    {
        IProviderContainer reflected = ReflectedProviderContainer.FromTypes(FixtureTypes);
        IProviderContainer simple = new SimpleProviderContainer()
            .Register<PaymentGateway>("Payment")
            .Register<ContentFolder>("Content")
            .Register<ContentItem>("Content");
        IProviderContainer auto = AutoProviderContainer.FromTypes(
            FixtureTypes,
            t => t == typeof(PaymentGateway) ? "Payment" : "Content");

        // Same fixture set, same read surface — the three are uniform regardless of strategy.
        Assert.Single(reflected["Payment"]);
        Assert.Single(simple["Payment"]);
        Assert.Single(auto["Payment"]);

        Assert.Contains(typeof(ContentFolder), reflected["Content"]);
        Assert.Contains(typeof(ContentFolder), simple["Content"]);
        Assert.Contains(typeof(ContentFolder), auto["Content"]);

        // Marker buckets agree: each strategy files ContentItem as a mergeable child entity.
        foreach (var container in new[] { reflected, simple, auto })
        {
            Assert.Contains(typeof(ContentItem), container.Mergeables);
            Assert.Contains(typeof(ContentItem), container.ChildEntities);
            Assert.Contains(typeof(ContentFolder), container.Containers);
        }
    }
}
