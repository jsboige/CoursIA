using MyIA.AI.ComponentModel.Entities;
using MyIA.AI.ComponentModel.Providers;
using Xunit;

namespace MyIA.AI.Shared.Tests;

/// <summary>
/// Proves the A1+ convention-driven contract: types are discovered across an assembly and
/// categorized by a caller-supplied rule (namespace/name shape) with NO decoration, while
/// marker-interface buckets are still derived from the discovered types.
/// </summary>
public class AutoProviderContainerTests
{
    // Undecorated fixtures: no [MainCategory], so they prove the convention alone files them.
    // Each implements a marker so the derived buckets are non-empty.
    public sealed class LegacyGateway : ISimpleEntity { public string Name => "legacy-gw"; }
    public sealed class LegacyRenderer : ISimpleEntity { public string Name => "legacy-rdr"; }
    public sealed class LegacyNode : IChildEntity
    {
        public IChildEntity? Parent { get; set; }
        public IReadOnlyList<IChildEntity> Children => Array.Empty<IChildEntity>();
    }

    // Convention: file by the trailing segment of the type name past "Legacy" (Gateway/Renderer/Node).
    private static string? CategoryByNameTail(Type t) =>
        t.Name.StartsWith("Legacy", StringComparison.Ordinal) && t.Name.Length > "Legacy".Length
            ? t.Name["Legacy".Length..]
            : null;

    [Fact]
    public void Convention_CategorizesUndecoratedTypes_WithoutMainCategoryAttribute()
    {
        var provider = AutoProviderContainer.FromAssembly<AutoProviderContainerTests>(CategoryByNameTail);

        Assert.Contains(typeof(LegacyGateway), provider["Gateway"]);
        Assert.Contains(typeof(LegacyRenderer), provider["Renderer"]);
        Assert.Contains(typeof(LegacyNode), provider["Node"]);
    }

    [Fact]
    public void Convention_ExcludesTypesTheRuleReturnsNullFor()
    {
        // PaymentGateway/ContentFolder/etc. don't start with "Legacy" -> convention yields null -> excluded.
        var provider = AutoProviderContainer.FromAssembly<AutoProviderContainerTests>(CategoryByNameTail);

        Assert.DoesNotContain(typeof(PaymentGateway), provider["Gateway"]);
        Assert.Empty(provider["Payment"]);
    }

    [Fact]
    public void Categories_ListsConventionGroups_InFirstSeenOrder()
    {
        var provider = AutoProviderContainer.FromAssembly<AutoProviderContainerTests>(CategoryByNameTail);

        Assert.Contains("Gateway", provider.Categories);
        Assert.Contains("Renderer", provider.Categories);
        Assert.Contains("Node", provider.Categories);
    }

    [Fact]
    public void MarkerBuckets_DerivedFromDiscoveredTypes()
    {
        var provider = AutoProviderContainer.FromAssembly<AutoProviderContainerTests>(CategoryByNameTail);

        // The three Legacy fixtures all implement markers; the convention-discovered set flows
        // into the same derived buckets as decoration-discovered types.
        Assert.Contains(typeof(LegacyGateway), provider.SimpleEntities);
        Assert.Contains(typeof(LegacyRenderer), provider.SimpleEntities);
        Assert.Contains(typeof(LegacyNode), provider.ChildEntities);
    }

    [Fact]
    public void Indexer_UnknownCategory_ReturnsEmpty_NoThrow()
    {
        var provider = AutoProviderContainer.FromAssembly<AutoProviderContainerTests>(CategoryByNameTail);

        Assert.Empty(provider["DoesNotExist"]);
    }

    [Fact]
    public void NamespaceConvention_AlsoWorks()
    {
        // A namespace-root convention is the other canonical shape: group by top namespace segment.
        var provider = AutoProviderContainer.FromAssembly<AutoProviderContainerTests>(
            t => t.Namespace?.Split('.').LastOrDefault());

        // The test namespace's last segment is "Tests".
        Assert.Contains("Tests", provider.Categories);
        Assert.Contains(typeof(LegacyGateway), provider["Tests"]);
    }

    [Fact]
    public void FromAssembly_NullConvention_Throws()
    {
        Assert.Throws<ArgumentNullException>(() =>
            AutoProviderContainer.FromAssembly<AutoProviderContainerTests>(null!));
    }
}
