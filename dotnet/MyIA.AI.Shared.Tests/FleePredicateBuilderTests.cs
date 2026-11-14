using MyIA.AI.ComponentModel.Rules;
using Xunit;

namespace MyIA.AI.Shared.Tests;

// Exercises the FleePredicateBuilder (EPIC #7265, nugget B4 "le liant universel"): a string
// rule compiled once into a reusable predicate over an entity type. These tests are the
// substance Prong-B proof — the rule engine that #10161's notebook demonstrates live.

/// <summary>Fixture entity with scalar properties bound as rule variables.</summary>
internal sealed class Invoice
{
    public string Country { get; set; } = string.Empty;
    public decimal Amount { get; set; }
    public int Quantity { get; set; }
    public bool Vip { get; set; }
}

public class FleePredicateBuilderTests
{
    private static readonly Invoice[] Sample =
    {
        new() { Country = "FR", Amount = 1500m, Quantity = 2, Vip = false },
        new() { Country = "US", Amount = 2000m, Quantity = 1, Vip = false },
        new() { Country = "FR", Amount = 500m, Quantity = 5, Vip = false },
        new() { Country = "DE", Amount = 300m, Quantity = 1, Vip = true },
    };

    [Fact]
    public void Create_compiles_a_numeric_comparison_predicate()
    {
        var predicate = FleePredicateBuilder.Create<Invoice>("Amount > 1000");

        var matches = Sample.Where(predicate).ToArray();

        Assert.Equal(2, matches.Length);
        Assert.All(matches, i => Assert.True(i.Amount > 1000m));
    }

    [Fact]
    public void Create_compiles_a_combined_and_rule_with_string_equality()
    {
        // Flee syntax: `and` (word) + `=` (single equals), not && / ==.
        var predicate = FleePredicateBuilder.Create<Invoice>("Amount > 1000 and Country = \"FR\"");

        var matches = Sample.Where(predicate).ToArray();

        var single = Assert.Single(matches);
        Assert.Equal("FR", single.Country);
        Assert.Equal(1500m, single.Amount);
    }

    [Fact]
    public void Create_compiles_an_or_rule_with_a_boolean_property()
    {
        var predicate = FleePredicateBuilder.Create<Invoice>("Vip or Amount > 1000");

        var matches = Sample.Where(predicate).ToArray();

        Assert.Equal(3, matches.Length); // FR/1500, US/2000, DE/300 (Vip)
    }

    [Fact]
    public void Create_evaluates_many_entities_with_one_compiled_rule()
    {
        // The predicate is compiled once and evaluated per entity (variable mutation + eval).
        var predicate = FleePredicateBuilder.Create<Invoice>("Quantity >= 3");

        Assert.True(predicate(Sample[2]));   // FR/500/5
        Assert.False(predicate(Sample[0]));  // FR/1500/2
        Assert.False(predicate(Sample[3]));  // DE/300/1
    }

    [Fact]
    public void Create_supports_arithmetic_in_the_rule()
    {
        var predicate = FleePredicateBuilder.Create<Invoice>("Amount / Quantity > 600");

        var matches = Sample.Where(predicate).ToArray();

        // FR/1500/2 = 750 > 600 (match); US/2000/1 = 2000 (match); FR/500/5 = 100 (no); DE/300/1 (no)
        Assert.Equal(2, matches.Length);
    }

    [Fact]
    public void Create_throws_on_a_null_or_empty_rule()
    {
        Assert.Throws<ArgumentNullException>(() => FleePredicateBuilder.Create<Invoice>(""));
        Assert.Throws<ArgumentNullException>(() => FleePredicateBuilder.Create<Invoice>(null!));
    }

    [Fact]
    public void Create_throws_on_a_syntactically_invalid_rule()
    {
        // == is not Flee syntax (equality is a single =).
        var ex = Assert.ThrowsAny<Exception>(() => FleePredicateBuilder.Create<Invoice>("Amount == 1000"));
        Assert.Contains("Compile", ex.GetType().Name);
    }

    [Fact]
    public void Create_throws_on_a_rule_referencing_an_unknown_variable()
    {
        // "Total" is not a property of Invoice.
        Assert.ThrowsAny<Exception>(() => FleePredicateBuilder.Create<Invoice>("Total > 1000"));
    }
}
