using System.CodeDom;
using MyIA.AI.ComponentModel.Filters;
using Xunit;

namespace MyIA.AI.Shared.Tests;

/// <summary>
/// Battery for the A3-T1 concrete filters (EPIC #7265, pépite #19088): the reflective
/// filters that consume the core contracts — <see cref="SimpleFilter{T}"/>,
/// <see cref="PredicateFilter{T}"/>, <see cref="ListFilter{T}"/> — including the corrected
/// semantics documented in the PR body (ListFilter subject/element bugs, empty-list vacuous
/// truth) and their composition inside a <see cref="FilterExpression"/>. The contracts, the
/// composition algebra and the comparers live in the stacked tranche and are covered by
/// <c>FiltersCoreTests</c>.
/// </summary>
public class FiltersConcreteTests
{
    private sealed class SampleTag
    {
        public string Label { get; set; } = "";
    }

    private sealed class SampleItem
    {
        public string Name { get; set; } = "";
        public int Score { get; set; }
        public List<SampleTag> Tags { get; set; } = new();
    }

    private static SampleItem Item(int score, string name = "a") =>
        new() { Name = name, Score = score };

    // --- SimpleFilter : chaque opérateur ---

    [Theory]
    [InlineData(CodeBinaryOperatorType.ValueEquality, 5, 5, true)]
    [InlineData(CodeBinaryOperatorType.ValueEquality, 5, 6, false)]
    [InlineData(CodeBinaryOperatorType.GreaterThan, 7, 5, true)]
    [InlineData(CodeBinaryOperatorType.GreaterThan, 5, 5, false)]
    [InlineData(CodeBinaryOperatorType.GreaterThanOrEqual, 5, 5, true)]
    [InlineData(CodeBinaryOperatorType.GreaterThanOrEqual, 4, 5, false)]
    [InlineData(CodeBinaryOperatorType.LessThan, 3, 5, true)]
    [InlineData(CodeBinaryOperatorType.LessThan, 5, 5, false)]
    [InlineData(CodeBinaryOperatorType.LessThanOrEqual, 5, 5, true)]
    [InlineData(CodeBinaryOperatorType.LessThanOrEqual, 6, 5, false)]
    public void SimpleFilter_Operators(CodeBinaryOperatorType op, int score, int value, bool expected)
    {
        var filter = new SimpleFilter<int>("Score", op, value);
        Assert.Equal(expected, filter.Match(Item(score)));
    }

    [Fact]
    public void SimpleFilter_IdentityEquality_UsesEqualsNotCompareTo()
    {
        // IdentityEquality on strings: Equals, so two distinct-but-equal strings match.
        var filter = new SimpleFilter<string>("Name", CodeBinaryOperatorType.IdentityEquality, "alpha");
        Assert.True(filter.Match(new SampleItem { Name = "alpha" }));
        Assert.False(filter.Match(new SampleItem { Name = "beta" }));
    }

    [Fact]
    public void SimpleFilter_UnsupportedOperator_ThrowsNotSupported()
    {
        var filter = new SimpleFilter<int>("Score", CodeBinaryOperatorType.Modulus, 1);
        Assert.Throws<NotSupportedException>(() => filter.Match(Item(5)));
    }

    [Fact]
    public void SimpleFilter_MissingProperty_ThrowsKeyNotFound()
    {
        var filter = new SimpleFilter<int>("NoSuchProp", CodeBinaryOperatorType.ValueEquality, 1);
        Assert.Throws<KeyNotFoundException>(() => filter.Match(Item(5)));
    }

    [Fact]
    public void SimpleFilter_DescriptorShape()
    {
        var filter = new SimpleFilter<int>("Score", CodeBinaryOperatorType.GreaterThan, 3);
        Assert.StartsWith("fScore-GreaterThan-3", filter.GetArgs());
        var expr = Assert.IsType<CodeBinaryOperatorExpression>(filter.GetCodeExpression());
        Assert.Equal(CodeBinaryOperatorType.GreaterThan, expr.Operator);
        var propRef = Assert.IsType<CodePropertyReferenceExpression>(expr.Left);
        Assert.Equal("Score", propRef.PropertyName);
        var primitive = Assert.IsType<CodePrimitiveExpression>(expr.Right);
        Assert.Equal(3, primitive.Value);
    }

    // --- PredicateFilter ---

    [Fact]
    public void PredicateFilter_MatchesPropertyThroughPredicate()
    {
        var filter = new PredicateFilter<int>("Score", s => s > 10);
        Assert.True(filter.Match(Item(11)));
        Assert.False(filter.Match(Item(10)));
    }

    [Fact]
    public void PredicateFilter_CodeExpressionNotSupported()
        => Assert.Throws<NotSupportedException>(
            () => new PredicateFilter<int>("Score", _ => true).GetCodeExpression());

    // --- ListFilter : bugs d'origine corrigés ---

    private static IFilter LabelFilter(string label) =>
        new PredicateFilter<string>("Label", l => l == label);

    [Fact]
    public void ListFilter_Any_OneElementMatches()
    {
        var item = new SampleItem
        {
            Tags = new() { new() { Label = "x" }, new() { Label = "y" } },
        };
        var filter = new ListFilter<SampleTag>("Tags", LabelFilter("y"), ScopeOperator.Any);
        Assert.True(filter.Match(item));
    }

    [Fact]
    public void ListFilter_Any_NoElementMatches()
    {
        var item = new SampleItem
        {
            Tags = new() { new() { Label = "x" }, new() { Label = "z" } },
        };
        var filter = new ListFilter<SampleTag>("Tags", LabelFilter("y"), ScopeOperator.Any);
        Assert.False(filter.Match(item));
    }

    [Fact]
    public void ListFilter_All_EveryElementMatches()
    {
        var item = new SampleItem
        {
            Tags = new() { new() { Label = "y" }, new() { Label = "y" } },
        };
        var filter = new ListFilter<SampleTag>("Tags", LabelFilter("y"), ScopeOperator.All);
        Assert.True(filter.Match(item));
    }

    [Fact]
    public void ListFilter_All_OneElementFails()
    {
        var item = new SampleItem
        {
            Tags = new() { new() { Label = "y" }, new() { Label = "x" } },
        };
        var filter = new ListFilter<SampleTag>("Tags", LabelFilter("y"), ScopeOperator.All);
        Assert.False(filter.Match(item));
    }

    [Fact]
    public void ListFilter_EmptyList_AnyFalse_AllTrue()
    {
        // Corrected: empty list satisfies All (vacuous truth) — the VB original
        // returned the default False for both scopes.
        var item = new SampleItem { Tags = new() };
        Assert.False(new ListFilter<SampleTag>("Tags", LabelFilter("y"), ScopeOperator.Any).Match(item));
        Assert.True(new ListFilter<SampleTag>("Tags", LabelFilter("y"), ScopeOperator.All).Match(item));
    }

    [Fact]
    public void ListFilter_InnerFilterReceives_Elements_NotContent()
    {
        // Regression guard for the corrected bug: the inner filter must see each list
        // element (its Label property), not the outer content object (no Label on SampleItem).
        var item = new SampleItem
        {
            Name = "outer",
            Tags = new() { new() { Label = "outer" } },
        };
        var filter = new ListFilter<SampleTag>("Tags", LabelFilter("outer"), ScopeOperator.All);
        Assert.True(filter.Match(item));
    }

    [Fact]
    public void ListFilter_GetArgs_Shape()
    {
        var filter = new ListFilter<SampleTag>("Tags", LabelFilter("y"), ScopeOperator.Any);
        Assert.StartsWith("fAny-f", filter.GetArgs());
    }

    // --- Composition : expression imbriquant ListFilter ---

    [Fact]
    public void Composition_ListFilter_Inside_FilterExpression()
    {
        var item = new SampleItem
        {
            Score = 5,
            Tags = new() { new() { Label = "y" } },
        };
        var expr = new FilterExpression(
            OperatorFilterExp.And,
            new SimpleFilter<int>("Score", CodeBinaryOperatorType.ValueEquality, 5),
            new ListFilter<SampleTag>("Tags", LabelFilter("y"), ScopeOperator.Any));
        Assert.True(expr.Match(item));
        Assert.True(expr.IsSimpleMatch);
    }
}
