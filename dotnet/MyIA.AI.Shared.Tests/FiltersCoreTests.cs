using System.CodeDom;
using System.ComponentModel;
using MyIA.AI.ComponentModel.Filters;
using Xunit;

namespace MyIA.AI.Shared.Tests;

/// <summary>
/// Battery for the A3-T1 core layer of the metadata-driven filters port (EPIC #7265,
/// pépite #19088): the contracts (<see cref="IDescriptor"/>, <see cref="IFilter"/>), the
/// composition algebra (<see cref="FilterExpression"/>, <see cref="FilterInExpression"/>,
/// <see cref="OperatorFilterExp"/>) with its corrected edge branches, and the
/// comparers/sorters. The concrete reflective filters live in the stacked tranche and are
/// covered by <c>FiltersConcreteTests</c>.
/// </summary>
public class FiltersCoreTests
{
    private sealed class SampleItem
    {
        public string Name { get; set; } = "";
        public int Score { get; set; }
    }

    private static SampleItem Item(int score, string name = "a") =>
        new() { Name = name, Score = score };

    /// <summary>
    /// Test double for the core layer: <see cref="FilterExpression"/> composes
    /// <see cref="IFilter"/> instances, and the concrete reflective filters that fill that
    /// role in production belong to the stacked tranche (A3-T1.2). Keeping the double here
    /// is precisely what makes the two tranches independently testable — the core suite
    /// never depends on the consumer layer.
    /// </summary>
    private sealed class ProbeFilter : IFilter
    {
        private readonly bool _result;

        public ProbeFilter(bool result) => _result = result;

        public bool IsSimpleMatch => true;

        public bool Match<T>(T content) => _result;

        public CodeExpression GetCodeExpression() => new CodeBinaryOperatorExpression(
            new CodePrimitiveExpression(true),
            CodeBinaryOperatorType.ValueEquality,
            new CodePrimitiveExpression(true));

        public string GetArgs() => "probe";
    }

    // --- FilterExpression : sémantique And/Or left-to-right ---

    [Fact]
    public void FilterExpression_AllAnd_True()
    {
        var expr = new FilterExpression(
            OperatorFilterExp.And,
            new ProbeFilter(true),
            new ProbeFilter(true));
        Assert.True(expr.Match(Item(5)));
    }

    [Fact]
    public void FilterExpression_AndFailure_ShortCircuitsFalse()
    {
        var expr = new FilterExpression(
            OperatorFilterExp.And,
            new ProbeFilter(false),
            new ProbeFilter(true));
        Assert.False(expr.Match(Item(5)));
    }

    [Fact]
    public void FilterExpression_OrSuccess_ShortCircuitsTrue()
    {
        var expr = new FilterExpression(
            OperatorFilterExp.Or,
            new ProbeFilter(true),
            new ProbeFilter(false));
        Assert.True(expr.Match(Item(5)));
    }

    [Fact]
    public void FilterExpression_OrNoMatch_False()
    {
        var expr = new FilterExpression(
            OperatorFilterExp.Or,
            new ProbeFilter(false),
            new ProbeFilter(false));
        Assert.False(expr.Match(Item(5)));
    }

    [Fact]
    public void FilterExpression_SingleFilterCtor_WrapsWithAnd()
    {
        var expr = new FilterExpression(new ProbeFilter(true));
        Assert.Single(expr);
        Assert.Equal(OperatorFilterExp.And, expr[0].OperatorFilterExp);
        Assert.True(expr.Match(Item(5)));
    }

    [Fact]
    public void FilterExpression_Empty_MatchFailsClosed_CodeExpressionIsIdentity()
    {
        // Match on empty: false — the deterministic VB original behavior (loop never
        // runs, toReturn stays false), kept as fail-closed. GetCodeExpression on empty:
        // true — identity of the And-chain (the VB original indexed this(0) here, the
        // corrected branch). The asymmetry between the two surfaces is inherited and
        // documented in the PR body.
        var expr = new FilterExpression();
        Assert.False(expr.Match(Item(5)));
        var primitive = Assert.IsType<CodePrimitiveExpression>(expr.GetCodeExpression());
        Assert.Equal(true, primitive.Value);
    }

    [Fact]
    public void FilterExpression_Single_CodeExpression_DelegatesToFilter()
    {
        // Corrected branch: single filter => that filter's expression (VB returned True).
        var inner = new ProbeFilter(true);
        var expr = new FilterExpression(inner);
        var binary = Assert.IsType<CodeBinaryOperatorExpression>(expr.GetCodeExpression());
        Assert.Equal(CodeBinaryOperatorType.ValueEquality, binary.Operator);
    }

    [Fact]
    public void FilterExpression_Multiple_CodeExpression_BuildsBinaryChain()
    {
        var expr = new FilterExpression(
            OperatorFilterExp.And,
            new ProbeFilter(true),
            new ProbeFilter(true));
        var binary = Assert.IsType<CodeBinaryOperatorExpression>(expr.GetCodeExpression());
        Assert.Equal(CodeBinaryOperatorType.BooleanAnd, binary.Operator);
        Assert.IsType<CodeBinaryOperatorExpression>(binary.Left);
        Assert.IsType<CodeBinaryOperatorExpression>(binary.Right);
    }

    [Fact]
    public void FilterExpression_IsSimpleMatch_And_GetArgs()
    {
        var expr = new FilterExpression(
            OperatorFilterExp.And,
            new ProbeFilter(true),
            new ProbeFilter(true));
        Assert.True(expr.IsSimpleMatch);
        var args = expr.GetArgs();
        Assert.StartsWith("fe", args);
        Assert.EndsWith("-fe", args);
        Assert.Contains("-f-0-And-", args);
        Assert.Contains("-f-1-And-", args);
    }

    [Fact]
    public void FilterExpression_ListCtor()
    {
        var list = new List<FilterInExpression>
        {
            new(new ProbeFilter(true), OperatorFilterExp.And),
        };
        var expr = new FilterExpression(list);
        Assert.True(expr.Match(Item(5)));
    }

    // --- Comparateurs et sorters ---

    [Fact]
    public void SimpleComparer_NonGeneric_Property_Ascending_Descending()
    {
        var asc = new SimpleComparer("Score", ListSortDirection.Ascending);
        var desc = new SimpleComparer("Score", ListSortDirection.Descending);
        Assert.True(asc.Compare(Item(1), Item(2)) < 0);
        Assert.True(desc.Compare(Item(1), Item(2)) > 0);
    }

    [Fact]
    public void SimpleComparer_NonGeneric_BothNull_Zero()
    {
        var comparer = new SimpleComparer("Score", ListSortDirection.Ascending);
        Assert.Equal(0, comparer.Compare(null, null));
    }

    [Fact]
    public void SimpleComparer_NonGeneric_MissingProperty_FallsBackToWholeObject()
    {
        // No "Score" property on plain string: falls back to IComparable on x.
        var comparer = new SimpleComparer("Score", ListSortDirection.Ascending);
        Assert.True(comparer.Compare("a", "b") < 0);
    }

    [Fact]
    public void SimpleComparer_Generic_Delegates()
    {
        var comparer = new SimpleComparer<int>(
            (a, b) => b.CompareTo(a), // inverted comparison
            a => a);
        Assert.True(comparer.Compare(1, 2) > 0);
        Assert.True(comparer.Equals(2, 2));
        Assert.Equal(7, comparer.GetHashCode(7));
    }

    [Fact]
    public void SimpleComparer_Generic_PropertyBased_EqualityAndHash()
    {
        var comparer = new SimpleComparer<SampleItem>("Name", ListSortDirection.Ascending);
        var a = new SampleItem { Name = "same" };
        var b = new SampleItem { Name = "same" };
        Assert.True(comparer.Equals(a, b));
        Assert.Equal(comparer.GetHashCode(a), comparer.GetHashCode(b));
        Assert.Equal("same".GetHashCode(), comparer.GetHashCode(a));
    }

    [Fact]
    public void SimpleSorter_Ascending_Descending()
    {
        var asc = new SimpleSorter<int>("Score", ListSortDirection.Ascending);
        var desc = new SimpleSorter<int>("Score", ListSortDirection.Descending);
        Assert.True(asc.Compare(1, 2) < 0);
        Assert.True(desc.Compare(1, 2) > 0);
    }

    [Fact]
    public void CustomSorter_WrapsComparison()
    {
        var sorter = new CustomSorter<string>((x, y) => y.Length - x.Length);
        Assert.True(sorter.Compare("aaa", "a") < 0);
    }

    [Fact]
    public void InvertComparer_NegatesSource()
    {
        var invert = new InvertComparer<int>(new SimpleSorter<int>("Score", ListSortDirection.Ascending));
        Assert.True(invert.Compare(1, 2) > 0);
    }

    [Fact]
    public void InvariantCharComparer_CaseInsensitive()
    {
        var comparer = new InvariantCharComparer();
        Assert.True(comparer.Equals('a', 'A'));
        Assert.False(comparer.Equals('a', 'b'));
        Assert.Equal(comparer.GetHashCode('a'), comparer.GetHashCode('A'));
    }
}
