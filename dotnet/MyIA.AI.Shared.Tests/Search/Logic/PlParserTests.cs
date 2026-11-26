using MyIA.AI.Shared.Search.Logic.Propositional;
using Xunit;

namespace MyIA.AI.Shared.Tests.Search.Logic;

/// <summary>
/// Tests du parseur propositionnel (EPIC #7265, volet B2 tranche 1, issue #23584).
/// </summary>
public sealed class PlParserTests
{
    [Fact]
    public void SymboleSeul_RendUnAtome()
    {
        PlAtom atom = Assert.IsType<PlAtom>(PlParser.Parse("P12"));

        Assert.Equal("P12", atom.Name);
    }

    /// <summary>
    /// La forme rendue par <c>ToString</c> est integralement parenthesee : c'est
    /// volontaire, elle doit rester relisible sans connaitre les priorites.
    /// </summary>
    [Theory]
    [InlineData("A & B", "(A & B)")]
    [InlineData("A | B", "(A | B)")]
    [InlineData("A => B", "(A => B)")]
    [InlineData("A <=> B", "(A <=> B)")]
    [InlineData("~A", "~A")]
    [InlineData("A -> B", "(A => B)")]
    [InlineData("A <-> B", "(A <=> B)")]
    [InlineData("!A", "~A")]
    public void Connecteurs_RendentLaFormeAttendue(string source, string expected)
    {
        PlFormula formula = PlParser.Parse(source);

        Assert.Equal(expected, formula.ToString());
    }

    [Fact]
    public void NegationLiePlusFortQueLaConjonction()
    {
        // ~A & B se lit (~A) & B, jamais ~(A & B) : la negation porte sur A seul.
        PlAnd conjunction = Assert.IsType<PlAnd>(PlParser.Parse("~A & B"));

        PlNot negation = Assert.IsType<PlNot>(conjunction.Left);
        Assert.Equal("A", Assert.IsType<PlAtom>(negation.Operand).Name);
        Assert.Equal("B", Assert.IsType<PlAtom>(conjunction.Right).Name);
    }

    [Fact]
    public void ConjonctionLiePlusFortQueLaDisjonction()
    {
        // A | B & C se lit A | (B & C).
        PlOr disjunction = Assert.IsType<PlOr>(PlParser.Parse("A | B & C"));

        Assert.Equal("A", Assert.IsType<PlAtom>(disjunction.Left).Name);
        Assert.IsType<PlAnd>(disjunction.Right);
    }

    [Fact]
    public void ImplicationLiePlusFortQueLEquivalence()
    {
        // A <=> B => C se lit A <=> (B => C).
        PlBiconditional biconditional = Assert.IsType<PlBiconditional>(PlParser.Parse("A <=> B => C"));

        Assert.Equal("A", Assert.IsType<PlAtom>(biconditional.Left).Name);
        Assert.IsType<PlImplies>(biconditional.Right);
    }

    [Fact]
    public void ImplicationEstAssociativeADroite()
    {
        // A => B => C se lit A => (B => C), et non (A => B) => C.
        PlImplies outer = Assert.IsType<PlImplies>(PlParser.Parse("A => B => C"));

        Assert.Equal("A", Assert.IsType<PlAtom>(outer.Left).Name);
        PlImplies inner = Assert.IsType<PlImplies>(outer.Right);
        Assert.Equal("B", Assert.IsType<PlAtom>(inner.Left).Name);
    }

    [Fact]
    public void ParenthesesForcentLeGroupement()
    {
        // (A | B) & C n'a pas la forme de A | (B & C).
        PlAnd conjunction = Assert.IsType<PlAnd>(PlParser.Parse("(A | B) & C"));

        Assert.IsType<PlOr>(conjunction.Left);
        Assert.Equal("C", Assert.IsType<PlAtom>(conjunction.Right).Name);
    }

    [Fact]
    public void Equivalence_EstVraieQuandLesDeuxCotesSontEgaux()
    {
        IReadOnlyDictionary<string, bool> assignment = new Dictionary<string, bool>
        {
            ["A"] = true,
            ["B"] = true,
        };

        Assert.True(PlParser.Parse("A <=> B").Evaluate(assignment));
        Assert.False(PlParser.Parse("A <=> B").Evaluate(new Dictionary<string, bool> { ["A"] = true, ["B"] = false }));
    }

    [Fact]
    public void Implication_EstVraieQuandLAntecedentEstFaux()
    {
        IReadOnlyDictionary<string, bool> assignment = new Dictionary<string, bool>
        {
            ["A"] = false,
            ["B"] = false,
        };

        Assert.True(PlParser.Parse("A => B").Evaluate(assignment));
    }

    [Fact]
    public void Symbols_RendLUnionSansDoublon()
    {
        PlFormula formula = PlParser.Parse("(A | B) & (B | ~C)");

        Assert.Equal(new[] { "A", "B", "C" }, formula.Symbols.OrderBy(s => s, StringComparer.Ordinal).ToArray());
    }

    [Theory]
    [InlineData("A &")]
    [InlineData("(A | B")]
    [InlineData("A | | B")]
    [InlineData("A # B")]
    [InlineData("")]
    public void EntreeMalFormee_LeveUneErreurDeSyntaxe(string source)
    {
        Assert.ThrowsAny<Exception>(() => PlParser.Parse(source));
    }

    [Fact]
    public void EntreeMalFormee_LevePlParseExceptionNommantLaPosition()
    {
        PlParseException error = Assert.Throws<PlParseException>(() => PlParser.Parse("A # B"));

        Assert.Contains("position", error.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void EvaluationPartielle_LeveAuLieuDeDeviner()
    {
        PlFormula formula = PlParser.Parse("A & B");
        Dictionary<string, bool> partial = new() { ["A"] = true };

        Assert.Throws<KeyNotFoundException>(() => formula.Evaluate(partial));
    }
}
