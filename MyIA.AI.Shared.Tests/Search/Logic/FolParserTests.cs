using MyIA.AI.Shared.Search.Logic.FirstOrder;
using Xunit;

namespace MyIA.AI.Shared.Tests.Search.Logic;

/// <summary>
/// Tests du parseur du premier ordre (EPIC #7265, volet B2 tranche 2, issue #24320).
/// </summary>
public sealed class FolParserTests
{
    [Fact]
    public void Atome_DeuxConstantes_RendLePredicat()
    {
        FolFormula.Predicate atom = Assert.IsType<FolFormula.Predicate>(FolParser.Parse("Pere(Armand, Cedric)"));

        Assert.Equal("Pere", atom.Name);
        Assert.Equal(2, atom.Arguments.Count);
        Assert.Equal("Armand", Assert.IsType<FolTerm.Constant>(atom.Arguments[0]).Name);
        Assert.Equal("Cedric", Assert.IsType<FolTerm.Constant>(atom.Arguments[1]).Name);
    }

    /// <summary>Convention AIMA : minuscule initiale = variable, majuscule = constante.</summary>
    [Fact]
    public void ConventionDeCasse_MinusculeEstVariableMajusculeEstConstante()
    {
        FolFormula.Predicate atom = Assert.IsType<FolFormula.Predicate>(FolParser.Parse("Aime(x, Marie)"));

        Assert.Equal("x", Assert.IsType<FolTerm.Variable>(atom.Arguments[0]).Name);
        Assert.Equal("Marie", Assert.IsType<FolTerm.Constant>(atom.Arguments[1]).Name);
    }

    [Fact]
    public void TermeFonction_ApparaissantEnArgument()
    {
        FolFormula.Predicate atom = Assert.IsType<FolFormula.Predicate>(FolParser.Parse("Pere(Pere(Armand), Cedric)"));

        FolTerm.FunctionApplication function =
            Assert.IsType<FolTerm.FunctionApplication>(atom.Arguments[0]);
        Assert.Equal("Pere", function.Name);
        Assert.Single(function.Arguments);
    }

    [Fact]
    public void Quantificateur_PorteSurUneImplicationParenthesee()
    {
        FolFormula.ForAll quantified =
            Assert.IsType<FolFormula.ForAll>(FolParser.Parse("FORALL x (Homme(x) => Mortel(x))"));

        Assert.Equal("x", quantified.Variable);
        Assert.IsType<FolFormula.Implies>(quantified.Body);
    }

    [Fact]
    public void Quantificateurs_Emboites()
    {
        FolFormula formula = FolParser.Parse("EXISTS y (FORALL x (Aime(x, y)))");

        FolFormula.Exists outer = Assert.IsType<FolFormula.Exists>(formula);
        Assert.IsType<FolFormula.ForAll>(outer.Body);
    }

    /// <summary>Les synonymes <c>&amp; | ~ -&gt; &lt;-&gt;</c> sont acceptes comme AND OR NOT =&gt; &lt;=&gt;.</summary>
    [Fact]
    public void Synonymes_SontAcceptes()
    {
        Assert.IsType<FolFormula.And>(FolParser.Parse("P(A) & Q(B)"));
        Assert.IsType<FolFormula.Or>(FolParser.Parse("P(A) | Q(B)"));
        Assert.IsType<FolFormula.Not>(FolParser.Parse("~P(A)"));
        Assert.IsType<FolFormula.Implies>(FolParser.Parse("P(A) -> Q(B)"));
        Assert.IsType<FolFormula.Biconditional>(FolParser.Parse("P(A) <-> Q(B)"));
        Assert.IsType<FolFormula.And>(FolParser.Parse("P(A) AND Q(B)"));
        Assert.IsType<FolFormula.Or>(FolParser.Parse("P(A) OR Q(B)"));
        Assert.IsType<FolFormula.Not>(FolParser.Parse("NOT P(A)"));
    }

    [Fact]
    public void ConjonctionLiePlusFortQueLaDisjonction()
    {
        // P(A) | Q(B) & R(C) se lit P(A) | (Q(B) & R(C)).
        FolFormula.Or disjunction =
            Assert.IsType<FolFormula.Or>(FolParser.Parse("P(A) | Q(B) & R(C)"));

        Assert.IsType<FolFormula.Predicate>(disjunction.Left);
        Assert.IsType<FolFormula.And>(disjunction.Right);
    }

    [Fact]
    public void NegationLiePlusFortQueLaConjonction()
    {
        FolFormula.And conjunction =
            Assert.IsType<FolFormula.And>(FolParser.Parse("~P(A) & Q(B)"));

        Assert.IsType<FolFormula.Not>(conjunction.Left);
        Assert.IsType<FolFormula.Predicate>(conjunction.Right);
    }

    [Fact]
    public void ImplicationEstAssociativeADroite()
    {
        // P => Q => R se lit P => (Q => R).
        FolFormula.Implies outer =
            Assert.IsType<FolFormula.Implies>(FolParser.Parse("P(A) => Q(B) => R(C)"));

        Assert.IsType<FolFormula.Predicate>(outer.Left);
        Assert.IsType<FolFormula.Implies>(outer.Right);
    }

    [Fact]
    public void ParenthesesForcentLeGroupement()
    {
        FolFormula.And conjunction =
            Assert.IsType<FolFormula.And>(FolParser.Parse("(P(A) | Q(B)) & R(C)"));

        Assert.IsType<FolFormula.Or>(conjunction.Left);
        Assert.IsType<FolFormula.Predicate>(conjunction.Right);
    }

    [Fact]
    public void VariablesLibres_SontLesNonQuantifiees()
    {
        FolFormula formula = FolParser.Parse("Pere(x, Armand) & Aime(x, y)");

        Assert.Equal(
            new[] { "x", "y" },
            formula.FreeVariables().OrderBy(name => name, StringComparer.Ordinal).ToArray());
    }

    [Fact]
    public void VariablesQuantifiees_NeSontPasLibres()
    {
        FolFormula formula = FolParser.Parse("FORALL x (Pere(x, Armand))");

        Assert.Empty(formula.FreeVariables());
    }

    [Theory]
    [InlineData("Pere(Armand")]
    [InlineData("(P(A)")]
    [InlineData("FORALL X (P(X))")]
    [InlineData("p(a)")]
    [InlineData("P(A) Q(B)")]
    [InlineData("")]
    [InlineData("P(A) # Q(B)")]
    [InlineData("FORALL")]
    public void EntreeMalFormee_LeveUneErreurDeSyntaxe(string source)
    {
        Assert.ThrowsAny<Exception>(() => FolParser.Parse(source));
    }

    [Fact]
    public void ErreurDeSyntaxe_NommeLaPosition()
    {
        FormatException error = Assert.Throws<FormatException>(() => FolParser.Parse("P(A) # Q(B)"));

        Assert.Contains("position", error.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void VariableQuantifieeDoitEtreMinuscule()
    {
        // La convention AIMA distingue variables et constantes par la casse :
        // un FORALL sur une majuscule est refuse.
        FormatException error = Assert.Throws<FormatException>(() => FolParser.Parse("FORALL X (P(X))"));

        Assert.Contains("minuscule", error.Message, StringComparison.OrdinalIgnoreCase);
    }
}
