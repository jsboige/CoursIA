using System;
using System.Collections.Generic;
using System.Linq;
using Flee.PublicTypes;
using MyIA.AI.Shared.Search.Csp;
using Xunit;
using Xunit.Abstractions;

namespace MyIA.AI.Shared.Tests.Csp;

/// <summary>
/// Tests de la contrainte Flee du noyau CSP (EPIC #7265, pepite B1).
/// Ce que ces tests doivent etablir, et que les tests du solveur n'etablissent pas :
/// une contrainte <b>arbitraire</b> — n-aire, ecrite en texte — change le verdict de
/// la recherche sans qu'aucun code hote soit recompile.
/// </summary>
public sealed class FleeConstraintTests
{
    private readonly ITestOutputHelper _output;

    public FleeConstraintTests(ITestOutputHelper output) => _output = output;

    private static Variable Integers(string name, params int[] values) =>
        new(name, Domain.Of(values.Cast<object?>().ToArray()));

    /// <summary>
    /// Le point de la pepite : une contrainte sur <b>trois</b> variables, que
    /// <see cref="BinaryConstraint"/> ne sait pas exprimer.
    /// </summary>
    [Fact]
    public void TernaryRuleBindsEveryVariableOfItsScope()
    {
        Variable a = Integers("A", 0, 1, 2, 3, 4, 5);
        Variable b = Integers("B", 0, 1, 2, 3, 4, 5);
        Variable c = Integers("C", 0, 1, 2, 3, 4, 5);

        FleeConstraint constraint = new("A + B + C <= 10", new[] { a, b, c }, "somme-bornee");

        Assignment satisfied = new();
        satisfied.Add(a, 3);
        satisfied.Add(b, 3);
        satisfied.Add(c, 4);
        Assert.True(constraint.IsSatisfied(satisfied));

        Assignment violated = new();
        violated.Add(a, 4);
        violated.Add(b, 4);
        violated.Add(c, 4);
        Assert.False(constraint.IsSatisfied(violated));

        _output.WriteLine($"{constraint}: 3+3+4 -> true, 4+4+4 -> false");
    }

    /// <summary>Une affectation partielle est satisfaite : contrat de <see cref="IConstraint"/> pendant la recherche.</summary>
    [Fact]
    public void PartialAssignmentIsAlwaysSatisfied()
    {
        Variable a = Integers("A", 0, 9);
        Variable b = Integers("B", 0, 9);
        Variable c = Integers("C", 0, 9);

        FleeConstraint constraint = new("A + B + C <= 10", new[] { a, b, c });

        Assignment partial = new();
        partial.Add(a, 9);
        partial.Add(b, 9);

        // 9 + 9 + C depasse la borne pour tout C du domaine : la contrainte n'est
        // pourtant pas encore evaluable, et ne doit donc pas condamner la branche.
        Assert.True(constraint.IsSatisfied(partial));
    }

    /// <summary>Les operateurs de Flee sont ceux de VB : difference par <c>&lt;&gt;</c>, pas par <c>!=</c>.</summary>
    [Fact]
    public void DifferenceRuleUsesFleeOperators()
    {
        Variable left = new("X", Domain.Of("rouge", "vert"));
        Variable right = new("Y", Domain.Of("rouge", "vert"));

        FleeConstraint constraint = new("X <> Y", new[] { left, right });

        Assignment distinct = new();
        distinct.Add(left, "rouge");
        distinct.Add(right, "vert");
        Assert.True(constraint.IsSatisfied(distinct));

        Assignment equal = new();
        equal.Add(left, "rouge");
        equal.Add(right, "rouge");
        Assert.False(constraint.IsSatisfied(equal));
    }

    /// <summary>
    /// Le test qui fait la difference entre "ca compile" et "ca sert" : un solveur
    /// reel resout un probleme reel sous une contrainte Flee, et la solution rendue
    /// satisfait la regle.
    /// </summary>
    [Fact]
    public void SolverSolvesUnderAFleeConstraint()
    {
        Variable a = Integers("A", 0, 1, 2, 3);
        Variable b = Integers("B", 0, 1, 2, 3);
        Variable c = Integers("C", 0, 1, 2, 3);

        CspProblem problem = CspProblem.CreateCsp(a, b, c);
        problem.AddConstraint(new FleeConstraint("A < B and B < C", new[] { a, b, c }, "ordre-strict"));

        BacktrackingSolver solver = new() { Selection = VariableSelection.MinimumRemainingValues };
        Assignment? solution = solver.Solve(problem);

        Assert.NotNull(solution);
        Assert.Equal(0, solution!.Get(a));
        Assert.Equal(1, solution.Get(b));
        Assert.Equal(2, solution.Get(c));

        // La meme contrainte, evaluee une seconde fois, doit rendre le meme verdict :
        // le contexte Flee est reutilise d'un noeud a l'autre, pas recompile.
        Assert.True(problem.Constraints[0].IsSatisfied(solution));

        _output.WriteLine($"solution A={solution.Get(a)} B={solution.Get(b)} C={solution.Get(c)} en {solver.NodeCount} noeuds");
    }

    /// <summary>Une regle qui nomme une variable absente du scope echoue a la compilation, pas a l'evaluation.</summary>
    [Fact]
    public void UnknownVariableNameFailsAtCompileTime()
    {
        Variable a = Integers("A", 0, 1);
        Variable b = Integers("B", 0, 1);

        Assert.Throws<ExpressionCompileException>(() => new FleeConstraint("A < Z", new[] { a, b }));
    }

    /// <summary>Un nom de variable non identifiable est refuse : sans garde, la variable serait inatteignable et la contrainte toujours vraie.</summary>
    [Fact]
    public void NonIdentifiableVariableNameIsRejected()
    {
        Variable hyphenated = new("X-Y", Domain.Of(0, 1));

        ArgumentException error = Assert.Throws<ArgumentException>(
            () => new FleeConstraint("X-Y > 0", new[] { hyphenated }));

        Assert.Contains("X-Y", error.Message, StringComparison.Ordinal);
    }

    /// <summary>Regle vide : refusee, jamais compilee en "toujours vrai".</summary>
    [Fact]
    public void EmptyRuleIsRejected()
    {
        Variable a = Integers("A", 0, 1);

        Assert.Throws<ArgumentNullException>(() => new FleeConstraint("   ", new[] { a }));
    }

    /// <summary>Scope vide : refuse, une contrainte sans variable n'a pas de sens en CSP.</summary>
    [Fact]
    public void EmptyScopeIsRejected()
    {
        Assert.Throws<ArgumentException>(() => new FleeConstraint("1 = 1", Array.Empty<Variable>()));
    }

    /// <summary>Le nom de trace par defaut porte la regle, pour que les journaux du solveur restent lisibles.</summary>
    [Fact]
    public void DefaultNameCarriesTheRule()
    {
        Variable a = Integers("A", 0, 1);

        FleeConstraint constraint = new("A > 0", new[] { a });

        Assert.Contains("A > 0", constraint.Name, StringComparison.Ordinal);
        Assert.Equal("A > 0", constraint.Rule);
        Assert.Single((IEnumerable<Variable>)constraint.Scope);
    }
}
