using System;
using System.Collections.Generic;
using System.Linq;
using MyIA.AI.Shared.Search.Csp;
using Xunit;
using Xunit.Abstractions;

namespace MyIA.AI.Shared.Tests.Csp;

/// <summary>
/// Tests du noyau CSP porte depuis AIMA (EPIC #7265, pepite B1).
/// Les problemes de reference sont ceux de la litterature et de la serie
/// <c>Search/Applications/CSP</c> : coloration de carte, n-dames.
/// </summary>
public sealed class BacktrackingSolverTests
{
    private readonly ITestOutputHelper _output;

    public BacktrackingSolverTests(ITestOutputHelper output) => _output = output;

    private static readonly string[] Colours = { "rouge", "vert", "bleu" };

    /// <summary>Carte d'Australie : le probleme canonique du chapitre CSP d'AIMA.</summary>
    private static CspProblem Australia(IEnumerable<string> colours)
    {
        Domain domain = Domain.Of(colours.Cast<object?>().ToArray());

        Variable wa = new("WA", domain.Copy());
        Variable nt = new("NT", domain.Copy());
        Variable sa = new("SA", domain.Copy());
        Variable q = new("Q", domain.Copy());
        Variable nsw = new("NSW", domain.Copy());
        Variable v = new("V", domain.Copy());
        Variable t = new("T", domain.Copy());

        CspProblem problem = CspProblem.CreateCsp(wa, nt, sa, q, nsw, v, t);

        // Voisinages de la carte d'Australie (AIMA, figure 6.1).
        problem.AddConstraint(Constraints.NotEqual(wa, nt));
        problem.AddConstraint(Constraints.NotEqual(wa, sa));
        problem.AddConstraint(Constraints.NotEqual(nt, sa));
        problem.AddConstraint(Constraints.NotEqual(nt, q));
        problem.AddConstraint(Constraints.NotEqual(sa, q));
        problem.AddConstraint(Constraints.NotEqual(sa, nsw));
        problem.AddConstraint(Constraints.NotEqual(sa, v));
        problem.AddConstraint(Constraints.NotEqual(q, nsw));
        problem.AddConstraint(Constraints.NotEqual(nsw, v));

        return problem;
    }

    /// <summary>N-dames en CSP : une variable par colonne, une contrainte par paire de reines.</summary>
    private static CspProblem Queens(int size)
    {
        object?[] rows = Enumerable.Range(0, size).Cast<object?>().ToArray();

        Variable[] columns = Enumerable.Range(0, size)
            .Select(column => new Variable($"C{column}", Domain.Of(rows)))
            .ToArray();

        CspProblem problem = CspProblem.CreateCsp(columns);

        for (int first = 0; first < size; first++)
        {
            for (int second = first + 1; second < size; second++)
            {
                int distance = second - first;
                Variable left = columns[first];
                Variable right = columns[second];

                problem.AddConstraint(Constraints.Binary(
                    left,
                    right,
                    (rowLeft, rowRight) =>
                    {
                        int a = Convert.ToInt32(rowLeft);
                        int b = Convert.ToInt32(rowRight);
                        return a != b && Math.Abs(a - b) != distance;
                    },
                    $"dames-{first}-{second}"));
            }
        }

        return problem;
    }

    private static void AssertConsistentColouring(CspProblem problem, Assignment solution)
    {
        Assert.True(solution.IsComplete(problem.Variables), "La solution doit affecter toutes les variables.");
        Assert.True(solution.IsConsistent(problem.Constraints), "Aucune contrainte ne doit etre violee.");
    }

    [Fact]
    public void AustraliaWithThreeColoursShouldReturnAConsistentSolution()
    {
        CspProblem problem = Australia(Colours);
        BacktrackingSolver solver = new();

        Assignment? solution = solver.Solve(problem);

        Assert.NotNull(solution);
        AssertConsistentColouring(problem, solution!);
        _output.WriteLine($"Solution : {solution} | noeuds={solver.NodeCount} retours={solver.BacktrackCount}");
    }

    [Fact]
    public void AustraliaWithTwoColoursShouldBeUnsatisfiable()
    {
        CspProblem problem = Australia(new[] { "rouge", "vert" });
        BacktrackingSolver solver = new();

        // WA-NT-SA forme un triangle : trois sommets deux a deux adjacents ne se
        // colorent pas avec deux couleurs. L'insatisfiabilite est structurelle.
        Assignment? solution = solver.Solve(problem);

        Assert.Null(solution);
        Assert.True(solver.BacktrackCount > 0, "Une recherche infructueuse doit avoir remonte au moins une fois.");
    }

    [Theory]
    [InlineData(VariableSelection.DefaultOrder)]
    [InlineData(VariableSelection.MinimumRemainingValues)]
    [InlineData(VariableSelection.MinimumRemainingValuesDegree)]
    public void EightQueensSolutionShouldPlaceEightNonAttackingQueens(VariableSelection selection)
    {
        CspProblem problem = Queens(8);
        BacktrackingSolver solver = new() { Selection = selection };

        Assignment? solution = solver.Solve(problem);

        Assert.NotNull(solution);
        AssertConsistentColouring(problem, solution!);

        int[] rows = problem.Variables.Select(variable => Convert.ToInt32(solution!.Get(variable))).ToArray();
        Assert.Equal(8, rows.Distinct().Count());
        _output.WriteLine($"{selection} : {string.Join(",", rows)} | noeuds={solver.NodeCount} retours={solver.BacktrackCount}");
    }

    /// <summary>
    /// Sans inference, tous les domaines du probleme gardent la meme taille :
    /// MRV n'a rien a discriminer et les deux ordres explores le meme arbre.
    /// Ce test fixe ce cas limite — il rend la mesure du test suivant
    /// interpretable (le gain vient de l'inference, pas du probleme).
    /// </summary>
    [Fact]
    public void WithoutInferenceMinimumRemainingValuesTiesWithDefaultOrder()
    {
        CspProblem problem = Queens(8);

        BacktrackingSolver baseline = new() { Selection = VariableSelection.DefaultOrder };
        BacktrackingSolver heuristic = new() { Selection = VariableSelection.MinimumRemainingValues };

        Assert.NotNull(baseline.Solve(problem));
        Assert.NotNull(heuristic.Solve(problem));

        _output.WriteLine($"sans inference, 8 dames : ordre par defaut={baseline.NodeCount} noeuds ; MRV={heuristic.NodeCount} noeuds");
        Assert.Equal(baseline.NodeCount, heuristic.NodeCount);
    }

    /// <summary>
    /// Avec forward checking, les domaines retrecissent : MRV choisit alors la
    /// variable la plus contrainte et doit explorer strictement moins de noeuds
    /// que l'ordre de declaration. C'est la mesure qui rend l'heuristique
    /// falsifiable plutot qu'affirmee.
    /// </summary>
    [Fact]
    public void MinimumRemainingValuesShouldExploreFewerNodesThanDefaultOrderWithForwardChecking()
    {
        CspProblem problem = Queens(8);

        BacktrackingSolver baseline = new()
        {
            Selection = VariableSelection.DefaultOrder,
            Inference = InferenceStrategy.ForwardChecking,
        };
        BacktrackingSolver heuristic = new()
        {
            Selection = VariableSelection.MinimumRemainingValues,
            Inference = InferenceStrategy.ForwardChecking,
        };

        Assert.NotNull(baseline.Solve(problem));
        Assert.NotNull(heuristic.Solve(problem));

        _output.WriteLine($"avec forward checking, 8 dames : ordre par defaut={baseline.NodeCount} noeuds ; MRV={heuristic.NodeCount} noeuds");
        Assert.True(
            heuristic.NodeCount < baseline.NodeCount,
            $"MRV a explore {heuristic.NodeCount} noeuds contre {baseline.NodeCount} pour l'ordre par defaut.");
    }

    [Fact]
    public void ForwardCheckingShouldNotExploreMoreNodesThanNoInference()
    {
        CspProblem problem = Queens(8);

        BacktrackingSolver plain = new();
        BacktrackingSolver forwardChecking = new() { Inference = InferenceStrategy.ForwardChecking };

        Assert.NotNull(plain.Solve(problem));
        Assert.NotNull(forwardChecking.Solve(problem));

        _output.WriteLine($"sans inference={plain.NodeCount} noeuds ; forward checking={forwardChecking.NodeCount} noeuds");
        Assert.True(
            forwardChecking.NodeCount <= plain.NodeCount,
            $"Le forward checking a explore {forwardChecking.NodeCount} noeuds contre {plain.NodeCount} sans inference.");
    }

    [Fact]
    public void Ac3ShouldKeepTheProblemSolvableAndPruneTheSearch()
    {
        CspProblem satisfiable = Australia(Colours);
        BacktrackingSolver solver = new() { Inference = InferenceStrategy.Ac3 };

        Assignment? solution = solver.Solve(satisfiable);

        Assert.NotNull(solution);
        AssertConsistentColouring(satisfiable, solution!);

        // AC-3 ne doit pas retirer de solution : le probleme a deux couleurs
        // reste insatisfiable, il ne devient pas « resolu » par propagation.
        BacktrackingSolver unsatisfiableSolver = new() { Inference = InferenceStrategy.Ac3 };
        Assert.Null(unsatisfiableSolver.Solve(Australia(new[] { "rouge", "vert" })));

        _output.WriteLine($"AC-3 sur la carte d'Australie : noeuds={solver.NodeCount} retours={solver.BacktrackCount}");
    }

    [Fact]
    public void SolverShouldBeDeterministic()
    {
        CspProblem problem = Queens(6);

        Assignment first = new BacktrackingSolver().Solve(problem)!;
        Assignment second = new BacktrackingSolver().Solve(problem)!;

        Assert.Equal(first.ToString(), second.ToString());
    }

    [Fact]
    public void DomainShouldDeduplicateAndSupportRemoval()
    {
        Domain domain = Domain.Of(1, 2, 2, 3);

        Assert.Equal(3, domain.Size);
        Assert.True(domain.Contains(2));
        Assert.True(domain.Remove(2));
        Assert.False(domain.Remove(2));
        Assert.False(domain.Contains(2));
        Assert.Equal(2, domain.Size);
    }

    [Fact]
    public void ConstraintOnAnUndeclaredVariableShouldBeRejected()
    {
        Variable declared = new("X", Domain.Of(1, 2));
        Variable foreign = new("Y", Domain.Of(1, 2));
        CspProblem problem = CspProblem.CreateCsp(declared);

        ArgumentException error = Assert.Throws<ArgumentException>(
            () => problem.AddConstraint(Constraints.NotEqual(declared, foreign)));

        Assert.Contains("Y", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void PartialAssignmentShouldLeaveUnassignedConstraintsSatisfied()
    {
        Variable left = new("X", Domain.Of(1, 2));
        Variable right = new("Y", Domain.Of(1, 2));
        BinaryConstraint constraint = Constraints.NotEqual(left, right);
        Assignment assignment = new();

        // Une contrainte dont une variable manque est satisfaite : c'est ce qui
        // permet de tester la coherence pendant la descente.
        Assert.True(constraint.IsSatisfied(assignment));

        assignment.Add(left, 1);
        Assert.True(constraint.IsSatisfied(assignment));

        assignment.Add(right, 1);
        Assert.False(constraint.IsSatisfied(assignment));
    }
}
