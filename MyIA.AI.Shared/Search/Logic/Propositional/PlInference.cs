namespace MyIA.AI.Shared.Search.Logic.Propositional;

/// <summary>Procedure d'inference propositionnelle.</summary>
/// <remarks>
/// Les six procedures que le wrapper <c>PLKbInferProcedureInfo</c> du patrimoine
/// Aricie expose (EPIC #7265, volet B2 tranche 1, issue #23584).
/// </remarks>
public enum PlInferProcedure
{
    /// <summary>Deduction par table de verite. Complete, cout exponentiel.</summary>
    TTEntails,

    /// <summary>Refutation par resolution. Complete.</summary>
    Resolve,

    /// <summary>Deduction par DPLL : insatisfiabilite de la base jointe a la negation de la requete.</summary>
    DPLLEntails,

    /// <summary>Satisfiabilite de la base par DPLL.</summary>
    DPLLSatisfiable,

    /// <summary>Satisfiabilite de la base par recherche locale WalkSAT.</summary>
    WalkSatKb,

    /// <summary>Satisfiabilite de la base jointe a la requete, par WalkSAT.</summary>
    WalkSatPredicate,
}

/// <summary>Verdict d'une procedure.</summary>
public enum PlVerdict
{
    /// <summary>La question posee a une reponse affirmative.</summary>
    Yes,

    /// <summary>La question posee a une reponse negative.</summary>
    No,

    /// <summary>La procedure n'a pas conclu : WalkSAT ne prouve jamais une insatisfiabilite.</summary>
    Unknown,
}

/// <summary>Resultat d'une procedure : verdict, cout mesure, et modele s'il y en a un.</summary>
/// <param name="Procedure">Procedure appliquee.</param>
/// <param name="Question">Question posee, en clair, pour lever l'ambiguite du verdict.</param>
/// <param name="Verdict">Reponse.</param>
/// <param name="Steps">Pas consommes, dans l'unite nommee par <paramref name="StepUnit"/>.</param>
/// <param name="StepUnit">Unite de <paramref name="Steps"/> : c'est elle qui rend deux procedures comparables.</param>
/// <param name="Model">Affectation temoin quand la reponse est l'existence d'un modele.</param>
public sealed record PlInferenceResult(
    PlInferProcedure Procedure,
    string Question,
    PlVerdict Verdict,
    int Steps,
    string StepUnit,
    IReadOnlyDictionary<string, bool>? Model = null)
{
    /// <summary>Vrai si la procedure a conclu.</summary>
    public bool IsConclusive => Verdict != PlVerdict.Unknown;

    public override string ToString() =>
        $"{Procedure}: {Question} -> {Verdict} ({Steps} {StepUnit})";
}

/// <summary>
/// Les six procedures d'inference propositionnelle.
/// </summary>
/// <remarks>
/// <para>
/// Chaque procedure mesure son cout et le publie dans
/// <see cref="PlInferenceResult.Steps"/>, avec son unite. C'est ce qui les rend
/// falsifiables <i>entre elles</i> : sur une meme instance, elles doivent rendre le
/// meme verdict et des couts differents, dans des unites differentes.
/// </para>
/// <para>
/// Honnetete des verdicts : <see cref="PlVerdict.Unknown"/> existe pour WalkSAT.
/// Une recherche locale qui echoue n'a pas prouve l'insatisfiabilite ; rendre
/// <see cref="PlVerdict.No"/> dans ce cas serait une affirmation non mesuree.
/// </para>
/// </remarks>
public static class PlInference
{
    /// <summary>Nombre maximal de symboles enumerables par la table de verite.</summary>
    public const int MaxTruthTableSymbols = 20;

    /// <summary>Nombre maximal de resolvantes derivees avant abandon explicite.</summary>
    public const int MaxResolvents = 20000;

    /// <summary>Deduction par table de verite : la base implique-t-elle la requete ?</summary>
    public static PlInferenceResult TtEntails(
        PlKnowledgeBase knowledgeBase,
        PlFormula query,
        int maxSymbols = MaxTruthTableSymbols)
    {
        ArgumentNullException.ThrowIfNull(knowledgeBase);
        ArgumentNullException.ThrowIfNull(query);

        string[] symbols = knowledgeBase.Symbols
            .Concat(query.Symbols)
            .Distinct(StringComparer.Ordinal)
            .OrderBy(symbol => symbol, StringComparer.Ordinal)
            .ToArray();

        if (symbols.Length > maxSymbols)
        {
            throw new InvalidOperationException(
                $"La table de verite exigerait 2^{symbols.Length} lignes " +
                $"(borne : {maxSymbols} symboles, soit {1 << maxSymbols} lignes). " +
                "Utiliser Resolve ou DPLL pour cette instance.");
        }

        int rows = 1 << symbols.Length;
        Dictionary<string, bool> assignment = new(StringComparer.Ordinal);
        int rowsExamined = 0;

        for (int mask = 0; mask < rows; mask++)
        {
            for (int index = 0; index < symbols.Length; index++)
            {
                assignment[symbols[index]] = (mask & (1 << index)) != 0;
            }

            rowsExamined = mask + 1;

            if (!knowledgeBase.IsSatisfiedBy(assignment))
            {
                continue;
            }

            if (!query.Evaluate(assignment))
            {
                return new PlInferenceResult(
                    PlInferProcedure.TTEntails,
                    "KB |= requete",
                    PlVerdict.No,
                    rowsExamined,
                    "lignes de table de verite");
            }
        }

        return new PlInferenceResult(
            PlInferProcedure.TTEntails,
            "KB |= requete",
            PlVerdict.Yes,
            rowsExamined,
            "lignes de table de verite");
    }

    /// <summary>Refutation par resolution : la base jointe a la negation de la requete est-elle insatisfiable ?</summary>
    public static PlInferenceResult Resolve(
        PlKnowledgeBase knowledgeBase,
        PlFormula query,
        int maxResolvents = MaxResolvents)
    {
        ArgumentNullException.ThrowIfNull(knowledgeBase);
        ArgumentNullException.ThrowIfNull(query);

        List<PlClause> clauses = new(knowledgeBase.ToClauses());
        clauses.AddRange(PlCnf.ToClauses(new PlNot(query)));

        bool refuted = ResolveRefutation(clauses, maxResolvents, out int derived);

        return new PlInferenceResult(
            PlInferProcedure.Resolve,
            "KB |= requete",
            refuted ? PlVerdict.Yes : PlVerdict.No,
            derived,
            "resolvantes derivees");
    }

    /// <summary>Deduction par DPLL : insatisfiabilite de la base jointe a la negation de la requete.</summary>
    public static PlInferenceResult DpllEntails(PlKnowledgeBase knowledgeBase, PlFormula query)
    {
        ArgumentNullException.ThrowIfNull(knowledgeBase);
        ArgumentNullException.ThrowIfNull(query);

        List<PlClause> clauses = new(knowledgeBase.ToClauses());
        clauses.AddRange(PlCnf.ToClauses(new PlNot(query)));

        int decisions = 0;
        int propagations = 0;
        Dictionary<string, bool> assignment = new(StringComparer.Ordinal);
        bool satisfiable = Dpll(clauses, assignment, ref decisions, ref propagations);

        return new PlInferenceResult(
            PlInferProcedure.DPLLEntails,
            "KB |= requete",
            satisfiable ? PlVerdict.No : PlVerdict.Yes,
            decisions,
            "decisions DPLL");
    }

    /// <summary>Satisfiabilite de la base par DPLL.</summary>
    public static PlInferenceResult DpllSatisfiable(PlKnowledgeBase knowledgeBase)
    {
        ArgumentNullException.ThrowIfNull(knowledgeBase);

        List<PlClause> clauses = new(knowledgeBase.ToClauses());
        int decisions = 0;
        int propagations = 0;
        Dictionary<string, bool> assignment = new(StringComparer.Ordinal);
        bool satisfiable = Dpll(clauses, assignment, ref decisions, ref propagations);

        return new PlInferenceResult(
            PlInferProcedure.DPLLSatisfiable,
            "KB est satisfiable",
            satisfiable ? PlVerdict.Yes : PlVerdict.No,
            decisions,
            "decisions DPLL",
            satisfiable ? Complete(knowledgeBase, assignment) : null);
    }

    /// <summary>Satisfiabilite de la base par recherche locale WalkSAT.</summary>
    public static PlInferenceResult WalkSatKb(
        PlKnowledgeBase knowledgeBase,
        int maxFlips = 1000,
        int seed = 0)
    {
        ArgumentNullException.ThrowIfNull(knowledgeBase);

        return WalkSatOnClauses(
            PlInferProcedure.WalkSatKb,
            "KB est satisfiable",
            new List<PlClause>(knowledgeBase.ToClauses()),
            maxFlips,
            seed);
    }

    /// <summary>Satisfiabilite de la base jointe a la requete, par WalkSAT.</summary>
    public static PlInferenceResult WalkSatPredicate(
        PlKnowledgeBase knowledgeBase,
        PlFormula query,
        int maxFlips = 1000,
        int seed = 0)
    {
        ArgumentNullException.ThrowIfNull(knowledgeBase);
        ArgumentNullException.ThrowIfNull(query);

        List<PlClause> clauses = new(knowledgeBase.ToClauses());
        clauses.AddRange(PlCnf.ToClauses(query));

        return WalkSatOnClauses(
            PlInferProcedure.WalkSatPredicate,
            "KB & requete est satisfiable",
            clauses,
            maxFlips,
            seed);
    }

    private static PlInferenceResult WalkSatOnClauses(
        PlInferProcedure procedure,
        string question,
        List<PlClause> clauses,
        int maxFlips,
        int seed)
    {
        if (clauses.Any(clause => clause.IsEmpty))
        {
            // Une clause vide rend l'ensemble insatisfiable : inutile de chercher.
            return new PlInferenceResult(procedure, question, PlVerdict.No, 0, "flips");
        }

        Random random = new(seed);
        bool satisfiable = WalkSat(clauses, random, maxFlips, out int flips, out IReadOnlyDictionary<string, bool>? model);

        return new PlInferenceResult(
            procedure,
            question,
            satisfiable ? PlVerdict.Yes : PlVerdict.Unknown,
            flips,
            "flips",
            model);
    }

    /// <summary>Determine si un ensemble de clauses est satisfiable, et rend un modele s'il en existe un.</summary>
    public static bool IsSatisfiable(IReadOnlyList<PlClause> clauses, out IReadOnlyDictionary<string, bool>? model)
    {
        ArgumentNullException.ThrowIfNull(clauses);

        int decisions = 0;
        int propagations = 0;
        Dictionary<string, bool> assignment = new(StringComparer.Ordinal);
        bool satisfiable = Dpll(clauses, assignment, ref decisions, ref propagations);
        model = satisfiable ? new Dictionary<string, bool>(assignment, StringComparer.Ordinal) : null;
        return satisfiable;
    }

    private static bool ResolveRefutation(IReadOnlyList<PlClause> clauses, int maxResolvents, out int derived)
    {
        derived = 0;
        List<PlClause> set = new();

        foreach (PlClause clause in clauses)
        {
            if (clause.IsEmpty)
            {
                return true;
            }

            if (clause.IsTautology)
            {
                continue;
            }

            if (!set.Any(existing => existing.SetEquals(clause)))
            {
                set.Add(clause);
            }
        }

        bool added = true;

        while (added)
        {
            added = false;
            int count = set.Count;

            for (int first = 0; first < count; first++)
            {
                for (int second = first + 1; second < count; second++)
                {
                    foreach (PlClause resolvent in ResolvePair(set[first], set[second]))
                    {
                        if (resolvent.IsTautology)
                        {
                            continue;
                        }

                        if (resolvent.IsEmpty)
                        {
                            derived++;
                            return true;
                        }

                        if (set.Any(existing => existing.SetEquals(resolvent)))
                        {
                            continue;
                        }

                        set.Add(resolvent);
                        derived++;
                        added = true;

                        if (derived > maxResolvents)
                        {
                            throw new InvalidOperationException(
                                $"La refutation a derive plus de {maxResolvents} resolvantes sans conclure ; " +
                                "l'instance sort du regime de cette procedure. Utiliser DPLL.");
                        }
                    }
                }
            }
        }

        return false;
    }

    private static IEnumerable<PlClause> ResolvePair(PlClause first, PlClause second)
    {
        foreach (PlLiteral literal in first.Literals)
        {
            if (!second.Literals.Contains(literal.Negate()))
            {
                continue;
            }

            IEnumerable<PlLiteral> merged = first.Literals
                .Where(candidate => candidate != literal)
                .Concat(second.Literals.Where(candidate => candidate != literal.Negate()));

            yield return new PlClause(merged);
        }
    }

    private static bool Dpll(
        IReadOnlyList<PlClause> clauses,
        Dictionary<string, bool> assignment,
        ref int decisions,
        ref int propagations)
    {
        while (true)
        {
            bool allSatisfied = true;
            bool hasUnit = false;
            PlLiteral unit = default;

            foreach (PlClause clause in clauses)
            {
                if (IsSatisfied(clause, assignment, out int unassigned, out PlLiteral lastUnassigned))
                {
                    continue;
                }

                allSatisfied = false;

                if (unassigned == 0)
                {
                    return false;
                }

                if (unassigned == 1 && !hasUnit)
                {
                    hasUnit = true;
                    unit = lastUnassigned;
                }
            }

            if (allSatisfied)
            {
                return true;
            }

            if (hasUnit)
            {
                assignment[unit.Name] = !unit.Negated;
                propagations++;
                continue;
            }

            if (TryPureLiteral(clauses, assignment, out PlLiteral pure))
            {
                assignment[pure.Name] = !pure.Negated;
                propagations++;
                continue;
            }

            break;
        }

        string? symbol = ChooseSymbol(clauses, assignment);

        if (symbol is null)
        {
            // Toutes les clauses sont satisfaites : le cas a ete traite plus haut.
            return true;
        }

        decisions++;
        Dictionary<string, bool> withTrue = new(assignment, StringComparer.Ordinal) { [symbol] = true };

        if (Dpll(clauses, withTrue, ref decisions, ref propagations))
        {
            Restore(assignment, withTrue);
            return true;
        }

        decisions++;
        Dictionary<string, bool> withFalse = new(assignment, StringComparer.Ordinal) { [symbol] = false };

        if (Dpll(clauses, withFalse, ref decisions, ref propagations))
        {
            Restore(assignment, withFalse);
            return true;
        }

        return false;
    }

    private static void Restore(Dictionary<string, bool> assignment, Dictionary<string, bool> source)
    {
        assignment.Clear();

        foreach (KeyValuePair<string, bool> entry in source)
        {
            assignment[entry.Key] = entry.Value;
        }
    }

    private static bool IsSatisfied(
        PlClause clause,
        IReadOnlyDictionary<string, bool> assignment,
        out int unassignedCount,
        out PlLiteral lastUnassigned)
    {
        unassignedCount = 0;
        lastUnassigned = default;

        foreach (PlLiteral literal in clause.Literals)
        {
            if (assignment.TryGetValue(literal.Name, out bool value))
            {
                // Un litteral est vrai quand la valeur du symbole vaut !Negated.
                if (value == !literal.Negated)
                {
                    return true;
                }
            }
            else
            {
                unassignedCount++;
                lastUnassigned = literal;
            }
        }

        return false;
    }

    private static bool TryPureLiteral(
        IReadOnlyList<PlClause> clauses,
        IReadOnlyDictionary<string, bool> assignment,
        out PlLiteral pure)
    {
        HashSet<string> positive = new(StringComparer.Ordinal);
        HashSet<string> negative = new(StringComparer.Ordinal);

        foreach (PlClause clause in clauses)
        {
            if (IsSatisfied(clause, assignment, out _, out _))
            {
                continue;
            }

            foreach (PlLiteral literal in clause.Literals)
            {
                if (assignment.ContainsKey(literal.Name))
                {
                    continue;
                }

                if (literal.Negated)
                {
                    negative.Add(literal.Name);
                }
                else
                {
                    positive.Add(literal.Name);
                }
            }
        }

        foreach (string symbol in positive.OrderBy(name => name, StringComparer.Ordinal))
        {
            if (!negative.Contains(symbol))
            {
                pure = new PlLiteral(symbol, false);
                return true;
            }
        }

        foreach (string symbol in negative.OrderBy(name => name, StringComparer.Ordinal))
        {
            if (!positive.Contains(symbol))
            {
                pure = new PlLiteral(symbol, true);
                return true;
            }
        }

        pure = default;
        return false;
    }

    private static string? ChooseSymbol(
        IReadOnlyList<PlClause> clauses,
        IReadOnlyDictionary<string, bool> assignment)
    {
        foreach (PlClause clause in clauses)
        {
            if (IsSatisfied(clause, assignment, out _, out _))
            {
                continue;
            }

            string? candidate = clause.Literals
                .Where(literal => !assignment.ContainsKey(literal.Name))
                .Select(literal => literal.Name)
                .OrderBy(name => name, StringComparer.Ordinal)
                .FirstOrDefault();

            if (candidate is not null)
            {
                return candidate;
            }
        }

        return null;
    }

    private static bool WalkSat(
        IReadOnlyList<PlClause> clauses,
        Random random,
        int maxFlips,
        out int flips,
        out IReadOnlyDictionary<string, bool>? model)
    {
        model = null;

        string[] symbols = clauses
            .SelectMany(clause => clause.Literals)
            .Select(literal => literal.Name)
            .Distinct(StringComparer.Ordinal)
            .OrderBy(name => name, StringComparer.Ordinal)
            .ToArray();

        Dictionary<string, bool> assignment = new(StringComparer.Ordinal);

        foreach (string symbol in symbols)
        {
            assignment[symbol] = random.Next(2) == 0;
        }

        for (flips = 0; flips < maxFlips; flips++)
        {
            List<PlClause> unsatisfied = clauses
                .Where(clause => !IsSatisfied(clause, assignment, out _, out _))
                .ToList();

            if (unsatisfied.Count == 0)
            {
                model = new Dictionary<string, bool>(assignment, StringComparer.Ordinal);
                return true;
            }

            PlClause chosen = unsatisfied[random.Next(unsatisfied.Count)];
            PlLiteral[] literals = chosen.Literals
                .OrderBy(literal => literal.Name, StringComparer.Ordinal)
                .ThenBy(literal => literal.Negated)
                .ToArray();

            PlLiteral flip;

            if (random.Next(2) == 0 || literals.Length == 0)
            {
                flip = literals[random.Next(literals.Length)];
            }
            else
            {
                // Biais glouton : retourner le litteral qui laisse le moins de clauses insatisfaites.
                List<PlLiteral> best = new();
                int bestCount = int.MaxValue;

                foreach (PlLiteral literal in literals)
                {
                    assignment[literal.Name] = !assignment[literal.Name];
                    int remaining = clauses.Count(clause => !IsSatisfied(clause, assignment, out _, out _));
                    assignment[literal.Name] = !assignment[literal.Name];

                    if (remaining < bestCount)
                    {
                        bestCount = remaining;
                        best.Clear();
                        best.Add(literal);
                    }
                    else if (remaining == bestCount)
                    {
                        best.Add(literal);
                    }
                }

                flip = best[random.Next(best.Count)];
            }

            assignment[flip.Name] = !assignment[flip.Name];
        }

        return false;
    }

    private static IReadOnlyDictionary<string, bool> Complete(
        PlKnowledgeBase knowledgeBase,
        Dictionary<string, bool> assignment)
    {
        Dictionary<string, bool> complete = new(assignment, StringComparer.Ordinal);

        foreach (string symbol in knowledgeBase.Symbols)
        {
            if (!complete.ContainsKey(symbol))
            {
                complete[symbol] = false;
            }
        }

        return complete;
    }
}

/// <summary>
/// Procedure d'inference appliquee a une base et a un predicat.
/// </summary>
/// <remarks>
/// Port de <c>PLKbInferProcedureInfo</c> : le wrapper Aricie associe une procedure
/// a une base de connaissances et a un predicat. Deux procedures ignorent le
/// predicat par construction (<see cref="PlInferProcedure.DPLLSatisfiable"/> et
/// <see cref="PlInferProcedure.WalkSatKb"/> interrogent la base seule) ; c'est
/// documente plutot que silencieux.
/// </remarks>
public sealed class PlKbInferProcedureInfo
{
    public PlKbInferProcedureInfo(PlInferProcedure procedure, int maxFlips = 1000, int seed = 0)
    {
        ArgumentOutOfRangeException.ThrowIfNegativeOrZero(maxFlips);

        Procedure = procedure;
        MaxFlips = maxFlips;
        Seed = seed;
    }

    /// <summary>Procedure appliquee.</summary>
    public PlInferProcedure Procedure { get; }

    /// <summary>Budget de flips des procedures WalkSAT.</summary>
    public int MaxFlips { get; }

    /// <summary>Graine des procedures WalkSAT : la rend reproductible.</summary>
    public int Seed { get; }

    /// <summary>Applique la procedure a la base et au predicat.</summary>
    public PlInferenceResult Ask(PlKnowledgeBase knowledgeBase, PlFormula predicate)
    {
        ArgumentNullException.ThrowIfNull(knowledgeBase);
        ArgumentNullException.ThrowIfNull(predicate);

        return Procedure switch
        {
            PlInferProcedure.TTEntails => PlInference.TtEntails(knowledgeBase, predicate),
            PlInferProcedure.Resolve => PlInference.Resolve(knowledgeBase, predicate),
            PlInferProcedure.DPLLEntails => PlInference.DpllEntails(knowledgeBase, predicate),
            PlInferProcedure.DPLLSatisfiable => PlInference.DpllSatisfiable(knowledgeBase),
            PlInferProcedure.WalkSatKb => PlInference.WalkSatKb(knowledgeBase, MaxFlips, Seed),
            PlInferProcedure.WalkSatPredicate => PlInference.WalkSatPredicate(knowledgeBase, predicate, MaxFlips, Seed),
            _ => throw new ArgumentOutOfRangeException(
                nameof(predicate),
                Procedure,
                "Procedure d'inference inconnue."),
        };
    }
}
