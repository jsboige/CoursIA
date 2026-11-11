namespace MyIA.AI.Shared.Search.Logic.Propositional;

/// <summary>Litteral : un symbole, eventuellement nie.</summary>
public readonly record struct PlLiteral(string Name, bool Negated)
{
    /// <summary>Litteral oppose.</summary>
    public PlLiteral Negate() => new(Name, !Negated);

    public override string ToString() => Negated ? "~" + Name : Name;
}

/// <summary>Clause : disjonction de litteraux, sans doublon.</summary>
public sealed class PlClause
{
    private readonly HashSet<PlLiteral> _literals;

    public PlClause(IEnumerable<PlLiteral> literals)
    {
        ArgumentNullException.ThrowIfNull(literals);
        _literals = new HashSet<PlLiteral>(literals);
    }

    /// <summary>Litteraux de la clause.</summary>
    public IReadOnlyCollection<PlLiteral> Literals => _literals;

    /// <summary>Vrai si la clause est vide : c'est la clause fausse de la refutation.</summary>
    public bool IsEmpty => _literals.Count == 0;

    /// <summary>Vrai si la clause contient un litteral et son oppose : toujours vraie, donc inutile.</summary>
    public bool IsTautology => _literals.Any(literal => _literals.Contains(literal.Negate()));

    /// <summary>Egalite ensembliste entre clauses.</summary>
    public bool SetEquals(PlClause other)
    {
        ArgumentNullException.ThrowIfNull(other);
        return _literals.SetEquals(other._literals);
    }

    public override string ToString() =>
        IsEmpty ? "[]" : "(" + string.Join(" | ", _literals.OrderBy(l => l.Name, StringComparer.Ordinal).ThenBy(l => l.Negated)) + ")";
}

/// <summary>
/// Mise sous forme normale conjonctive.
/// </summary>
/// <remarks>
/// Trois etapes, dans cet ordre : elimination de l'equivalence et de l'implication,
/// poussee des negations jusqu'aux symboles (forme normale de negation), puis
/// distribution de la disjonction sur la conjonction. Les clauses tautologiques
/// sont ecartees : elles n'apportent rien a la refutation et gonflent le compteur
/// de pas des procedures.
/// </remarks>
public static class PlCnf
{
    /// <summary>
    /// Nombre maximal de clauses que la distribution peut produire avant de lever.
    /// Une formule du type (a1 &amp; b1) | ... | (an &amp; bn) produit 2^n clauses :
    /// cette borne evite que la conversion elle-meme derive sans budget, alors que
    /// toutes les procedures qui la consomment sont, elles, budgetees.
    /// </summary>
    public const int MaxClauses = 20000;

    /// <summary>Convertit une formule en ensemble de clauses.</summary>
    public static IReadOnlyList<PlClause> ToClauses(PlFormula formula)
    {
        ArgumentNullException.ThrowIfNull(formula);

        PlFormula eliminated = Eliminate(formula);
        PlFormula nnf = ToNegationNormalForm(eliminated, negated: false);
        List<PlClause> clauses = Distribut(nnf, budget: MaxClauses);

        return clauses
            .Where(clause => !clause.IsTautology)
            .ToList();
    }

    private static PlFormula Eliminate(PlFormula formula) => formula switch
    {
        PlBiconditional biconditional => new PlAnd(
            Eliminate(new PlImplies(biconditional.Left, biconditional.Right)),
            Eliminate(new PlImplies(biconditional.Right, biconditional.Left))),
        PlImplies implies => new PlOr(
            new PlNot(Eliminate(implies.Left)),
            Eliminate(implies.Right)),
        PlNot not => new PlNot(Eliminate(not.Operand)),
        PlAnd and => new PlAnd(Eliminate(and.Left), Eliminate(and.Right)),
        PlOr or => new PlOr(Eliminate(or.Left), Eliminate(or.Right)),
        PlAtom => formula,
        _ => throw new ArgumentException($"Formule non prise en charge : {formula.GetType().Name}", nameof(formula)),
    };

    private static PlFormula ToNegationNormalForm(PlFormula formula, bool negated)
    {
        switch (formula)
        {
            case PlAtom atom:
                return negated ? new PlNot(atom) : atom;

            case PlNot not:
                return ToNegationNormalForm(not.Operand, !negated);

            case PlAnd and:
                return negated
                    ? new PlOr(ToNegationNormalForm(and.Left, true), ToNegationNormalForm(and.Right, true))
                    : new PlAnd(ToNegationNormalForm(and.Left, false), ToNegationNormalForm(and.Right, false));

            case PlOr or:
                return negated
                    ? new PlAnd(ToNegationNormalForm(or.Left, true), ToNegationNormalForm(or.Right, true))
                    : new PlOr(ToNegationNormalForm(or.Left, false), ToNegationNormalForm(or.Right, false));

            default:
                throw new ArgumentException(
                    $"La formule '{formula}' n'est pas en forme eliminee (equivalence ou implication restante).",
                    nameof(formula));
        }
    }

    private static List<PlClause> Distribut(PlFormula nnf, int budget)
    {
        switch (nnf)
        {
            case PlAtom atom:
                return new List<PlClause> { new(new[] { new PlLiteral(atom.Name, false) }) };

            case PlNot not when not.Operand is PlAtom negatedAtom:
                return new List<PlClause> { new(new[] { new PlLiteral(negatedAtom.Name, true) }) };

            case PlAnd and:
                {
                    List<PlClause> clauses = Distribut(and.Left, budget);
                    clauses.AddRange(Distribut(and.Right, budget));
                    return clauses;
                }

            case PlOr or:
                {
                    List<PlClause> left = Distribut(or.Left, budget);
                    List<PlClause> right = Distribut(or.Right, budget);
                    List<PlClause> product = new(left.Count * right.Count);

                    foreach (PlClause leftClause in left)
                    {
                        foreach (PlClause rightClause in right)
                        {
                            product.Add(new PlClause(leftClause.Literals.Concat(rightClause.Literals)));
                        }
                    }

                    if (product.Count > budget)
                    {
                        throw new InvalidOperationException(
                            $"La distribution produit plus de {budget} clauses ; " +
                            "l'instance sort du regime de la conversion CNF. " +
                            "Utiliser DPLL ou une decomposition de la formule.");
                    }

                    return product;
                }

            default:
                throw new ArgumentException(
                    $"Noeud inattendu dans la forme normale de negation : {nnf.GetType().Name}.",
                    nameof(nnf));
        }
    }
}
