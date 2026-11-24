namespace MyIA.AI.Shared.Search.Logic.FirstOrder;

/// <summary>
/// Base de connaissances du premier ordre : un ensemble de phrases, un domaine, une procedure.
/// </summary>
/// <remarks>
/// Port de <c>FolKbInfo</c> du patrimoine Aricie (EPIC #7265, volet B2
/// tranche 2, issue #24320) : <c>Domain</c>, <c>Procedure</c> et phrases.
/// La base ne calcule rien d'elle-meme : elle stocke des phrases et expose les
/// clauses definies ; la deduction appartient a <see cref="FolInference"/>.
/// </remarks>
public sealed class FolKnowledgeBase
{
    private readonly List<FolFormula> sentences = new();

    /// <summary>Domaine associe a la base.</summary>
    public FolDomain Domain { get; } = new();

    /// <summary>Procedure d'inference selectionnee, comme sur le wrapper Aricie.</summary>
    public FolInferenceProcedure Procedure { get; set; } = FolInferenceProcedure.FCAsk;

    /// <summary>Phrases de la base, dans l'ordre d'ajout.</summary>
    public IReadOnlyList<FolFormula> Sentences => this.sentences;

    /// <summary>Ajoute une phrase a la base.</summary>
    public FolKnowledgeBase Tell(FolFormula sentence)
    {
        ArgumentNullException.ThrowIfNull(sentence);
        this.sentences.Add(sentence);
        return this;
    }

    /// <summary>Analyse la source puis ajoute la phrase obtenue.</summary>
    public FolKnowledgeBase Tell(string source) => Tell(FolParser.Parse(source));

    /// <summary>
    /// Clauses definies de la base : chaque phrase de la forme
    /// <c>FORALL ... (conjonction d'atomes =&gt; atome)</c>, quantificateurs
    /// retires, avec la conjonction aplatie en premisses. Les phrases qui ne
    /// sont ni des clauses definies ni des faits ne participent pas au chainage.
    /// </summary>
    public IReadOnlyList<FolDefiniteClause> DefiniteClauses()
    {
        List<FolDefiniteClause> clauses = new();
        foreach (FolFormula sentence in this.sentences)
        {
            FolFormula body = StripQuantifiers(sentence);
            if (body is FolFormula.Implies { Left: var antecedent, Right: FolFormula.Predicate head }
                && FlattenConjunction(antecedent) is { Length: > 0 } premises)
            {
                clauses.Add(new FolDefiniteClause(premises, head));
            }
            else if (body is FolFormula.Predicate fact)
            {
                clauses.Add(new FolDefiniteClause(Array.Empty<FolFormula.Predicate>(), fact));
            }
        }

        return clauses;
    }

    private static FolFormula StripQuantifiers(FolFormula formula)
    {
        while (formula is FolFormula.ForAll { Body: var inner })
        {
            formula = inner;
        }

        return formula;
    }

    /// <summary>Aplatit une conjonction d'atomes ; rend null des qu'un operand n'est pas un atome.</summary>
    private static FolFormula.Predicate[]? FlattenConjunction(FolFormula formula)
    {
        List<FolFormula.Predicate> atoms = new();
        bool Walk(FolFormula node)
        {
            if (node is FolFormula.And { Left: var left, Right: var right })
            {
                return Walk(left) && Walk(right);
            }

            if (node is FolFormula.Predicate atom)
            {
                atoms.Add(atom);
                return true;
            }

            return false;
        }

        return Walk(formula) ? atoms.ToArray() : null;
    }
}

/// <summary>Clause definie : premisses (conjonction d'atomes) et tete (atome).</summary>
/// <param name="Premises">Atomes du corps de la clause.</param>
/// <param name="Head">Atome de tete.</param>
public sealed record FolDefiniteClause(IReadOnlyList<FolFormula.Predicate> Premises, FolFormula.Predicate Head);
