namespace MyIA.AI.Shared.Search.Logic.Propositional;

/// <summary>
/// Base de connaissances propositionnelle : un ensemble de phrases.
/// </summary>
/// <remarks>
/// Port de la surface <c>PLKbInfo</c> du patrimoine Aricie (EPIC #7265, volet B2
/// tranche 1, issue #23584). La base ne calcule rien d'elle-meme : elle stocke des
/// phrases et les expose en clauses ; la deduction appartient a
/// <see cref="PlInference"/>.
/// </remarks>
public sealed class PlKnowledgeBase
{
    private readonly List<PlFormula> _sentences = new();

    /// <summary>Phrases de la base, dans l'ordre d'ajout.</summary>
    public IReadOnlyList<PlFormula> Sentences => _sentences;

    /// <summary>Symboles apparaissant dans les phrases de la base.</summary>
    public IReadOnlyCollection<string> Symbols =>
        _sentences.SelectMany(sentence => sentence.Symbols)
            .Distinct(StringComparer.Ordinal)
            .OrderBy(symbol => symbol, StringComparer.Ordinal)
            .ToArray();

    /// <summary>Ajoute une phrase a la base.</summary>
    public PlKnowledgeBase Tell(PlFormula sentence)
    {
        ArgumentNullException.ThrowIfNull(sentence);
        _sentences.Add(sentence);
        return this;
    }

    /// <summary>Analyse la source puis ajoute la phrase obtenue.</summary>
    public PlKnowledgeBase Tell(string source) => Tell(PlParser.Parse(source));

    /// <summary>Vrai si l'affectation satisfait toutes les phrases de la base.</summary>
    public bool IsSatisfiedBy(IReadOnlyDictionary<string, bool> assignment)
    {
        ArgumentNullException.ThrowIfNull(assignment);
        return _sentences.All(sentence => sentence.Evaluate(assignment));
    }

    /// <summary>
    /// Clauses de la conjonction des phrases de la base.
    /// Une base vide rend une liste vide, qui est satisfiable par construction.
    /// </summary>
    public IReadOnlyList<PlClause> ToClauses()
    {
        List<PlClause> clauses = new();

        foreach (PlFormula sentence in _sentences)
        {
            clauses.AddRange(PlCnf.ToClauses(sentence));
        }

        return clauses;
    }
}
