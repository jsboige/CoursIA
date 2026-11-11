namespace MyIA.AI.Shared.Search.Logic.Propositional;

/// <summary>
/// Formule du calcul propositionnel (PL).
/// </summary>
/// <remarks>
/// Port du noyau propositionnel de <c>Logic.cs</c> du patrimoine Aricie
/// (EPIC #7265, volet B2 tranche 1, issue #23584). La surface reproduite est
/// celle que le wrapper <c>PLKbInfo</c> expose : des phrases et des procedures
/// d'inference. La semantique est celle du chapitre 7 d'AIMA (Russell et Norvig,
/// <i>Artificial Intelligence: A Modern Approach</i>).
/// </remarks>
public abstract record PlFormula
{
    /// <summary>Evalue la formule sous une affectation totale des symboles.</summary>
    /// <param name="assignment">Valeur de chaque symbole. Une affectation partielle leve.</param>
    public abstract bool Evaluate(IReadOnlyDictionary<string, bool> assignment);

    /// <summary>Symboles apparaissant dans la formule, sans doublon.</summary>
    public abstract IReadOnlyCollection<string> Symbols { get; }
}

/// <summary>Symbole propositionnel, par exemple <c>A</c> ou <c>P12</c>.</summary>
public sealed record PlAtom(string Name) : PlFormula
{
    public override bool Evaluate(IReadOnlyDictionary<string, bool> assignment)
    {
        ArgumentNullException.ThrowIfNull(assignment);
        if (!assignment.TryGetValue(Name, out bool value))
        {
            throw new KeyNotFoundException(
                $"Le symbole '{Name}' n'est pas assigne ; l'evaluation exige une affectation totale.");
        }

        return value;
    }

    public override IReadOnlyCollection<string> Symbols => new[] { Name };

    public override string ToString() => Name;
}

/// <summary>Negation logique, notee <c>~</c>.</summary>
public sealed record PlNot(PlFormula Operand) : PlFormula
{
    public override bool Evaluate(IReadOnlyDictionary<string, bool> assignment)
    {
        ArgumentNullException.ThrowIfNull(Operand);
        return !Operand.Evaluate(assignment);
    }

    public override IReadOnlyCollection<string> Symbols => Operand.Symbols;

    public override string ToString() => $"~{Operand}";
}

/// <summary>Connecteur binaire.</summary>
public abstract record PlBinary(PlFormula Left, PlFormula Right) : PlFormula
{
    public override IReadOnlyCollection<string> Symbols =>
        Left.Symbols.Concat(Right.Symbols).Distinct(StringComparer.Ordinal).ToArray();
}

/// <summary>Conjonction, notee <c>&amp;</c>.</summary>
public sealed record PlAnd(PlFormula Left, PlFormula Right) : PlBinary(Left, Right)
{
    public override bool Evaluate(IReadOnlyDictionary<string, bool> assignment) =>
        Left.Evaluate(assignment) && Right.Evaluate(assignment);

    public override string ToString() => $"({Left} & {Right})";
}

/// <summary>Disjonction, notee <c>|</c>.</summary>
public sealed record PlOr(PlFormula Left, PlFormula Right) : PlBinary(Left, Right)
{
    public override bool Evaluate(IReadOnlyDictionary<string, bool> assignment) =>
        Left.Evaluate(assignment) || Right.Evaluate(assignment);

    public override string ToString() => $"({Left} | {Right})";
}

/// <summary>Implication, notee <c>=&gt;</c>. Semantique : <c>~Left | Right</c>.</summary>
public sealed record PlImplies(PlFormula Left, PlFormula Right) : PlBinary(Left, Right)
{
    public override bool Evaluate(IReadOnlyDictionary<string, bool> assignment) =>
        !Left.Evaluate(assignment) || Right.Evaluate(assignment);

    public override string ToString() => $"({Left} => {Right})";
}

/// <summary>Equivalence, notee <c>&lt;=&gt;</c>.</summary>
public sealed record PlBiconditional(PlFormula Left, PlFormula Right) : PlBinary(Left, Right)
{
    public override bool Evaluate(IReadOnlyDictionary<string, bool> assignment) =>
        Left.Evaluate(assignment) == Right.Evaluate(assignment);

    public override string ToString() => $"({Left} <=> {Right})";
}
