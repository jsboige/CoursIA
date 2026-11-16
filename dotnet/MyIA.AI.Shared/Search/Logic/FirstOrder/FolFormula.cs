namespace MyIA.AI.Shared.Search.Logic.FirstOrder;

/// <summary>
/// Terme du premier ordre : variable, constante ou application de fonction.
/// </summary>
/// <remarks>
/// Port de la representation FOL du patrimoine Aricie (EPIC #7265, volet B2
/// tranche 2, issue #24320). La convention AIMA fait la difference entre
/// variables et symboles par la casse : identifiant commencant par une
/// minuscule = variable, majuscule = constante, fonction ou predicat.
/// </remarks>
public abstract record FolTerm
{
    /// <summary>Variable (quantifiee ou libre) : commence par une minuscule.</summary>
    public sealed record Variable(string Name) : FolTerm;

    /// <summary>Constante du domaine : commence par une majuscule.</summary>
    public sealed record Constant(string Name) : FolTerm;

    /// <summary>Application de fonction a des termes.</summary>
    public sealed record FunctionApplication(string Name, IReadOnlyList<FolTerm> Arguments) : FolTerm;

    /// <summary>Variables apparaissant dans le terme.</summary>
    public IEnumerable<string> Variables()
    {
        return this switch
        {
            Variable v => new[] { v.Name },
            Constant => Array.Empty<string>(),
            FunctionApplication f => f.Arguments.SelectMany(term => term.Variables()),
            _ => throw new InvalidOperationException($"Terme inconnu : {GetType().Name}"),
        };
    }
}

/// <summary>
/// Formule du premier ordre : predicat, connecteurs propositionnels, quantificateurs.
/// </summary>
/// <remarks>
/// Les connecteurs suivent la grammaire AIMA ch. 9 (<c>AND OR NOT =&gt; &lt;=&gt;</c>,
/// <c>FORALL</c>/<c>EXISTS</c>). L'evaluation n'existe pas ici : une formule FOL
/// n'a pas de valeur de verite sans interpretation, et la deduction appartient a
/// <see cref="FolInference"/>.
/// </remarks>
public abstract record FolFormula
{
    /// <summary>Atome : predicat applique a des termes (un predicat d'arite zero est une proposition).</summary>
    public sealed record Predicate(string Name, IReadOnlyList<FolTerm> Arguments) : FolFormula;

    /// <summary>Negation.</summary>
    public sealed record Not(FolFormula Operand) : FolFormula;

    /// <summary>Conjonction.</summary>
    public sealed record And(FolFormula Left, FolFormula Right) : FolFormula;

    /// <summary>Disjonction.</summary>
    public sealed record Or(FolFormula Left, FolFormula Right) : FolFormula;

    /// <summary>Implication.</summary>
    public sealed record Implies(FolFormula Left, FolFormula Right) : FolFormula;

    /// <summary>Equivalence.</summary>
    public sealed record Biconditional(FolFormula Left, FolFormula Right) : FolFormula;

    /// <summary>Quantification universelle sur une variable.</summary>
    public sealed record ForAll(string Variable, FolFormula Body) : FolFormula;

    /// <summary>Quantification existentielle sur une variable.</summary>
    public sealed record Exists(string Variable, FolFormula Body) : FolFormula;

    /// <summary>Variables libres de la formule (non liees par un quantificateur).</summary>
    public IReadOnlyCollection<string> FreeVariables() => FreeVariables(this, new HashSet<string>());

    private static HashSet<string> FreeVariables(FolFormula formula, HashSet<string> bound)
    {
        HashSet<string> result = new();
        switch (formula)
        {
            case Predicate p:
                foreach (FolTerm term in p.Arguments)
                {
                    foreach (string variable in term.Variables())
                    {
                        if (!bound.Contains(variable))
                        {
                            result.Add(variable);
                        }
                    }
                }

                break;
            case Not n:
                result.UnionWith(FreeVariables(n.Operand, bound));
                break;
            case Implies i:
                result.UnionWith(FreeVariables(i.Left, bound));
                result.UnionWith(FreeVariables(i.Right, bound));
                break;
            case Biconditional b:
                result.UnionWith(FreeVariables(b.Left, bound));
                result.UnionWith(FreeVariables(b.Right, bound));
                break;
            case And a:
                result.UnionWith(FreeVariables(a.Left, bound));
                result.UnionWith(FreeVariables(a.Right, bound));
                break;
            case Or o:
                result.UnionWith(FreeVariables(o.Left, bound));
                result.UnionWith(FreeVariables(o.Right, bound));
                break;
            case ForAll f:
                bound.Add(f.Variable);
                result.UnionWith(FreeVariables(f.Body, bound));
                bound.Remove(f.Variable);
                break;
            case Exists e:
                bound.Add(e.Variable);
                result.UnionWith(FreeVariables(e.Body, bound));
                bound.Remove(e.Variable);
                break;
            default:
                throw new InvalidOperationException($"Formule inconnue : {formula.GetType().Name}");
        }

        return result;
    }

    /// <summary>Variables quantifiees apparaissant dans la formule, pas seulement libres.</summary>
    public IEnumerable<string> AllVariables()
    {
        return this switch
        {
            Predicate p => p.Arguments.SelectMany(term => term.Variables()),
            Not n => n.Operand.AllVariables(),
            Implies i => i.Left.AllVariables().Concat(i.Right.AllVariables()),
            Biconditional b => b.Left.AllVariables().Concat(b.Right.AllVariables()),
            And a => a.Left.AllVariables().Concat(a.Right.AllVariables()),
            Or o => o.Left.AllVariables().Concat(o.Right.AllVariables()),
            ForAll f => new[] { f.Variable }.Concat(f.Body.AllVariables()),
            Exists e => new[] { e.Variable }.Concat(e.Body.AllVariables()),
            _ => throw new InvalidOperationException($"Formule inconnue : {GetType().Name}"),
        };
    }

    /// <summary>
    /// Constantes apparaissant dans la formule. L'ancrage sur domaine fini itere
    /// <see cref="FolDomain"/> : une constante utilisee sans etre declaree y est
    /// invisible pour les quantificateurs, d'ou la garde du meme nom dans
    /// <see cref="FolInference"/> (revue Hermes #24324, point 1).
    /// </summary>
    public IEnumerable<string> AllConstants()
    {
        return this switch
        {
            Predicate p => p.Arguments.SelectMany(ConstantNames),
            Not n => n.Operand.AllConstants(),
            Implies i => i.Left.AllConstants().Concat(i.Right.AllConstants()),
            Biconditional b => b.Left.AllConstants().Concat(b.Right.AllConstants()),
            And a => a.Left.AllConstants().Concat(a.Right.AllConstants()),
            Or o => o.Left.AllConstants().Concat(o.Right.AllConstants()),
            ForAll f => f.Body.AllConstants(),
            Exists e => e.Body.AllConstants(),
            _ => throw new InvalidOperationException($"Formule inconnue : {GetType().Name}"),
        };
    }

    /// <summary>Constantes d'un terme, fonction recursive comprise.</summary>
    private static IEnumerable<string> ConstantNames(FolTerm term)
    {
        return term switch
        {
            FolTerm.Constant c => new[] { c.Name },
            FolTerm.FunctionApplication f => f.Arguments.SelectMany(ConstantNames),
            _ => Array.Empty<string>(),
        };
    }
}
