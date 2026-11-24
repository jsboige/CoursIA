namespace MyIA.AI.Shared.Search.Logic.FirstOrder;

/// <summary>
/// Domaine du premier ordre : constantes, predicats et fonctions avec leurs arites.
/// </summary>
/// <remarks>
/// Port de <c>FolDomainInfo</c> du patrimoine Aricie (EPIC #7265, volet B2
/// tranche 2, issue #24320). Les arites suivent la convention aima-core :
/// un symbole se declare sous la forme <c>"Nom/2"</c>. Le domaine est fini,
/// enonce tel quel : c'est ce qui rend possible l'ancrage des quantificateurs
/// par <see cref="FolInference"/> (chaque <c>FORALL x</c> devient la
/// conjonction des instances de <c>x</c> sur les constantes du domaine).
/// </remarks>
public sealed class FolDomain
{
    private readonly Dictionary<string, int> predicates = new(StringComparer.Ordinal);
    private readonly Dictionary<string, int> functions = new(StringComparer.Ordinal);

    /// <summary>Constantes du domaine, dans l'ordre d'ajout.</summary>
    public IReadOnlyList<string> Constants => this.constants;

    private readonly List<string> constants = new();

    /// <summary>Predicats declares, avec leur arite.</summary>
    public IReadOnlyDictionary<string, int> Predicates => this.predicates;

    /// <summary>Fonctions declarees, avec leur arite.</summary>
    public IReadOnlyDictionary<string, int> Functions => this.functions;

    /// <summary>Ajoute une constante.</summary>
    public FolDomain AddConstant(string name)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(name);
        if (!this.constants.Contains(name))
        {
            this.constants.Add(name);
        }

        return this;
    }

    /// <summary>Declare un predicat sous la forme <c>"Nom/2"</c> (arite deduite).</summary>
    public FolDomain AddPredicate(string declaration)
    {
        (string name, int arity) = ParseDeclaration(declaration);
        this.predicates[name] = arity;
        return this;
    }

    /// <summary>Declare une fonction sous la forme <c>"Nom/1"</c> (arite deduite).</summary>
    public FolDomain AddFunction(string declaration)
    {
        (string name, int arity) = ParseDeclaration(declaration);
        this.functions[name] = arity;
        return this;
    }

    private static (string Name, int Arity) ParseDeclaration(string declaration)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(declaration);
        int slash = declaration.IndexOf('/');
        if (slash <= 0 || slash == declaration.Length - 1)
        {
            throw new FormatException($"Declaration de symbole invalide : '{declaration}' (attendu 'Nom/arite').");
        }

        string name = declaration[..slash];
        if (!int.TryParse(declaration[(slash + 1)..], out int arity) || arity < 0)
        {
            throw new FormatException($"Arite invalide dans '{declaration}' (attendu un entier >= 0).");
        }

        return (name, arity);
    }
}
