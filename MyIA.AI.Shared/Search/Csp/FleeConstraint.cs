using System;
using System.Collections.Generic;
using System.Linq;
using System.Text.RegularExpressions;
using Flee.PublicTypes;

namespace MyIA.AI.Shared.Search.Csp;

/// <summary>
/// Contrainte CSP dont le verdict est une expression Flee ecrite en texte, portant
/// sur n variables nommees. C'est le "bijou" du wrapper d'origine (AIMA + Flee,
/// EPIC #7265, pepite B1) : une contrainte arbitraire — pas seulement binaire —
/// s'exprime sans recompiler l'hote, ce que <see cref="BinaryConstraint"/> ne
/// permet pas.
/// </summary>
/// <remarks>
/// <para>
/// <b>Compile une fois, evalue a chaque noeud.</b> L'expression est compilee dans le
/// constructeur contre les noms des variables du scope ; chaque
/// <see cref="IsSatisfied"/> ne fait plus que pousser les valeurs courantes dans le
/// contexte Flee et appeler le delegue compile. C'est le meme contrat que
/// <c>ComponentModel.Rules.FleePredicateBuilder</c> (pepite B4, "le liant
/// universel"), applique a des variables nommees au lieu des proprietes d'un type :
/// B4 lie un predicat a un <c>T</c>, celui-ci le lie a un scope CSP. Les deux sont
/// des consommateurs de Flee, pas deux implementations de la meme chose.
/// </para>
/// <para>
/// <b>Sentinel de type.</b> Flee infere le type d'une variable a la compilation et
/// refuse les valeurs nulles. La premiere valeur non nulle du domaine sert donc de
/// sentinelle a la compilation ; un domaine vide ou entierement nul retombe sur la
/// chaine vide, comme B4 le fait pour un type de reference. Consequence a connaitre :
/// les valeurs d'un domaine doivent etre de type homogene, sinon Flee refuse la
/// valeur au moment de l'evaluation.
/// </para>
/// <para>
/// <b>Affectation partielle.</b> Comme <see cref="BinaryConstraint"/>, une contrainte
/// dont une variable du scope n'est pas encore affectee est consideree satisfaite :
/// c'est ce qui la rend utilisable pendant la recherche, ou l'on teste la coherence
/// avant d'avoir une affectation complete.
/// </para>
/// <para>
/// <b>Syntaxe des regles.</b> Celle de Flee, qui est proche de VB : <c>and</c> /
/// <c>or</c> / <c>not</c> en mots (pas <c>&amp;&amp;</c> / <c>||</c>), egalite par
/// <c>=</c> (pas <c>==</c>), difference par <c>&lt;&gt;</c>. Exemple :
/// <c>"X &lt;&gt; Y and X + Y &lt;= 5"</c>.
/// </para>
/// </remarks>
public sealed class FleeConstraint : IConstraint
{
    // Flee resout un nom de variable par son texte : un nom qui n'est pas un
    // identifiant valide serait silencieusement inatteignable depuis la regle,
    // et la contrainte se contenterait de rendre toujours vrai.
    private static readonly Regex IdentifierPattern =
        new("^[A-Za-z_][A-Za-z0-9_]*$", RegexOptions.CultureInvariant);

    private readonly ExpressionContext _context;
    private readonly IGenericExpression<bool> _expression;
    private readonly Variable[] _scope;
    private readonly object[] _sentinels;

    /// <summary>Compile <paramref name="rule"/> contre les noms des variables du scope.</summary>
    /// <param name="rule">Expression Flee rendant un booleen, ex. <c>"X &lt;&gt; Y"</c>.</param>
    /// <param name="scope">Variables liees par leur nom ; au moins une.</param>
    /// <param name="name">Nom de trace ; par defaut le texte de la regle.</param>
    /// <exception cref="ArgumentNullException"><paramref name="rule"/> vide ou nul.</exception>
    /// <exception cref="ArgumentException">Scope vide, ou nom de variable non identifiable.</exception>
    /// <exception cref="ExpressionCompileException">Regle invalide, ou nom inconnu du scope.</exception>
    public FleeConstraint(string rule, IEnumerable<Variable> scope, string? name = null)
    {
        if (string.IsNullOrWhiteSpace(rule))
        {
            throw new ArgumentNullException(nameof(rule));
        }

        ArgumentNullException.ThrowIfNull(scope);

        _scope = scope.ToArray();
        if (_scope.Length == 0)
        {
            throw new ArgumentException(
                "Une contrainte Flee doit porter sur au moins une variable.",
                nameof(scope));
        }

        _sentinels = new object[_scope.Length];
        _context = new ExpressionContext();
        _context.Options.CaseSensitive = true;

        for (int index = 0; index < _scope.Length; index++)
        {
            Variable variable = _scope[index];

            if (!IdentifierPattern.IsMatch(variable.Name))
            {
                throw new ArgumentException(
                    $"Le nom de variable '{variable.Name}' n'est pas un identifiant utilisable dans une regle Flee.",
                    nameof(scope));
            }

            _sentinels[index] = SentinelFor(variable);
            _context.Variables[variable.Name] = _sentinels[index];
        }

        _expression = _context.CompileGeneric<bool>(rule);
        Rule = rule;
        Name = name ?? $"flee({rule})";
    }

    /// <summary>Texte de la regle, tel qu'il a ete compile.</summary>
    public string Rule { get; }

    /// <summary>Nom de la contrainte, utilise dans les traces.</summary>
    public string Name { get; }

    /// <summary>Variables du scope, dans l'ordre de declaration.</summary>
    public IReadOnlyList<Variable> Scope => _scope;

    /// <inheritdoc />
    public bool IsSatisfied(Assignment assignment)
    {
        ArgumentNullException.ThrowIfNull(assignment);

        // Toutes les variables doivent etre affectees avant d'evaluer : une
        // affectation partielle est satisfaite par contrat, et on ne mute pas le
        // contexte Flee pour rien.
        for (int index = 0; index < _scope.Length; index++)
        {
            if (!assignment.TryGetValue(_scope[index], out _))
            {
                return true;
            }
        }

        for (int index = 0; index < _scope.Length; index++)
        {
            object? value = assignment.Get(_scope[index]);

            // Flee refuse une valeur nulle : on retombe sur la sentinelle de
            // compilation, exactement comme FleePredicateBuilder le fait pour
            // un type de reference (B4).
            _context.Variables[_scope[index].Name] = value ?? _sentinels[index];
        }

        return _expression.Evaluate();
    }

    public override string ToString() => Name;

    private static object SentinelFor(Variable variable)
    {
        foreach (object? value in variable.Domain.Values)
        {
            if (value is not null)
            {
                return value;
            }
        }

        return string.Empty;
    }
}
