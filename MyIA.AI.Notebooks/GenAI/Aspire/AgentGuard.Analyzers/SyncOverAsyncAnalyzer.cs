using System.Collections.Immutable;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Diagnostics;

namespace AgentGuard.Analyzers;

/// <summary>
/// AGENTGUARD005 : blocage synchrone d'une Task via GetAwaiter().GetResult().
///
/// Quatrieme pattern typique du code genere par agent : appeler une tache
/// asynchrone depuis du code synchrone en la bloquant par `.GetAwaiter()
/// .GetResult()` au lieu de l'attendre (`await`). Meme consequence qu'
/// AGENTGUARD001 (.Result / .Wait()) : deadlock potentiel en code d'agent --
/// mais un pattern plus discret, parce que l'agent "voit" un appel de
/// methode ordinaire et ne se doute pas qu'il traverse l'etat-majeur
/// d'une tache.
///
/// La forme legitime est `await` ; la resolution de la valeur doit passer
/// par le mecanisme d'attente, pas par la decompilation explicite de la
/// machine a etats de la tache.
///
/// Formes LEGITIMES (a ne PAS signaler) :
///   - `await tache`                  -- composition normale
///   - `tache.GetAwaiter().GetResult()` -- UNIQUEMENT si la tache n'est PAS
///                                         issue de `Task` ou `Task<T>` (un
///                                         awaiter personnalise qui implemente
///                                         `INotifyCompletion` n'a pas le
///                                         pattern deadlock du TaskAwaiter)
///   - `monAwaiterPerso.GetResult()`  -- un awaiter custom peut avoir une
///                                         semantique differente (par exemple
///                                         synchrone-par-construction)
/// </summary>
[DiagnosticAnalyzer(LanguageNames.CSharp)]
public sealed class SyncOverAsyncAnalyzer : DiagnosticAnalyzer
{
    public const string DiagnosticId = "AGENTGUARD005";

    private static readonly DiagnosticDescriptor Rule = new(
        DiagnosticId,
        "Blocage synchrone via GetAwaiter().GetResult()",
        "GetAwaiter().GetResult() bloque une Task/{0} de maniere synchrone : remplacer par await",
        "Agentisme",
        DiagnosticSeverity.Warning,
        isEnabledByDefault: true,
        description: "Le code genere par agent qui synchronise une tache via .GetAwaiter().GetResult() expose au deadlock. Preferer await.");

    public override ImmutableArray<DiagnosticDescriptor> SupportedDiagnostics
        => ImmutableArray.Create(Rule);

    public override void Initialize(AnalysisContext context)
    {
        context.ConfigureGeneratedCodeAnalysis(GeneratedCodeAnalysisFlags.None);
        context.EnableConcurrentExecution();
        // On s'abonne aux INVOCATIONS : le noeud syntaxique pertinent est
        // l'appel a GetResult(). Le filtre syntaxique est "le membre est
        // appele par un appel a GetAwaiter() sur une expression de type
        // Task ou Task<T>" -- le type est verifie SEMANTIQUEMENT (pas de
        // recherche par nom), ce qui evince les awaiters personnalises
        // et les methodes homonymes.
        context.RegisterSyntaxNodeAction(AnalyzeInvocation, SyntaxKind.InvocationExpression);
    }

    private static void AnalyzeInvocation(SyntaxNodeAnalysisContext ctx)
    {
        var inv = (InvocationExpressionSyntax)ctx.Node;

        // 1. Filtre syntaxique bon marche : le membre invoque s'appelle
        //    GetResult. Un awaiter custom peut s'appeler autrement, mais
        //    la cible de ce diagnostic est precisement le pattern
        //    canonique `.GetAwaiter().GetResult()` -- on accepte donc
        //    de laisser passer les autres noms (ils relevent d'un autre
        //    analyseur, ou ils sont exempts par construction).
        if (inv.Expression is not MemberAccessExpressionSyntax member) return;
        if (member.Name.Identifier.ValueText is not "GetResult") return;

        // 2. Filtre syntaxique : le receiver du GetResult() est lui-meme
        //    un appel a GetAwaiter() (forme canonique de la machine a etats
        //    d'une tache). `monAwaiter.GetResult()` directement (sans
        //    passer par GetAwaiter) echoue a ce filtre -- ce qui est
        //    coherent : ce code appelle une methode sur une variable
        //    deja awaiter, pas sur une tache.
        if (member.Expression is not InvocationExpressionSyntax awaiterCall) return;
        if (awaiterCall.Expression is not MemberAccessExpressionSyntax awaiterMember) return;
        if (awaiterMember.Name.Identifier.ValueText is not "GetAwaiter") return;

        // 3. Filtre semantique : le type de l'expression sur laquelle
        //    GetAwaiter() est appele est-il Task ou Task<T> ? On utilise
        //    le modele semantique -- un `customAwaitable.GetAwaiter()`
        //    ou `ValueTask<int>.GetAwaiter()` ne correspond PAS, le code
        //    est alors legitime. C'est la cle anti-faux-positif.
        var tacheExpr = awaiterMember.Expression;
        var typeInfo = ctx.SemanticModel.GetTypeInfo(tacheExpr);
        if (typeInfo.Type is not INamedTypeSymbol ct) return;
        if (ct.MetadataName is not ("Task" or "Task`1")) return;
        // Defence supplementaire : le namespace doit etre System.Threading.Tasks
        // (evince un `Task` local qui porterait le meme nom simple).
        if (ct.ContainingNamespace?.ToDisplayString() != "System.Threading.Tasks") return;

        ctx.ReportDiagnostic(Diagnostic.Create(
            Rule, inv.GetLocation(), ct.MetadataName));
    }
}
