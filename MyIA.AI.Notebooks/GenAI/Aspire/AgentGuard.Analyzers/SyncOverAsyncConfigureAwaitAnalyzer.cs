using System.Collections.Immutable;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Diagnostics;

namespace AgentGuard.Analyzers;

/// <summary>
/// AGENTGUARD005b : variante syntaxique d'AGENTGUARD005, attrapee par un
/// analyseur dedie pour des raisons pedagogiques.
///
/// Le defaut : l'agent genere
/// `tache.ConfigureAwait(false).GetAwaiter().GetResult()` en croyant que
/// `ConfigureAwait(false)` "rend ca safe". **C'est faux.** ConfigureAwait
/// reduit le risque de deadlock par capture de SynchronizationContext,
/// mais l'appel `.GetAwaiter().GetResult()` BLOQUE TOUJOURS le thread --
/// le sync-over-async reste entier.
///
/// Pourquoi un analyseur dedie plutot qu'une extension d'AGENTGUARD005 :
/// le message diagnostique doit expliquer POURQUOI ConfigureAwait ne
/// sauve pas, pas seulement signaler la meme faute avec un enonce
/// generique. Sur ce depot la valeur d'un analyseur est d'expliquer, pas
/// seulement de hurler. (cf voie 2 dans l'issue #13842.)
///
/// Formes LEGITIMES (a ne PAS signaler) :
///   - `await tache`                       -- composition normale
///   - `tache.ConfigureAwait(false).GetAwaiter().GetResult()` -- UNIQUEMENT
///                                             si le type EN AMONT du
///                                             ConfigureAwait n'est PAS
///                                             `System.Threading.Tasks.Task`
///                                             ou `Task<T>` (exemption
///                                             semantique exacte comme
///                                             AGENTGUARD005)
///   - `monAwaiterPerso.GetAwaiter().GetResult()` -- awaiter custom
///
/// Faux positifs explicitement testes (verifier Verifier/samples/) :
///   - `MonAwaitable.GetAwaiter().GetResult()`            -- awaiter custom
///   - `Task.Delay(100).ConfigureAwait(false).IsCompleted` -- pas GetResult
///   - `valueTask.ConfigureAwait(false).GetAwaiter().GetResult()` -- ValueTask
/// </summary>
[DiagnosticAnalyzer(LanguageNames.CSharp)]
public sealed class SyncOverAsyncConfigureAwaitAnalyzer : DiagnosticAnalyzer
{
    public const string DiagnosticId = "AGENTGUARD005b";

    private static readonly DiagnosticDescriptor Rule = new(
        DiagnosticId,
        "Blocage synchrone apres ConfigureAwait : le deadlock reste entier",
        "ConfigureAwait({0}) ne protege pas du sync-over-async : .GetAwaiter().GetResult() bloque toujours le thread, remplacer par await",
        "Agentisme",
        DiagnosticSeverity.Warning,
        isEnabledByDefault: true,
        description: "L'agent genere du code en croyant que ConfigureAwait(false) suffit a rendre l'appel safe. Faux : ConfigureAwait reduit la capture de SynchronizationContext, mais .GetAwaiter().GetResult() bloque le thread quoi qu'il arrive. Seul await evite le deadlock.");

    public override ImmutableArray<DiagnosticDescriptor> SupportedDiagnostics
        => ImmutableArray.Create(Rule);

    public override void Initialize(AnalysisContext context)
    {
        context.ConfigureGeneratedCodeAnalysis(GeneratedCodeAnalysisFlags.None);
        context.EnableConcurrentExecution();
        // Comme AGENTGUARD005 : on s'abonne aux INVOCATIONS, le noeud
        // pertinent est l'appel a GetResult(). La cible est ici la forme
        // `tache.ConfigureAwait(arg).GetAwaiter().GetResult()`.
        context.RegisterSyntaxNodeAction(AnalyzeInvocation, SyntaxKind.InvocationExpression);
    }

    private static void AnalyzeInvocation(SyntaxNodeAnalysisContext ctx)
    {
        var inv = (InvocationExpressionSyntax)ctx.Node;

        // 1. Filtre syntaxique bon marche : le membre invoque est GetResult.
        if (inv.Expression is not MemberAccessExpressionSyntax member) return;
        if (member.Name.Identifier.ValueText is not "GetResult") return;

        // 2. Le receiver de GetResult() doit etre lui-meme un appel a
        //    GetAwaiter() : `... .GetAwaiter().GetResult()`.
        if (member.Expression is not InvocationExpressionSyntax awaiterCall) return;
        if (awaiterCall.Expression is not MemberAccessExpressionSyntax awaiterMember) return;
        if (awaiterMember.Name.Identifier.ValueText is not "GetAwaiter") return;

        // 3. Le receiver de GetAwaiter() doit etre lui-meme un appel a
        //    ConfigureAwait(...) : c'est le pivot de cette variante.
        //    `tache.ConfigureAwait(false).GetAwaiter().GetResult()`.
        if (awaiterMember.Expression is not InvocationExpressionSyntax configureAwaitCall) return;
        if (configureAwaitCall.Expression is not MemberAccessExpressionSyntax configureAwaitMember) return;
        if (configureAwaitMember.Name.Identifier.ValueText is not "ConfigureAwait") return;

        // 4. L'argument de ConfigureAwait doit etre un literal bool (true
        //    OU false). Les formes
        //    `tache.ConfigureAwait(condition).GetAwaiter().GetResult()`
        //    ou `ConfigureAwait()` sans argument sont exclues du scope
        //    (l'analyse semantique de l'argument reste possible mais
        //    excede le bug #13842 ; le rapport signal/de-bruit est
        //    meilleur en literal-strict).
        if (configureAwaitCall.ArgumentList.Arguments.Count != 1) return;
        var argExpr = configureAwaitCall.ArgumentList.Arguments[0].Expression;
        if (argExpr is not (LiteralExpressionSyntax { Token.Value: bool })) return;
        var configureAwaitValue = ((LiteralExpressionSyntax)argExpr).Token.Value;

        // 5. Filtre semantique cle anti-faux-positif : le type de l'
        //    expression sur laquelle ConfigureAwait() est appele doit
        //    etre `System.Threading.Tasks.Task` ou `Task<T>`. C'est la
        //    meme borne qu'AGENTGUARD005 transposée sur le receiver du
        //    ConfigureAwait (et non sur le receiver du GetAwaiter --
        //    celui-ci serait de type `ConfiguredTaskAwaitable`, qui ne
        //    discrimine rien). Cette cle evince :
        //      - awaiters custom (le type n'est pas Task)
        //      - ValueTask<T> (le type n'est pas Task)
        //      - homonymes locaux (le namespace doit etre exact)
        var tacheExpr = configureAwaitMember.Expression;
        var typeInfo = ctx.SemanticModel.GetTypeInfo(tacheExpr);
        if (typeInfo.Type is not INamedTypeSymbol ct) return;
        if (ct.MetadataName is not ("Task" or "Task`1")) return;
        if (ct.ContainingNamespace?.ToDisplayString() != "System.Threading.Tasks") return;

        ctx.ReportDiagnostic(Diagnostic.Create(
            Rule, inv.GetLocation(), configureAwaitValue));
    }
}
