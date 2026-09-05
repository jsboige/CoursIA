using System.Collections.Immutable;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.Diagnostics;

namespace AgentGuard.Analyzers;

/// <summary>
/// AGENTGUARD001 : blocage synchrone d'une Task (.Result / .Wait()).
///
/// Pattern typique du code d'agent genere : appeler une tache asynchrone
/// (appel LLM, streaming, canal) depuis du code synchrone en la bloquant.
/// Le garde-fou vit DANS la compilation -- `dotnet build` rend le diagnostic
/// sans aucun outil supplementaire (la these du notebook 06 de la serie Aspire,
/// Epic #10473 axe Roslyn).
/// </summary>
[DiagnosticAnalyzer(LanguageNames.CSharp)]
public sealed class TaskResultBlockAnalyzer : DiagnosticAnalyzer
{
    public const string DiagnosticId = "AGENTGUARD001";

    private static readonly DiagnosticDescriptor Rule = new(
        DiagnosticId,
        "Blocage synchrone d'une Task",
        "Task bloquee de maniere synchrone ({0}) : deadlock potentiel en code d'agent",
        "Agentisme",
        DiagnosticSeverity.Warning,
        isEnabledByDefault: true,
        description: "Le code genere par agent qui bloque une Task via .Result/.Wait() expose au deadlock.");

    public override ImmutableArray<DiagnosticDescriptor> SupportedDiagnostics
        => ImmutableArray.Create(Rule);

    public override void Initialize(AnalysisContext context)
    {
        context.ConfigureGeneratedCodeAnalysis(GeneratedCodeAnalysisFlags.None);
        context.EnableConcurrentExecution();
        // Le membre accede (.Result, .Wait) est un MemberAccessExpression --
        // on s'abonne a CE noeud syntaxique, pas a toute l'arborescence.
        context.RegisterSyntaxNodeAction(AnalyzeNode, SyntaxKind.SimpleMemberAccessExpression);
    }

    private static void AnalyzeNode(SyntaxNodeAnalysisContext ctx)
    {
        var node = (Microsoft.CodeAnalysis.CSharp.Syntax.MemberAccessExpressionSyntax)ctx.Node;

        // 1. Filtre syntaxique bon marche : le membre s'appelle Result ou Wait.
        if (node.Name is not { Identifier.ValueText: "Result" or "Wait" }) return;

        // 2. Filtre semantique : le membre appartient bien a Task / Task<T>.
        //    (Evince les faux positifs : un Result<T> monadique, un .Wait()
        //    de type custom.) C'est le modele semantique qui tranchera.
        if (ctx.SemanticModel.GetSymbolInfo(node).Symbol is not { } member) return;
        if (member.ContainingType is not INamedTypeSymbol ct
            || ct.MetadataName is not ("Task" or "Task`1")) return;

        ctx.ReportDiagnostic(Diagnostic.Create(
            Rule, node.GetLocation(), "." + node.Name.Identifier.ValueText));
    }
}
