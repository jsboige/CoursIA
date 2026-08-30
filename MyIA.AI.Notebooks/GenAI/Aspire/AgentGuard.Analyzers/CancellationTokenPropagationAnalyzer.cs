using System.Collections.Immutable;
using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Diagnostics;
using Microsoft.CodeAnalysis.Operations;

namespace AgentGuard.Analyzers;

/// <summary>
/// AGENTGUARD004 : perte d'un CancellationToken disponible.
///
/// Une méthode d'agent reçoit souvent un token depuis la requête HTTP ou le
/// BackgroundService. Si elle appelle une opération dont la signature expose
/// explicitement CancellationToken mais omet cet argument optionnel, l'arrêt
/// demandé ne traverse plus la chaîne. L'analyse est entièrement sémantique :
/// le type doit être System.Threading.CancellationToken, sans heuristique sur
/// le nom de la méthode ni du paramètre.
/// </summary>
[DiagnosticAnalyzer(LanguageNames.CSharp)]
public sealed class CancellationTokenPropagationAnalyzer : DiagnosticAnalyzer
{
    public const string DiagnosticId = "AGENTGUARD004";

    private static readonly DiagnosticDescriptor Rule = new(
        DiagnosticId,
        "CancellationToken disponible mais non propage",
        "L'appel à '{0}' omet CancellationToken alors que '{1}' est disponible dans la méthode englobante",
        "Agentisme",
        DiagnosticSeverity.Warning,
        isEnabledByDefault: true,
        description: "Propager le CancellationToken disponible aux opérations annulables afin que l'arrêt traverse toute la chaîne d'agent.");

    public override ImmutableArray<DiagnosticDescriptor> SupportedDiagnostics
        => ImmutableArray.Create(Rule);

    public override void Initialize(AnalysisContext context)
    {
        context.ConfigureGeneratedCodeAnalysis(GeneratedCodeAnalysisFlags.None);
        context.EnableConcurrentExecution();
        context.RegisterOperationAction(AnalyzeInvocation, OperationKind.Invocation);
    }

    private static void AnalyzeInvocation(OperationAnalysisContext ctx)
    {
        var invocation = (IInvocationOperation)ctx.Operation;
        var cancellationToken = ctx.Compilation.GetTypeByMetadataName(
            "System.Threading.CancellationToken");
        if (cancellationToken is null) return;

        var tokenParameter = invocation.TargetMethod.Parameters.FirstOrDefault(
            parameter => SymbolEqualityComparer.Default.Equals(
                parameter.Type, cancellationToken));
        if (tokenParameter is null) return;

        // Roslyn matérialise un argument optionnel omis avec ArgumentKind.DefaultValue.
        // Seul un argument Explicit prouve que l'appelant a propagé un token.
        var tokenIsExplicit = invocation.Arguments.Any(argument =>
            SymbolEqualityComparer.Default.Equals(argument.Parameter, tokenParameter)
            && argument.ArgumentKind == ArgumentKind.Explicit);
        if (tokenIsExplicit) return;

        var availableToken = FindAvailableToken(ctx.ContainingSymbol, cancellationToken);
        if (availableToken is null) return;

        ctx.ReportDiagnostic(Diagnostic.Create(
            Rule,
            invocation.Syntax.GetLocation(),
            invocation.TargetMethod.ToDisplayString(SymbolDisplayFormat.MinimallyQualifiedFormat),
            availableToken.Name));
    }

    private static IParameterSymbol FindAvailableToken(
        ISymbol symbol,
        INamedTypeSymbol cancellationToken)
    {
        // Une lambda ou une fonction locale peut capturer le token de sa méthode
        // englobante : on remonte donc la chaîne de symboles, sans sortir du type.
        for (var current = symbol; current is not null && current is not INamedTypeSymbol;
             current = current.ContainingSymbol)
        {
            if (current is not IMethodSymbol method) continue;

            var token = method.Parameters.FirstOrDefault(parameter =>
                SymbolEqualityComparer.Default.Equals(
                    parameter.Type, cancellationToken));
            if (token is not null) return token;
        }

        return null;
    }
}
