using System.Collections.Immutable;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Diagnostics;

namespace AgentGuard.Analyzers;

/// <summary>
/// AGENTGUARD002 : methode async void hors gestionnaire d'evenement.
///
/// Second pattern typique du code genere par agent : ecrire
/// `async void FaitUneChose()` parce que la signature "ressemble" a une
/// async Task. Les consequences sont silencieuses et mortelles : la
/// methode n'est pas attendable (impossible a composer, a tester), et ses
/// exceptions echappent a tout mécanisme d'observation -- une seule
/// suffit a faire planter le process entier.
///
/// La forme LEGITIME est le gestionnaire d'evenement :
/// `async void OnClick(object sender, EventArgs e)`. On l'exempte par sa
/// signature canonique -- premier parametre object, second parametre
/// derive de System.EventArgs -- parce que le contrat des evenements C#
/// EXIGE void, l'agent n'a pas le choix. C'est l'exemption démontree par
/// le terrain samples/AsyncVoidHandlerExempt.cs.
/// </summary>
[DiagnosticAnalyzer(LanguageNames.CSharp)]
public sealed class AsyncVoidAnalyzer : DiagnosticAnalyzer
{
    public const string DiagnosticId = "AGENTGUARD002";

    private static readonly DiagnosticDescriptor Rule = new(
        DiagnosticId,
        "async void hors gestionnaire d'evenement",
        "La methode async void '{0}' echappe a toute attente -- exceptions non observees, process mort",
        "Agentisme",
        DiagnosticSeverity.Warning,
        isEnabledByDefault: true,
        description: "Une methode async void n'est ni attendable ni testable ; ses exceptions ne sont jamais observees. Reserver async void aux gestionnaires d'evenements.");

    public override ImmutableArray<DiagnosticDescriptor> SupportedDiagnostics
        => ImmutableArray.Create(Rule);

    public override void Initialize(AnalysisContext context)
    {
        context.ConfigureGeneratedCodeAnalysis(GeneratedCodeAnalysisFlags.None);
        context.EnableConcurrentExecution();
        // Contrairement a AGENTGUARD001 (abonne a un noeud d'acces membre),
        // le defaut vit sur la DECLARATION elle-meme.
        context.RegisterSyntaxNodeAction(AnalyzeMethod, SyntaxKind.MethodDeclaration);
    }

    private static void AnalyzeMethod(SyntaxNodeAnalysisContext ctx)
    {
        var method = (MethodDeclarationSyntax)ctx.Node;

        // 1. Filtre syntaxique : modificateur async + type de retour void.
        if (!method.Modifiers.Any(SyntaxKind.AsyncKeyword)) return;
        if (method.ReturnType is not PredefinedTypeSyntax { Keyword.ValueText: "void" }) return;

        // 2. Exemption : signature de gestionnaire d'evenement. Le contrat
        //    C# des handlers impose void -- l'agent n'y peut rien, on ne
        //    signale pas. Tranchee par le modele semantique (pas par le nom
        //    du parametre) : (object, T) ou T : System.EventArgs.
        if (EstHandlerEvenement(method, ctx)) return;

        ctx.ReportDiagnostic(Diagnostic.Create(
            Rule, method.Identifier.GetLocation(), method.Identifier.ValueText));
    }

    private static bool EstHandlerEvenement(MethodDeclarationSyntax method, SyntaxNodeAnalysisContext ctx)
    {
        var parameters = method.ParameterList.Parameters;
        if (parameters.Count < 2) return false;

        // Premier parametre exactement object (le "sender").
        var senderType = ctx.SemanticModel.GetTypeInfo(parameters[0].Type).Type;
        if (senderType?.SpecialType != SpecialType.System_Object) return false;

        // Second parametre derive de System.EventArgs (ou l'est lui-meme).
        var argsType = ctx.SemanticModel.GetTypeInfo(parameters[1].Type).Type;
        if (argsType is null || argsType.TypeKind == TypeKind.Error) return false;
        return EstEventArgsOuDerive(argsType, ctx.Compilation);
    }

    private static bool EstEventArgsOuDerive(ITypeSymbol type, Compilation compilation)
    {
        var eventArgs = compilation.GetTypeByMetadataName("System.EventArgs");
        if (eventArgs is null) return false;

        var courant = type;
        while (courant is not null)
        {
            if (SymbolEqualityComparer.Default.Equals(courant, eventArgs)) return true;
            // Interfaces implementees : EventArgs implementsNothing en pratique,
            // mais la boucle d'heritage couvre le cas general.
            courant = courant.BaseType;
        }
        return false;
    }
}
