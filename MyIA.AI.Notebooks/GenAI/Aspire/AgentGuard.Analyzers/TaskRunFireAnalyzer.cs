using System.Collections.Immutable;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Diagnostics;

namespace AgentGuard.Analyzers;

/// <summary>
/// AGENTGUARD003 : invocation nue de Task.Run, tache non observee.
///
/// Troisieme pattern typique du code genere par agent : ecrire
/// `Task.Run(() => Travail())` comme enonce autonome. La signature est
/// honnete (la methode rend une Task, pas void), MAIS la tache resultante
/// n'est ni attendue (await), ni affectee a une variable, ni retournee,
/// ni explicitement ignoree via discard (`_ =`). Elle s'execute en arriere-
/// plan ; ses exceptions ne sont observees par personne. A la finalisation
/// d'une telle tache fautive, le runtime declenche
/// `TaskScheduler.UnobservedTaskException`, un evenement qui porte une
/// `AggregateException` collectant les exceptions internes -- le defaut
/// (.NET 4.5+) est d'absorber l'evenement et de laisser le process vivre,
/// mais ce comportement est configurable et n'est pas garanti.
///
/// Formes LEGITIMES (a ne PAS signaler) :
///   - `await Task.Run(...)`            -- tache observee
///   - `var t = Task.Run(...)`          -- tache recuperee (composee ou attendue plus tard)
///   - `_ = Task.Run(...)`              -- discard explicite (assume, volontaire)
///   - `return Task.Run(...)`           -- tache retournee a l'appelant
///   - homonyme custom (autre type, autre signature) -- filtre semantique
/// </summary>
[DiagnosticAnalyzer(LanguageNames.CSharp)]
public sealed class TaskRunFireAnalyzer : DiagnosticAnalyzer
{
    public const string DiagnosticId = "AGENTGUARD003";

    private static readonly DiagnosticDescriptor Rule = new(
        DiagnosticId,
        "Task.Run feu, tache non observee",
        "Task.Run '{0}' lance une tache non observee -- exceptions perdues, comportement indefini",
        "Agentisme",
        DiagnosticSeverity.Warning,
        isEnabledByDefault: true,
        description: "Une invocation nue de Task.Run execute la tache en arriere-plan ; ses exceptions ne sont observees par personne. Utiliser await, affecter a une variable, retourner ou discarder explicitement (_ =).");

    public override ImmutableArray<DiagnosticDescriptor> SupportedDiagnostics
        => ImmutableArray.Create(Rule);

    public override void Initialize(AnalysisContext context)
    {
        context.ConfigureGeneratedCodeAnalysis(GeneratedCodeAnalysisFlags.None);
        context.EnableConcurrentExecution();
        // On s'abonne aux INVOCATIONS (le noeud Task.Run(...)). Le diagnostic
        // porte sur l'invocation, pas sur un membre -- le membre ici est un
        // IdentifierName (Run), pas un MemberAccessExpression, donc on ne peut
        // pas reutiliser la strategie d'AGENTGUARD001.
        context.RegisterSyntaxNodeAction(AnalyzeInvocation, SyntaxKind.InvocationExpression);
    }

    private static void AnalyzeInvocation(SyntaxNodeAnalysisContext ctx)
    {
        var inv = (InvocationExpressionSyntax)ctx.Node;

        // 1. Filtre semantique : la methode invoquee est bien Task.Run.
        //    Reutilise le pattern d'AGENTGUARD001 : resoudre le symbole et
        //    verifier que la ContainingType est Task (non-generique).
        //    Evince les methodes homonymes : un type custom `MonService.Run`
        //    ne doit PAS declencher AGENTGUARD003.
        if (ctx.SemanticModel.GetSymbolInfo(inv).Symbol is not IMethodSymbol method) return;
        if (method.ContainingType is not INamedTypeSymbol ct
            || ct.MetadataName is not "Task"
            || ct.ContainingNamespace?.ToDisplayString() != "System.Threading.Tasks") return;
        if (method.MetadataName is not "Run") return;

        // 2. Filtre syntaxique : la seule forme signalee est l'ExpressionStatement
        //    nu (l'invocation est l'integralite de l'enonce). Les autres formes
        //    -- await, affectation, discard, return, argument d'une autre
        //    invocation -- ne sont JAMAIS signalees.
        //
        //    Cas particulier `_ = Task.Run(...)` : Roslyn represente le discard
        //    comme un AssignmentExpression avec Left = IdentifierName("_"),
        //    donc le parent n'est PAS un ExpressionStatement nu -- il est
        //    rattrape par le filtre "n'est pas ExpressionStatement" et tombe
        //    naturellement dans la branche exempt. Le test terrain le verifie.
        if (inv.Parent is not ExpressionStatementSyntax) return;

        ctx.ReportDiagnostic(Diagnostic.Create(
            Rule, inv.GetLocation(), inv.ToString()));
    }
}
