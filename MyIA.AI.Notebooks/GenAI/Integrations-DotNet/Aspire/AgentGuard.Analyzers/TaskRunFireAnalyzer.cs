using System.Collections.Immutable;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Diagnostics;

namespace AgentGuard.Analyzers;

/// <summary>
/// AGENTGUARD003 : invocation nue d'une fabrique de Task, tache non observee.
///
/// Troisieme pattern typique du code genere par agent : ecrire
/// `Task.Run(() => Travail())`, `Task.Factory.StartNew(() => Travail())`
/// ou la variante generique via `Task<TResult>.Factory` comme enonce autonome.
/// La signature est
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
///   - `await Task.Run(...)`                    -- tache observee
///   - `var t = Task.Factory.StartNew(...)`     -- tache recuperee
///   - `_ = Task.Factory.StartNew(...)`         -- discard explicite
///   - `return Task.Run(...)`                   -- tache retournee
///   - homonyme custom (autre type, autre signature) -- filtre semantique
/// </summary>
[DiagnosticAnalyzer(LanguageNames.CSharp)]
public sealed class TaskRunFireAnalyzer : DiagnosticAnalyzer
{
    public const string DiagnosticId = "AGENTGUARD003";

    private static readonly DiagnosticDescriptor Rule = new(
        DiagnosticId,
        "Fabrique de Task nue, tache non observee",
        "L'appel '{0}' lance une tache non observee -- exceptions potentiellement perdues, defaillance silencieuse",
        "Agentisme",
        DiagnosticSeverity.Warning,
        isEnabledByDefault: true,
        description: "Une invocation nue de Task.Run, Task.Factory.StartNew ou Task<TResult>.Factory.StartNew execute la tache en arriere-plan ; ses exceptions ne sont observees par personne. Utiliser await, affecter a une variable, retourner ou discarder explicitement (_ =).");

    public override ImmutableArray<DiagnosticDescriptor> SupportedDiagnostics
        => ImmutableArray.Create(Rule);

    public override void Initialize(AnalysisContext context)
    {
        context.ConfigureGeneratedCodeAnalysis(GeneratedCodeAnalysisFlags.None);
        context.EnableConcurrentExecution();
        // On s'abonne aux INVOCATIONS (Task.Run(...) ou StartNew(...)). Le
        // diagnostic porte sur l'appel complet et non sur un simple acces de
        // membre : la strategie d'AGENTGUARD001 ne s'applique donc pas ici.
        context.RegisterSyntaxNodeAction(AnalyzeInvocation, SyntaxKind.InvocationExpression);
    }

    private static void AnalyzeInvocation(SyntaxNodeAnalysisContext ctx)
    {
        var inv = (InvocationExpressionSyntax)ctx.Node;

        // 1. Filtre semantique : la methode invoquee est exactement Task.Run
        //    ou TaskFactory.StartNew. Les proprietes Task.Factory et
        //    Task<TResult>.Factory rendent respectivement TaskFactory et
        //    TaskFactory<TResult> : StartNew est defini sur ces fabriques,
        //    pas sur Task.
        //    Les noms seuls ne comptent pas : le namespace et le type contenant
        //    evincent MonService.Run et une TaskFactory homonyme.
        if (ctx.SemanticModel.GetSymbolInfo(inv).Symbol is not IMethodSymbol method) return;
        if (method.ContainingType is not INamedTypeSymbol ct
            || ct.ContainingNamespace?.ToDisplayString() != "System.Threading.Tasks") return;

        var isTaskRun = ct.MetadataName == "Task" && method.MetadataName == "Run";
        var isTaskFactoryStartNew = ct.MetadataName is "TaskFactory" or "TaskFactory`1"
            && method.MetadataName == "StartNew";
        if (!isTaskRun && !isTaskFactoryStartNew) return;

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
