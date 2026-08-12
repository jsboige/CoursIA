// AgentSafetyAnalyzer.cs — Roslyn DiagnosticAnalyzer as compile-time guardrail
// for agent-generated C# code (Epic #10473, axe Roslyn, sub-grain #10500c).
//
// Four semantic rules inspired by the OWASP Agentic Security Top-10 patterns:
//   AGSEC001 — Process.Start with non-constant first argument (command injection)
//   AGSEC002 — SQL string concatenation (use SqlParameter instead)
//   AGSEC003 — File.* operations on non-constant paths (path traversal)
//   AGSEC004 — HttpClient.Get*/Post*/Put*/Delete*/Send* with non-constant URL
//
// The semantic key (the value grep cannot provide) is `SemanticModel.GetConstantValue`:
// a literal literal is safe; an attacker-controlled variable collapses to no constant
// value and is therefore flagged. Each rule reports a *localized* diagnostic at the
// suspect expression, with the expression text passed as the message argument.
//
// Originally prototyped in `MyIA.AI.Notebooks/GenAI/Vibe-Coding/docs/Roslyn-Code-Guardrails.ipynb`
// (cell 4, PR #10502). This standalone .csproj package is the production-ready
// packaging exercise called out in cell 17 of the notebook. Sub-grain #10500c
// (this commit) extends the analyzer with AGSEC004 for HTTP client URL injection.

using System.Collections.Immutable;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Diagnostics;

namespace MyIA.AgentSafety;

[DiagnosticAnalyzer(LanguageNames.CSharp)]
public sealed class AgentSafetyAnalyzer : DiagnosticAnalyzer
{
    public const string AGSEC001 = "AGSEC001"; // Process.Start non-constant
    public const string AGSEC002 = "AGSEC002"; // SQL concatenation
    public const string AGSEC003 = "AGSEC003"; // File.* path non-constant
    public const string AGSEC004 = "AGSEC004"; // HttpClient.Get*/Post*/... non-constant URL

    internal static readonly DiagnosticDescriptor Rule001 = new(
        AGSEC001,
        "Command injection: non-constant Process.Start argument",
        "Process.Start is called with a non-constant value '{0}': attacker-controlled input could inject a command",
        "Security",
        DiagnosticSeverity.Warning,
        isEnabledByDefault: true,
        description: "Detects Process.Start calls whose first argument is not a compile-time constant. See OWASP Agentic Top-10 — Command Injection.",
        helpLinkUri: "https://github.com/jsboige/CoursIA/issues/10500");

    internal static readonly DiagnosticDescriptor Rule002 = new(
        AGSEC002,
        "SQL string concatenation",
        "SQL query built by concatenating '{0}': use a parameterized query (SqlParameter) instead",
        "Security",
        DiagnosticSeverity.Warning,
        isEnabledByDefault: true,
        description: "Detects SQL string concatenation patterns. Use parameterized queries to prevent SQL injection.",
        helpLinkUri: "https://github.com/jsboige/CoursIA/issues/10500");

    internal static readonly DiagnosticDescriptor Rule003 = new(
        AGSEC003,
        "Path traversal: non-constant file path",
        "File operation on a non-constant path '{0}': validate/contain the path before access",
        "Security",
        DiagnosticSeverity.Warning,
        isEnabledByDefault: true,
        description: "Detects File.Read/Write/Delete on a non-constant path. Validate the path against an allow-list before access.",
        helpLinkUri: "https://github.com/jsboige/CoursIA/issues/10500");

    internal static readonly DiagnosticDescriptor Rule004 = new(
        AGSEC004,
        "HTTP request: non-constant URL",
        "HttpClient.{0} called with non-constant URL '{1}': validate the URL against an allow-list (scheme + host + path) before sending",
        "Security",
        DiagnosticSeverity.Warning,
        isEnabledByDefault: true,
        description: "Detects HttpClient requests whose URL is not a compile-time constant. SSRF (Server-Side Request Forgery) is the canonical risk: an attacker-controlled URL may target internal services.",
        helpLinkUri: "https://github.com/jsboige/CoursIA/issues/10500");

    public override ImmutableArray<DiagnosticDescriptor> SupportedDiagnostics =>
        ImmutableArray.Create(Rule001, Rule002, Rule003, Rule004);

    public override void Initialize(AnalysisContext context)
    {
        context.ConfigureGeneratedCodeAnalysis(GeneratedCodeAnalysisFlags.None);
        context.EnableConcurrentExecution();
        context.RegisterSyntaxNodeAction(AnalyzeInvocation, SyntaxKind.InvocationExpression);
        context.RegisterSyntaxNodeAction(AnalyzeAdd, SyntaxKind.AddExpression);
    }

    private static void AnalyzeInvocation(SyntaxNodeAnalysisContext ctx)
    {
        var inv = (InvocationExpressionSyntax)ctx.Node;
        var name = inv.Expression.ToString();
        var args = inv.ArgumentList?.Arguments ?? default(SeparatedSyntaxList<ArgumentSyntax>);

        // AGSEC001: Process.Start whose first argument is NOT a compile-time constant
        if (name.Contains("Process.Start") && args.Count > 0 && !IsConstant(ctx, args[0].Expression))
            ctx.ReportDiagnostic(Diagnostic.Create(Rule001, args[0].GetLocation(), args[0].Expression));

        // AGSEC003: File.Read/Write/Delete on a non-constant path
        if ((name.StartsWith("File.Read") || name.StartsWith("File.Write") || name.StartsWith("File.Delete"))
            && args.Count > 0 && !IsConstant(ctx, args[0].Expression))
            ctx.ReportDiagnostic(Diagnostic.Create(Rule003, args[0].GetLocation(), args[0].Expression));

        // AGSEC004: HttpClient.Get*/Post*/Put*/Delete*/Send* on a non-constant URL
        if (IsHttpClientCall(name) && args.Count > 0 && !IsConstant(ctx, args[0].Expression))
            ctx.ReportDiagnostic(Diagnostic.Create(Rule004, args[0].GetLocation(), ExtractMethodName(name), args[0].Expression));
    }

    private static void AnalyzeAdd(SyntaxNodeAnalysisContext ctx)
    {
        // AGSEC002: "SELECT ..." + variable  (the textbook SQL injection primitive)
        var add = (BinaryExpressionSyntax)ctx.Node;
        if (add.Left is not LiteralExpressionSyntax lit || !lit.IsKind(SyntaxKind.StringLiteralExpression))
            return;
        if (!IsSqlLike(lit.Token.ValueText))
            return;
        ctx.ReportDiagnostic(Diagnostic.Create(Rule002, add.GetLocation(), add.Right));
    }

    // AGSEC004: Heuristic detection of HttpClient request methods. Matches:
    //   HttpClient.GetAsync / GetStringAsync / PostAsync / PutAsync / DeleteAsync
    //   HttpClient.SendAsync
    // Plus the synchronous variants (GetByteArray, etc.) when invoked on an
    // HttpClient field. The pattern is intentionally narrow: only invocation
    // expressions whose callee ends in one of the canonical request methods.
    private static bool IsHttpClientCall(string name)
    {
        // The expression may be `httpClient.GetAsync` (MemberAccessExpression)
        // or `client.GetStringAsync(url)` — match by suffix.
        foreach (var suffix in HttpClientMethodSuffixes)
        {
            if (name.EndsWith("." + suffix, System.StringComparison.Ordinal))
                return true;
        }
        return false;
    }

    private static readonly string[] HttpClientMethodSuffixes = new[]
    {
        "GetAsync", "GetStringAsync", "GetByteArrayAsync", "GetStreamAsync",
        "PostAsync", "PutAsync", "DeleteAsync", "PatchAsync", "HeadAsync",
        "SendAsync",
    };

    private static string ExtractMethodName(string name)
    {
        var dot = name.LastIndexOf('.');
        return dot >= 0 ? name.Substring(dot + 1) : name;
    }

    // The semantic key: ask the compiler whether the expression folds to a constant.
    // A literal literal is safe; an attacker-controlled variable collapses to no value
    // and is therefore flagged. This is what `grep Process.Start` cannot distinguish.
    private static bool IsConstant(SyntaxNodeAnalysisContext ctx, ExpressionSyntax expr) =>
        ctx.SemanticModel.GetConstantValue(expr).HasValue;

    private static bool IsSqlLike(string s)
    {
        var u = s.ToUpperInvariant();
        return u.Contains("SELECT ") || u.Contains("INSERT ") ||
               u.Contains("UPDATE ") || u.Contains("DELETE ");
    }
}
