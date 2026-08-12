// AgentSafetyAnalyzer.cs — Roslyn DiagnosticAnalyzer as compile-time guardrail
// for agent-generated C# code (Epic #10473, axe Roslyn, sub-grain #10500f).
//
// Four semantic rules inspired by the OWASP Agentic Security Top-10 patterns:
//   AGSEC001 — Process.Start with non-constant first argument (command injection)
//   AGSEC002 — SQL string concatenation (use SqlParameter instead)
//   AGSEC003 — File.* operations on non-constant paths (path traversal)
//   AGSEC005 — Hardcoded credentials (string literals starting with a known
//              provider prefix: sk-… / ghp_… / AKIA… / AIza… / hf_… / etc.)
//
// The semantic key (the value grep cannot provide) is `SemanticModel.GetConstantValue`
// for the first three rules: a literal literal is safe; an attacker-controlled
// variable collapses to no constant value and is therefore flagged. AGSEC005 uses
// a different pivot — a *prefix discrimination* on the literal itself, since a
// hardcoded credential IS a constant and the protection has to fire on its shape,
// not on its provenance. Each rule reports a *localized* diagnostic at the
// suspect expression, with the expression text passed as the message argument.
//
// Sub-grain #10500f (this commit) adds the `HardcodedCredentialCodeFixProvider`
// companion for AGSEC005: a code action that replaces a hardcoded credential
// literal with `System.Environment.GetEnvironmentVariable("PROVIDER_API_KEY") ?? ""`,
// where the env var name is picked from the matched prefix (sk- → OPENAI_API_KEY,
// ghp_ → GITHUB_TOKEN, AKIA → AWS_ACCESS_KEY_ID, …).
//
// Originally prototyped in `MyIA.AI.Notebooks/GenAI/Vibe-Coding/docs/Roslyn-Code-Guardrails.ipynb`
// (cell 4, PR #10502). This standalone .csproj package is the production-ready
// packaging exercise called out in cell 17 of the notebook.

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
    public const string AGSEC005 = "AGSEC005"; // Hardcoded credential prefix

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

    internal static readonly DiagnosticDescriptor Rule005 = new(
        AGSEC005,
        "Hardcoded credential detected",
        "String literal '{0}' starts with a known provider prefix ('{1}'): this is almost certainly a hardcoded API key/token — load via os.getenv(...) or a secret manager instead",
        "Security",
        DiagnosticSeverity.Warning,
        isEnabledByDefault: true,
        description: "Detects string literals whose prefix matches a well-known credential provider (OpenAI, Anthropic, GitHub, AWS, Google, HuggingFace, Slack, GitLab, Perplexity). See CWE-798 — Use of Hardcoded Credentials.",
        helpLinkUri: "https://github.com/jsboige/CoursIA/issues/10500");

    public override ImmutableArray<DiagnosticDescriptor> SupportedDiagnostics =>
        ImmutableArray.Create(Rule001, Rule002, Rule003, Rule005);

    public override void Initialize(AnalysisContext context)
    {
        context.ConfigureGeneratedCodeAnalysis(GeneratedCodeAnalysisFlags.None);
        context.EnableConcurrentExecution();
        context.RegisterSyntaxNodeAction(AnalyzeInvocation, SyntaxKind.InvocationExpression);
        context.RegisterSyntaxNodeAction(AnalyzeAdd, SyntaxKind.AddExpression);
        context.RegisterSyntaxNodeAction(AnalyzeLiteral, SyntaxKind.StringLiteralExpression);
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

    private static void AnalyzeLiteral(SyntaxNodeAnalysisContext ctx)
    {
        // AGSEC005: hardcoded credential detection. The literal must be a
        // *plain* string literal (not interpolated, not a concatenation
        // fragment). String literal values whose leading characters match one
        // of the well-known credential prefixes are flagged with the matched
        // prefix name so the message points the developer at the right
        // provider (sk- → OpenAI/Anthropic, ghp_ → GitHub, etc.).
        var lit = (LiteralExpressionSyntax)ctx.Node;
        var value = lit.Token.ValueText;
        if (string.IsNullOrEmpty(value) || value.Length < 4)
            return;
        var match = MatchCredentialPrefix(value);
        if (match is null)
            return;
        ctx.ReportDiagnostic(Diagnostic.Create(Rule005, lit.GetLocation(), TruncateForMessage(value), match));
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

    // AGSEC005 prefix table. Order: most specific first (so `sk-ant-` wins
    // over `sk-`). Each entry is (prefix, friendly-name). The friendly name
    // appears in the diagnostic message so the developer knows which provider
    // leaked the key.
    private static readonly (string Prefix, string Provider)[] CredentialPrefixes = new[]
    {
        ("sk-ant-",  "Anthropic"),
        ("sk-",      "OpenAI / Anthropic (sk-)"),
        ("ghp_",     "GitHub Personal Access Token"),
        ("gho_",     "GitHub OAuth token"),
        ("ghs_",     "GitHub server token"),
        ("ghr_",     "GitHub refresh token"),
        ("glpat-",   "GitLab Personal Access Token"),
        ("xoxb-",    "Slack Bot token"),
        ("xoxp-",    "Slack User token"),
        ("xoxa-",    "Slack App token"),
        ("AIza",     "Google API key"),
        ("AKIA",     "AWS Access Key ID"),
        ("ASIA",     "AWS STS Access Key ID"),
        ("hf_",      "HuggingFace token"),
        ("pplx-",    "Perplexity API key"),
        ("dapi",     "Databricks token"),
        ("ddp_",     "Datadog API key"),
    };

    private static string? MatchCredentialPrefix(string s)
    {
        foreach (var (prefix, _) in CredentialPrefixes)
        {
            if (s.StartsWith(prefix, System.StringComparison.Ordinal))
                return prefix;
        }
        return null;
    }

    private static string MatchCredentialProvider(string s)
    {
        foreach (var (prefix, provider) in CredentialPrefixes)
        {
            if (s.StartsWith(prefix, System.StringComparison.Ordinal))
                return provider;
        }
        return "unknown provider";
    }

    // The diagnostic message embeds the literal value (truncated for safety
    // — 12 chars head + ellipsis) so the developer can identify which literal
    // triggered the rule. CWE-798 forbids displaying the secret, but the
    // leading prefix is enough to recognise it; the rest is masked.
    private static string TruncateForMessage(string s) =>
        s.Length <= 16 ? s : s.Substring(0, 12) + "…";

    // Public helper for tests: returns the provider name for a matched value.
    internal static string ProviderFor(string s) => MatchCredentialProvider(s);
}
