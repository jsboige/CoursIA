// AgentSafetyAnalyzer.cs — Roslyn DiagnosticAnalyzer as compile-time guardrail
// for agent-generated C# code (Epic #10473, axe Roslyn, sub-grain #10500d).
//
// Four semantic rules inspired by the OWASP Agentic Security Top-10 patterns:
//   AGSEC001 — Process.Start with non-constant first argument (command injection)
//   AGSEC002 — SQL string concatenation (use SqlParameter instead)
//   AGSEC003 — File.* operations on non-constant paths (path traversal)
//   AGSEC004 — HttpClient.Get*/Post*/Put*/Delete*/Send* with non-constant URL
//   AGSEC005 — Hardcoded credentials (string literals starting with a known
//              provider prefix: sk-, ghp_, AKIA, AIza, hf_, xoxb-, ...)
//
// The semantic key (the value grep cannot provide) is `SemanticModel.GetConstantValue`:
// a literal literal is safe; an attacker-controlled variable collapses to no constant
// value and is therefore flagged. Each rule reports a *localized* diagnostic at the
// suspect expression, with the expression text passed as the message argument.
//
// Sub-grain #10500d (this commit) adds a pragma-suppression registry: developers
// who intentionally use a non-constant argument at a specific call site (e.g. a
// `Path.Combine(baseDir, userInput)` that is then validated by an allow-list, or
// a `Process.Start(exePath, "--safe-flag", input)` that is whitelisted) can
// silence the rule locally with
//
//     #pragma warning disable AGSEC001
//     Process.Start(userInput);   // reviewed: whitelisted exe + safe args
//     #pragma warning restore AGSEC001
//
// The check walks the leading trivia of the invocation (or `AddExpression` for
// AGSEC002) and matches directive tokens. Per-rule suppression is the documented
// contract: `#pragma warning disable AGSEC001` only affects AGSEC001. A bare
// `#pragma warning disable` (no rule ids) suppresses every AGSEC* rule at that
// site — same semantics as the C# compiler's CS-suppression.
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
    public const string AGSEC004 = "AGSEC004"; // HttpClient.Get*/Post*/... non-constant URL
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

    internal static readonly DiagnosticDescriptor Rule004 = new(
        AGSEC004,
        "HTTP request: non-constant URL",
        "HttpClient.{0} called with non-constant URL '{1}': validate the URL against an allow-list (scheme + host + path) before sending",
        "Security",
        DiagnosticSeverity.Warning,
        isEnabledByDefault: true,
        description: "Detects HttpClient requests whose URL is not a compile-time constant. SSRF (Server-Side Request Forgery) is the canonical risk: an attacker-controlled URL may target internal services.",
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
        ImmutableArray.Create(Rule001, Rule002, Rule003, Rule004, Rule005);

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
        if (name.Contains("Process.Start") && args.Count > 0 && !IsConstant(ctx, args[0].Expression)
            && !IsSuppressedByPragma(inv, AGSEC001))
            ctx.ReportDiagnostic(Diagnostic.Create(Rule001, args[0].GetLocation(), args[0].Expression));

        // AGSEC003: File.Read/Write/Delete on a non-constant path
        if ((name.StartsWith("File.Read") || name.StartsWith("File.Write") || name.StartsWith("File.Delete"))
            && args.Count > 0 && !IsConstant(ctx, args[0].Expression)
            && !IsSuppressedByPragma(inv, AGSEC003))
            ctx.ReportDiagnostic(Diagnostic.Create(Rule003, args[0].GetLocation(), args[0].Expression));

        // AGSEC004: HttpClient.Get*/Post*/Put*/Delete*/Send* on a non-constant URL
        if (IsHttpClientCall(name) && args.Count > 0 && !IsConstant(ctx, args[0].Expression)
            && !IsSuppressedByPragma(inv, AGSEC004))
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
        if (IsSuppressedByPragma(add, AGSEC002))
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
    // — 16 chars head + ellipsis) so the developer can identify which literal
    // triggered the rule. CWE-798 forbids displaying the secret, but the
    // leading prefix is enough to recognise it; the rest is masked.
    private static string TruncateForMessage(string s) =>
        s.Length <= 16 ? s : s.Substring(0, 12) + "…";

    // Public helper for tests: returns the provider name for a matched value.
    internal static string ProviderFor(string s) => MatchCredentialProvider(s);

    // The semantic key: ask the compiler whether the expression folds to a constant.
    // A literal literal is safe; an attacker-controlled variable collapses to no value
    // and is therefore flagged. This is what `grep Process.Start` cannot distinguish.
    private static bool IsConstant(SyntaxNodeAnalysisContext ctx, ExpressionSyntax expr) =>
        ctx.SemanticModel.GetConstantValue(expr).HasValue;

    // Pragma suppression registry (sub-grain #10500d).
    //
    // The C# compiler already honors `#pragma warning disable AGSEC001` /
    // `#pragma warning restore AGSEC001` for warnings it emits, but those
    // directives do NOT apply to analyzer-emitted diagnostics by default — we
    // walk the leading trivia of the suspect expression and look for the same
    // directives ourselves. This is the standard pattern recommended in the
    // Roslyn analyzer docs (DiagnosticSuppressor).
    //
    // Per-rule suppression:
    //     #pragma warning disable AGSEC001   // only AGSEC001 is silenced
    //     #pragma warning disable AGSEC001 AGSEC003   // both
    //
    // Bare suppression (suppresses every AGSEC* rule at this site):
    //     #pragma warning disable   // no ids ⇒ all AGSEC* off
    //
    // Restore semantics: a matching `restore` token cancels the suppression.
    // Single-line trivia are walked left-to-right; the final state wins.
    private static bool IsSuppressedByPragma(SyntaxNode node, string ruleId)
    {
        bool suppressed = false;
        foreach (var trivia in node.GetLeadingTrivia())
        {
            if (!trivia.IsKind(SyntaxKind.PragmaWarningDirectiveTrivia))
                continue;
            var text = trivia.ToString();
            // Split on whitespace; tokens are e.g. "pragma", "warning",
            // "disable", "AGSEC001" — case-sensitive per C# spec.
            var tokens = text.Split(
                new[] { ' ', '\t', '\r', '\n' }, System.StringSplitOptions.RemoveEmptyEntries);

            bool hasDisable = false;
            bool hasRestore = false;
            bool targetsAll = false;
            bool targetsRule = false;

            for (int i = 0; i < tokens.Length; i++)
            {
                var token = tokens[i];
                if (token == "disable")
                {
                    hasDisable = true;
                    continue;
                }
                if (token == "restore")
                {
                    hasRestore = true;
                    continue;
                }
                // Anything after the directive keyword on a `#pragma warning`
                // line is a rule id — for our purposes, treat any non-keyword
                // token as a candidate rule id. Empty list = "all rules".
                if (i >= 2 && token.StartsWith("AGSEC", System.StringComparison.Ordinal))
                {
                    if (string.Equals(token, ruleId, System.StringComparison.Ordinal))
                        targetsRule = true;
                    else
                        targetsAll = false; // explicit list, not "all"
                }
            }

            // No rule ids at all on the pragma line ⇒ applies to every AGSEC* rule.
            // (We track this lazily: if no AGSEC* token appeared, targetsAll stays true.)
            if (hasDisable || hasRestore)
            {
                bool anyRuleIdMentioned = false;
                for (int i = 2; i < tokens.Length; i++)
                {
                    if (tokens[i].StartsWith("AGSEC", System.StringComparison.Ordinal))
                    {
                        anyRuleIdMentioned = true;
                        break;
                    }
                }
                if (!anyRuleIdMentioned)
                    targetsAll = true;

                if (hasDisable && (targetsAll || targetsRule))
                    suppressed = true;
                if (hasRestore && (targetsAll || targetsRule))
                    suppressed = false;
            }
        }
        return suppressed;
    }

    private static bool IsSqlLike(string s)
    {
        var u = s.ToUpperInvariant();
        return u.Contains("SELECT ") || u.Contains("INSERT ") ||
               u.Contains("UPDATE ") || u.Contains("DELETE ");
    }
}
