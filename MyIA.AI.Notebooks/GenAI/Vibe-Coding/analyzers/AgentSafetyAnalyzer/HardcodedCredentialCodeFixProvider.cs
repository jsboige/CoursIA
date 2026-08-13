// HardcodedCredentialCodeFixProvider.cs — CodeFixProvider companion to
// AgentSafetyAnalyzer's AGSEC005 rule (sub-grain #10500f of Epic #10473).
//
// Transforms a literal string whose value starts with a known credential
// prefix (sk-/ghp_/AKIA/AIza/hf_/etc.) into a call to
// `Environment.GetEnvironmentVariable("PROVIDER_API_KEY") ?? ""`, where
// PROVIDER_API_KEY is a conventional env-var name picked from the matched
// prefix. The transformation is applied at the **declaration site** —
// we walk up from the literal to the enclosing LocalDeclarationStatement /
// FieldDeclaration / PropertyDeclaration and replace the literal in place.
//
// Example — before:
//     const string openaiKey = "sk-proj-AbCdEf1234567890abcdef";
// After (lightbulb fix):
//     const string openaiKey = Environment.GetEnvironmentVariable("OPENAI_API_KEY") ?? "";
//
// The `?? ""` keeps the variable's effective type unchanged (still a `string`,
// never null), so downstream code that reads the value is unaffected. The
// env var name is a *suggestion*, not a contract — the developer is expected
// to set the env var to the actual key in their environment (or to pick a
// different env var name if their CI convention differs).
//
// Triggered by the lightbulb in IDEs after AGSEC005 fires; applied through
// `dotnet format` analyzers or IDE quick-fix UI.

using System.Collections.Generic;
using System.Collections.Immutable;
using System.Composition;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CodeActions;
using Microsoft.CodeAnalysis.CodeFixes;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace MyIA.AgentSafety;

[ExportCodeFixProvider(LanguageNames.CSharp, Name = nameof(HardcodedCredentialCodeFixProvider))]
[Shared]
public sealed class HardcodedCredentialCodeFixProvider : CodeFixProvider
{
    public override ImmutableArray<string> FixableDiagnosticIds =>
        ImmutableArray.Create(AgentSafetyAnalyzer.AGSEC005);

    public override FixAllProvider GetFixAllProvider() => WellKnownFixAllProviders.BatchFixer;

    public override async Task RegisterCodeFixesAsync(CodeFixContext context)
    {
        var root = await context.Document.GetSyntaxRootAsync(context.CancellationToken).ConfigureAwait(false);
        if (root is null) return;

        var diagnostic = context.Diagnostics.First();
        var span = diagnostic.Location.SourceSpan;
        var node = root.FindNode(span, getInnermostNodeForTie: true) as LiteralExpressionSyntax;
        if (node is null || !node.IsKind(SyntaxKind.StringLiteralExpression)) return;

        // Identify the credential prefix so we can pick a sensible env var name.
        var value = node.Token.ValueText;
        var envVarName = MapPrefixToEnvVar(value);
        if (envVarName is null) return;

        var title = $"Replace hardcoded credential with Environment.GetEnvironmentVariable(\"{envVarName}\")";
        context.RegisterCodeFix(
            CodeAction.Create(
                title: title,
                createChangedDocument: ct => ToEnvVarLookupAsync(context.Document, node, envVarName, ct),
                equivalenceKey: $"AGSEC005_EnvVar_{envVarName}"),
            diagnostic);
    }

    // Replaces the literal with `Environment.GetEnvironmentVariable("ENV_VAR") ?? ""`.
    // The `?? ""` keeps the variable's effective type `string` (never null), so
    // downstream code that consumes the variable is unaffected. The call is wrapped
    // in `System.Environment` to avoid pulling `using System;` into the developer's
    // file — analyzers are not supposed to silently add `using` directives.
    private static async Task<Document> ToEnvVarLookupAsync(
        Document doc,
        LiteralExpressionSyntax literal,
        string envVarName,
        CancellationToken ct)
    {
        var root = await doc.GetSyntaxRootAsync(ct).ConfigureAwait(false);
        if (root is null) return doc;

        var replacementText = $"System.Environment.GetEnvironmentVariable(\"{envVarName}\") ?? \"\"";
        var fixedExpr = SyntaxFactory.ParseExpression(replacementText).WithTriviaFrom(literal);
        var newRoot = root.ReplaceNode(literal, fixedExpr);
        return doc.WithSyntaxRoot(newRoot);
    }

    // Maps a credential prefix to a conventional env var name. The mapping mirrors
    // the prefix table in AgentSafetyAnalyzer.cs; it's repeated here (rather than
    // shared via an internal helper) to keep the CodeFixProvider's public surface
    // self-contained — analyzers and code-fix providers are loaded independently
    // by the Roslyn host and may not share internals across assemblies.
    //
    // For prefixes that don't have a single canonical env-var name (e.g. the
    // `dapi` / `ddp_` family which spans multiple vendors), the mapping falls
    // back to a generic name. The developer can rename the env var locally.
    private static string? MapPrefixToEnvVar(string s)
    {
        foreach (var (prefix, envVar) in PrefixEnvVarMap)
        {
            if (s.StartsWith(prefix, System.StringComparison.Ordinal))
                return envVar;
        }
        return null;
    }

    // Order matters: most-specific-first, same as CredentialPrefixes in the
    // analyzer. A `sk-ant-` literal must resolve to `ANTHROPIC_API_KEY`,
    // not the more generic `OPENAI_API_KEY`.
    private static readonly (string Prefix, string EnvVar)[] PrefixEnvVarMap = new[]
    {
        ("sk-ant-",  "ANTHROPIC_API_KEY"),
        ("sk-",      "OPENAI_API_KEY"),
        ("ghp_",     "GITHUB_TOKEN"),
        ("gho_",     "GITHUB_OAUTH_TOKEN"),
        ("ghs_",     "GITHUB_SERVER_TOKEN"),
        ("ghr_",     "GITHUB_REFRESH_TOKEN"),
        ("glpat-",   "GITLAB_TOKEN"),
        ("xoxb-",    "SLACK_BOT_TOKEN"),
        ("xoxp-",    "SLACK_USER_TOKEN"),
        ("xoxa-",    "SLACK_APP_TOKEN"),
        ("AIza",     "GOOGLE_API_KEY"),
        ("AKIA",     "AWS_ACCESS_KEY_ID"),
        ("ASIA",     "AWS_STS_ACCESS_KEY_ID"),
        ("hf_",      "HUGGINGFACE_TOKEN"),
        ("pplx-",    "PERPLEXITY_API_KEY"),
        ("dapi",     "DATABRICKS_TOKEN"),
        ("ddp_",     "DATADOG_API_KEY"),
    };
}
