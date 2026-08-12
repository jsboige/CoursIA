// SqlConcatCodeFixProvider.cs — CodeFixProvider companion to AgentSafetyAnalyzer's
// AGSEC002 rule. Transforms ` "SELECT ..." + variable ` into a C# interpolated
// string `$"SELECT ... {variable}"` so the developer can then swap it for a
// parameterized SqlCommand/SqlParameter.
//
// Triggered by the lightbulb in IDEs after AGSEC002 fires; applied through
// `dotnet format` analyzers or `Roslynator`/IDE quick-fix UI.

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

[ExportCodeFixProvider(LanguageNames.CSharp, Name = nameof(SqlConcatCodeFixProvider))]
[Shared]
public sealed class SqlConcatCodeFixProvider : CodeFixProvider
{
    public override ImmutableArray<string> FixableDiagnosticIds =>
        ImmutableArray.Create(AgentSafetyAnalyzer.AGSEC002);

    public override FixAllProvider GetFixAllProvider() => WellKnownFixAllProviders.BatchFixer;

    public override async Task RegisterCodeFixesAsync(CodeFixContext context)
    {
        var root = await context.Document.GetSyntaxRootAsync(context.CancellationToken).ConfigureAwait(false);
        if (root is null) return;

        var diagnostic = context.Diagnostics.First();
        var span = diagnostic.Location.SourceSpan;
        var node = root.FindNode(span, getInnermostNodeForTie: true) as BinaryExpressionSyntax;
        if (node is null || node.Left is not LiteralExpressionSyntax) return;

        context.RegisterCodeFix(
            CodeAction.Create(
                title: "Convert SQL concatenation to interpolated string",
                createChangedDocument: ct => ToInterpolatedAsync(context.Document, node, ct),
                equivalenceKey: "AGSEC002_InterpolatedString"),
            diagnostic);
    }

    // "SELECT ... " + var   ->   $"SELECT ... {var}"
    private static async Task<Document> ToInterpolatedAsync(Document doc, BinaryExpressionSyntax add, CancellationToken ct)
    {
        var root = await doc.GetSyntaxRootAsync(ct).ConfigureAwait(false);
        if (root is null) return doc;

        var leftText = ((LiteralExpressionSyntax)add.Left).Token.ValueText;
        var rightText = add.Right.ToString();
        var replacement = $"$\"{leftText}{{{rightText}}}\"";
        var fixedExpr = SyntaxFactory.ParseExpression(replacement).WithTriviaFrom(add);
        var newRoot = root.ReplaceNode(add, fixedExpr);
        return doc.WithSyntaxRoot(newRoot);
    }
}
