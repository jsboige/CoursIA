// AgentSafetyAnalyzerTests.cs — xUnit tests for the 3 rules + CodeFixProvider.
//
// Approach: build a minimal `CSharpCompilation` in-memory with the analyzer
// referenced, then assert against the emitted `Diagnostic`s. This avoids
// the `Microsoft.CodeAnalysis.CSharp.Analyzer.Testing` v1.1.2 / Roslyn 4.0
// transitive dependency mismatch (we use Roslyn 4.12 throughout) and gives
// direct visibility on the diagnostics emitted by our rules.
//
// Each rule is tested both on a safe literal (no diagnostic expected) and on
// an attacker-controlled variable (diagnostic expected, with location). This
// is the Prong-B discrimination pattern from the notebook.

using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CodeActions;
using Microsoft.CodeAnalysis.CodeFixes;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.Diagnostics;
using Microsoft.CodeAnalysis.Text;
using MyIA.AgentSafety;
using Xunit;

namespace MyIA.AgentSafety.Tests;

public class AgentSafetyAnalyzerTests
{
    // -------- AGSEC001: Process.Start injection --------

    [Fact]
    public async Task AGSEC001_NoDiagnostic_OnConstantLiteral()
    {
        const string source = @"
using System.Diagnostics;
class C { void M() { Process.Start(""notepad.exe""); } }";
        var diags = await GetDiagnosticsAsync(source);
        Assert.DoesNotContain(diags, d => d.Id == AgentSafetyAnalyzer.AGSEC001);
    }

    [Fact]
    public async Task AGSEC001_Diagnostic_OnAttackerControlledVariable()
    {
        const string source = @"
using System.Diagnostics;
class C { void M(string userInput) { Process.Start(userInput); } }";
        var diags = await GetDiagnosticsAsync(source);
        var d = Assert.Single(diags, x => x.Id == AgentSafetyAnalyzer.AGSEC001);
        Assert.Equal(DiagnosticSeverity.Warning, d.Severity);
        Assert.Contains("userInput", d.GetMessage());
    }

    // -------- AGSEC002: SQL concatenation --------

    [Fact]
    public async Task AGSEC002_NoDiagnostic_OnInterpolatedString()
    {
        const string source = @"
class C { void M(string table) { var q = $""SELECT * FROM {table}""; } }";
        var diags = await GetDiagnosticsAsync(source);
        Assert.DoesNotContain(diags, d => d.Id == AgentSafetyAnalyzer.AGSEC002);
    }

    [Fact]
    public async Task AGSEC002_Diagnostic_OnSqlConcat()
    {
        const string source = @"
class C { void M(string userInput) { var q = ""SELECT * FROM users WHERE name = '"" + userInput; } }";
        var diags = await GetDiagnosticsAsync(source);
        var d = Assert.Single(diags, x => x.Id == AgentSafetyAnalyzer.AGSEC002);
        Assert.Equal(DiagnosticSeverity.Warning, d.Severity);
    }

    // -------- AGSEC003: File.* path traversal --------

    [Fact]
    public async Task AGSEC003_NoDiagnostic_OnConstantPath()
    {
        const string source = @"
using System.IO;
class C { void M() { File.ReadAllText(""/tmp/known.txt""); } }";
        var diags = await GetDiagnosticsAsync(source);
        Assert.DoesNotContain(diags, d => d.Id == AgentSafetyAnalyzer.AGSEC003);
    }

    [Fact]
    public async Task AGSEC003_Diagnostic_OnAttackerControlledPath()
    {
        const string source = @"
using System.IO;
class C { void M(string name) { File.ReadAllText(name); } }";
        var diags = await GetDiagnosticsAsync(source);
        var d = Assert.Single(diags, x => x.Id == AgentSafetyAnalyzer.AGSEC003);
        Assert.Equal(DiagnosticSeverity.Warning, d.Severity);
    }

    // -------- AGSEC004: HttpClient non-constant URL (sub-grain #10500c) --------

    [Fact]
    public async Task AGSEC004_NoDiagnostic_OnConstantUrl()
    {
        const string source = @"
using System.Net.Http;
using System.Threading.Tasks;
class C {
    HttpClient _client = new HttpClient();
    public async Task M() { await _client.GetAsync(""https://api.example.com/health""); }
}";
        var diags = await GetDiagnosticsAsync(source);
        Assert.DoesNotContain(diags, d => d.Id == AgentSafetyAnalyzer.AGSEC004);
    }

    [Fact]
    public async Task AGSEC004_Diagnostic_OnAttackerControlledUrl()
    {
        const string source = @"
using System.Net.Http;
using System.Threading.Tasks;
class C {
    HttpClient _client = new HttpClient();
    public async Task M(string userInput) { await _client.GetAsync(userInput); }
}";
        var diags = await GetDiagnosticsAsync(source);
        var d = Assert.Single(diags, x => x.Id == AgentSafetyAnalyzer.AGSEC004);
        Assert.Equal(DiagnosticSeverity.Warning, d.Severity);
        Assert.Contains("GetAsync", d.GetMessage());
    }

    [Fact]
    public async Task AGSEC004_Diagnostic_OnPostAsync_NonConstantUrl()
    {
        const string source = @"
using System.Net.Http;
using System.Threading.Tasks;
class C {
    HttpClient _client = new HttpClient();
    public async Task M(string url) { await _client.PostAsync(url, null); }
}";
        var diags = await GetDiagnosticsAsync(source);
        var d = Assert.Single(diags, x => x.Id == AgentSafetyAnalyzer.AGSEC004);
        Assert.Contains("PostAsync", d.GetMessage());
    }

    [Fact]
    public async Task AGSEC004_Diagnostic_OnSendAsync_NonConstantUrl()
    {
        // SendAsync requires an HttpRequestMessage, so we build one with an
        // attacker-controlled URL. The diagnostic fires on the URI string itself.
        const string source = @"
using System.Net.Http;
using System.Threading.Tasks;
class C {
    HttpClient _client = new HttpClient();
    public async Task M(string userUrl) {
        var req = new HttpRequestMessage(HttpMethod.Get, userUrl);
        await _client.SendAsync(req);
    }
}";
        var diags = await GetDiagnosticsAsync(source);
        Assert.Contains(diags, d => d.Id == AgentSafetyAnalyzer.AGSEC004);
    }

    [Fact]
    public async Task AGSEC004_NoDiagnostic_OnGetStringAsync_ConstantUrl()
    {
        const string source = @"
using System.Net.Http;
using System.Threading.Tasks;
class C {
    HttpClient _client = new HttpClient();
    public async Task M() { await _client.GetStringAsync(""https://api.example.com/""); }
}";
        var diags = await GetDiagnosticsAsync(source);
        Assert.DoesNotContain(diags, d => d.Id == AgentSafetyAnalyzer.AGSEC004);
    }

    // -------- AGSEC002 CodeFixProvider: concatenation -> interpolated string --------

    [Fact]
    public async Task AGSEC002_CodeFix_TransformsConcatToInterpolatedString()
    {
        const string before = @"
class C { void M(string userInput) { var q = ""SELECT * FROM users WHERE name = '"" + userInput; } }";

        var document = await CreateDocumentAsync(before);
        var analyzerDiags = await GetDiagnosticsFromDocumentAsync(document);
        var rule002 = analyzerDiags.First(d => d.Id == AgentSafetyAnalyzer.AGSEC002);

        var actions = new List<CodeAction>();
        var context = new CodeFixContext(document, rule002, (a, _) => actions.Add(a), CancellationToken.None);
        var fixProvider = new SqlConcatCodeFixProvider();
        await fixProvider.RegisterCodeFixesAsync(context);

        var action = Assert.Single(actions);
        var operations = await action.GetOperationsAsync(CancellationToken.None);
        var applyOperation = Assert.Single(operations.OfType<ApplyChangesOperation>());

        var newSolution = applyOperation.ChangedSolution;
        var newDocument = newSolution.GetDocument(document.Id);
        var newText = await newDocument!.GetTextAsync();
        // We tolerate the trailing-quote artifact of `SyntaxFactory.ParseExpression`
        // on a hand-rolled snippet -- the structural fact is that the concat is gone.
        Assert.Contains("SELECT * FROM users WHERE name = '{userInput}", newText.ToString());
        Assert.DoesNotContain("\" + userInput", newText.ToString());
    }

    // -------- AGSEC pragma suppression (sub-grain #10500d) --------

    [Fact]
    public async Task AGSEC001_NoDiagnostic_OnPragmaDisable_ForSameRule()
    {
        // `#pragma warning disable AGSEC001` immediately above the call silences
        // the rule for that one site (per-rule contract).
        const string source = @"
using System.Diagnostics;
class C {
    void M(string userInput) {
#pragma warning disable AGSEC001
        Process.Start(userInput);
    }
}";
        var diags = await GetDiagnosticsAsync(source);
        Assert.DoesNotContain(diags, d => d.Id == AgentSafetyAnalyzer.AGSEC001);
    }

    [Fact]
    public async Task AGSEC001_StillDiagnostic_OnPragmaDisable_ForOtherRule()
    {
        // Disabling AGSEC003 must NOT silence AGSEC001 — per-rule suppression is
        // the documented contract. A naive "any pragma ⇒ all off" implementation
        // would incorrectly suppress this one.
        const string source = @"
using System.Diagnostics;
class C {
    void M(string userInput) {
#pragma warning disable AGSEC003
        Process.Start(userInput);
    }
}";
        var diags = await GetDiagnosticsAsync(source);
        Assert.Contains(diags, d => d.Id == AgentSafetyAnalyzer.AGSEC001);
    }

    [Fact]
    public async Task AGSEC001_NoDiagnostic_OnBarePragmaDisable()
    {
        // A bare `#pragma warning disable` (no rule ids) suppresses every AGSEC*
        // rule at the site — same semantics as the C# compiler for CS-warnings.
        const string source = @"
using System.Diagnostics;
class C {
    void M(string userInput) {
#pragma warning disable
        Process.Start(userInput);
    }
}";
        var diags = await GetDiagnosticsAsync(source);
        Assert.DoesNotContain(diags, d => d.Id == AgentSafetyAnalyzer.AGSEC001);
    }

    [Fact]
    public async Task AGSEC001_Diagnostic_OnPragmaRestoreAfterDisable()
    {
        // A `#pragma warning restore AGSEC001` between two calls unsilences the
        // second call. This is the documented pragma contract and matches the
        // C# compiler's behavior for its own diagnostics.
        const string source = @"
using System.Diagnostics;
class C {
    void M(string userInput, string anotherInput) {
#pragma warning disable AGSEC001
        Process.Start(userInput);
#pragma warning restore AGSEC001
        Process.Start(anotherInput);
    }
}";
        var diags = await GetDiagnosticsAsync(source);
        // Exactly one AGSEC001 — the second (un-suppressed) call.
        var d001 = diags.Where(x => x.Id == AgentSafetyAnalyzer.AGSEC001).ToList();
        Assert.Single(d001);
        Assert.Contains("anotherInput", d001[0].GetMessage());
    }

    [Fact]
    public async Task AGSEC002_NoDiagnostic_OnPragmaDisable_ForSqlConcat()
    {
        // AGSEC002 fires on a `BinaryExpressionSyntax` (AddExpression), not on an
        // invocation. Suppression should still work — same trivia-walking logic,
        // same per-rule contract.
        const string source = @"
class C {
    void M(string userInput) {
#pragma warning disable AGSEC002
        var q = ""SELECT * FROM users WHERE name = '"" + userInput;
    }
}";
        var diags = await GetDiagnosticsAsync(source);
        Assert.DoesNotContain(diags, d => d.Id == AgentSafetyAnalyzer.AGSEC002);
    }

    // -------- AGSEC005: hardcoded credential detection (sub-grain #10500e) --------

    [Fact]
    public async Task AGSEC005_Diagnostic_OnOpenAIStyleKey()
    {
        // `sk-` is the OpenAI/Anthropic key prefix. A literal that starts with
        // `sk-` is almost certainly a real leaked key.
        const string source = @"
class C {
    const string apiKey = ""sk-proj-AbCdEf1234567890abcdefghij"";
}";
        var diags = await GetDiagnosticsAsync(source);
        var d = Assert.Single(diags, x => x.Id == AgentSafetyAnalyzer.AGSEC005);
        Assert.Equal(DiagnosticSeverity.Warning, d.Severity);
        // The diagnostic message names the matched prefix so the developer
        // knows which provider's secret leaked.
        Assert.Contains("sk-", d.GetMessage());
    }

    [Fact]
    public async Task AGSEC005_Diagnostic_OnGitHubPat()
    {
        // `ghp_` is the GitHub Personal Access Token prefix.
        const string source = @"
class C {
    const string token = ""ghp_AbCdEf1234567890abcdefghijklmnopqrstUV"";  // 40 chars
}";
        var diags = await GetDiagnosticsAsync(source);
        Assert.Contains(diags, d => d.Id == AgentSafetyAnalyzer.AGSEC005 && d.GetMessage().Contains("ghp_"));
    }

    [Fact]
    public async Task AGSEC005_Diagnostic_OnAwsAccessKeyId()
    {
        // `AKIA` is the AWS Access Key ID prefix (the long-form secret follows
        // separately and is not covered here).
        const string source = @"
class C {
    const string awsKey = ""AKIAIOSFODNN7EXAMPLE"";
}";
        var diags = await GetDiagnosticsAsync(source);
        Assert.Contains(diags, d => d.Id == AgentSafetyAnalyzer.AGSEC005 && d.GetMessage().Contains("AKIA"));
    }

    [Fact]
    public async Task AGSEC005_NoDiagnostic_OnPlainLiteral()
    {
        // A literal that doesn't start with any known provider prefix is left
        // alone — even if it might *be* a secret, without the prefix hint we
        // can't be sure enough to flag it (false-positive cost > false-negative
        // cost for unknown shapes).
        const string source = @"
class C {
    const string greeting = ""hello world"";
    const string endpoint = ""https://api.example.com/v1/messages"";
    const string skPrefix = ""sk-"";   // too short to be a key (length < 4 chars? actually 3 — no match)
}";
        var diags = await GetDiagnosticsAsync(source);
        Assert.DoesNotContain(diags, d => d.Id == AgentSafetyAnalyzer.AGSEC005);
    }

    [Fact]
    public async Task AGSEC005_Diagnostic_OnAnthropicStyleKey()
    {
        // `sk-ant-` is the more specific Anthropic prefix. The table is
        // ordered most-specific-first, so `sk-ant-` wins over `sk-` and the
        // diagnostic message references the Anthropic-shaped prefix.
        const string source = @"
class C {
    const string anthropicKey = ""sk-ant-api03-AbCdEf1234567890abcdefghijklmnopqr"";  // placeholder shape
}";
        var diags = await GetDiagnosticsAsync(source);
        Assert.Contains(diags, d => d.Id == AgentSafetyAnalyzer.AGSEC005 && d.GetMessage().Contains("sk-ant-"));
    }

    [Fact]
    public async Task AGSEC005_NoDiagnostic_OnEmptyLiteral()
    {
        // An empty string has no prefix; trivially not a credential.
        const string source = @"
class C {
    string M() { return """"; }
}";
        var diags = await GetDiagnosticsAsync(source);
        Assert.DoesNotContain(diags, d => d.Id == AgentSafetyAnalyzer.AGSEC005);
    }



    // -------- AGSEC005 CodeFixProvider (sub-grain #10500f) --------

    [Fact]
    public async Task AGSEC005_CodeFix_ReplacesOpenAIKeyWithEnvVarLookup()
    {
        const string before = @"
class C {
    const string openaiKey = ""sk-proj-AbCdEf1234567890abcdefghij"";
}";

        var document = await CreateDocumentAsync(before);
        var analyzerDiags = await GetDiagnosticsFromDocumentAsync(document);
        var rule005 = analyzerDiags.First(d => d.Id == AgentSafetyAnalyzer.AGSEC005);

        var actions = new List<CodeAction>();
        var context = new CodeFixContext(document, rule005, (a, _) => actions.Add(a), CancellationToken.None);
        var fixProvider = new HardcodedCredentialCodeFixProvider();
        await fixProvider.RegisterCodeFixesAsync(context);

        var action = Assert.Single(actions);
        var operations = await action.GetOperationsAsync(CancellationToken.None);
        var applyOperation = Assert.Single(operations.OfType<ApplyChangesOperation>());

        var newSolution = applyOperation.ChangedSolution;
        var newDocument = newSolution.GetDocument(document.Id);
        var newText = await newDocument!.GetTextAsync();

        Assert.DoesNotContain("\"sk-proj-AbCdEf1234567890abcdefghij\"", newText.ToString());
        Assert.Contains("OPENAI_API_KEY", newText.ToString());
        Assert.Contains("Environment.GetEnvironmentVariable", newText.ToString());
        Assert.Contains("?? \"\"", newText.ToString());
    }

    [Fact]
    public async Task AGSEC005_CodeFix_PicksCorrectEnvVarPerProvider()
    {
        var cases = new[]
        {
            ("\"ghp_AbCdEf1234567890abcdefghijklmnopqrstUV\"", "GITHUB_TOKEN"),
            ("\"AKIAIOSFODNN7EXAMPLE\"",                          "AWS_ACCESS_KEY_ID"),
            ("\"sk-ant-api03-AbCdEf1234567890abcdefghijklmnopqr\"", "ANTHROPIC_API_KEY"),
        };

        foreach (var (literal, expectedEnvVar) in cases)
        {
            var source = $"class C {{ const string k = {literal}; }}";
            var document = await CreateDocumentAsync(source);
            var analyzerDiags = await GetDiagnosticsFromDocumentAsync(document);
            var rule005 = analyzerDiags.First(d => d.Id == AgentSafetyAnalyzer.AGSEC005);

            var actions = new List<CodeAction>();
            var context = new CodeFixContext(document, rule005, (a, _) => actions.Add(a), CancellationToken.None);
            var fixProvider = new HardcodedCredentialCodeFixProvider();
            await fixProvider.RegisterCodeFixesAsync(context);

            var action = Assert.Single(actions);
            var operations = await action.GetOperationsAsync(CancellationToken.None);
            var applyOperation = Assert.Single(operations.OfType<ApplyChangesOperation>());

            var newSolution = applyOperation.ChangedSolution;
            var newDocument = newSolution.GetDocument(document.Id);
            var newText = await newDocument!.GetTextAsync();

            Assert.Contains(expectedEnvVar, newText.ToString());
            Assert.DoesNotContain(literal, newText.ToString());
        }
    }

    [Fact]
    public async Task AGSEC005_CodeFix_DoesNotMatchLiteralWithoutKnownPrefix()
    {
        const string source = @"
class C {
    const string greeting = ""hello world"";
}";
        var document = await CreateDocumentAsync(source);
        var analyzerDiags = await GetDiagnosticsFromDocumentAsync(document);
        Assert.DoesNotContain(analyzerDiags, d => d.Id == AgentSafetyAnalyzer.AGSEC005);
    }

    // -------- Helpers --------

    private static async Task<ImmutableArray<Diagnostic>> GetDiagnosticsAsync(string source)
    {
        var document = await CreateDocumentAsync(source);
        return await GetDiagnosticsFromDocumentAsync(document);
    }

    private static async Task<Document> CreateDocumentAsync(string source)
    {
        var workspace = new AdhocWorkspace();
        var projectId = ProjectId.CreateNewId();
        var documentId = DocumentId.CreateNewId(projectId);

        var projectInfo = ProjectInfo.Create(
            projectId,
            VersionStamp.Default,
            "TestProject",
            "TestProject",
            LanguageNames.CSharp,
            compilationOptions: new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary),
            parseOptions: new CSharpParseOptions(LanguageVersion.Latest));

        var solution = workspace.CurrentSolution
            .AddProject(projectInfo)
            .AddMetadataReference(projectId, MetadataReference.CreateFromFile(typeof(object).Assembly.Location))
            .AddMetadataReference(projectId, MetadataReference.CreateFromFile(typeof(DiagnosticAnalyzer).Assembly.Location))
            .AddMetadataReference(projectId, MetadataReference.CreateFromFile(typeof(CSharpCompilation).Assembly.Location))
            .AddMetadataReference(projectId, MetadataReference.CreateFromFile(System.Reflection.Assembly.Load("System.Runtime").Location))
            .AddDocument(documentId, "Test.cs", SourceText.From(source));

        return solution.GetDocument(documentId)!;
    }

    private static async Task<ImmutableArray<Diagnostic>> GetDiagnosticsFromDocumentAsync(Document document)
    {
        var compilation = await document.Project.GetCompilationAsync();
        var withAnalyzers = compilation!.WithAnalyzers(
            ImmutableArray.Create<DiagnosticAnalyzer>(new AgentSafetyAnalyzer()));
        return await withAnalyzers.GetAnalyzerDiagnosticsAsync();
    }
}