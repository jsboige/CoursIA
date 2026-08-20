// Canal API : compiler un source via Roslyn et rendre le verdict de
// l'analyseur SANS passer par MSBuild. C'est le canal qu'utilisent l'IDE
// (soulignement jaune) et un test unitaire ; le projet Demo montre le canal
// build (dotnet build rend le meme diagnostic). Deux canaux, un moteur.
//
// usage: dotnet run --project AgentGuard.Verifier -- <fautif.cs> <corrige.cs>

using AgentGuard.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.Diagnostics;

if (args.Length != 2)
{
    Console.WriteLine("usage: dotnet run -- <fautif.cs> <corrige.cs>");
    return 2;
}

// References pour compiler les sources sous test : les assemblies de
// reference du ref pack SDK (packs/Microsoft.NETCore.App.Ref/*/ref/...),
// faites exactement pour ca -- 100 % managed. (Le dossier "shared" du
// runtime, lui, melange DLL natives : clrjit, msquic... qui ne portent
// pas de metadonnees gerables ; et pointer CoreLib seul ne suffit pas,
// le compilateur exige les facades System.Runtime/System.Threading.Tasks
// -- mesure firsthand : sans elles, Task ne resout pas et l'analyseur
// n'a rien a trancher.)
var frameworkDir = Path.GetDirectoryName(typeof(object).Assembly.Location)!;
var dotnetRoot = Path.GetFullPath(Path.Combine(frameworkDir, "..", "..", ".."));
// Meme version que le runtime qui execute ce Verifier (le nom du dossier
// shared = numero de version). Un tri lexicographique des versions serait
// faux : "9.0.19" > "10.0.11" en chaine.
var fxVersion = new DirectoryInfo(frameworkDir).Name;
var refDir = Path.Combine(
    dotnetRoot, "packs", "Microsoft.NETCore.App.Ref", fxVersion, "ref");
var refs = Directory.GetFiles(refDir, "*.dll", SearchOption.AllDirectories)
    .Select(p => (MetadataReference)MetadataReference.CreateFromFile(p))
    .ToArray();

foreach (var path in args)
{
    var tree = CSharpSyntaxTree.ParseText(
        File.ReadAllText(path),
        new CSharpParseOptions(LanguageVersion.Latest),
        path: Path.GetFileName(path));

    // Un fichier a top-level statements exige un point d'entree (exe) ;
    // un fichier de classes seules n'en a pas (DLL). On adapte.
    var hasTopLevel = tree.GetCompilationUnitRoot()
        .Members.OfType<Microsoft.CodeAnalysis.CSharp.Syntax.GlobalStatementSyntax>().Any();
    var compilation = CSharpCompilation.Create(
        assemblyName: "under-test",
        syntaxTrees: [tree],
        references: refs,
        options: new CSharpCompilationOptions(
            hasTopLevel ? OutputKind.ConsoleApplication : OutputKind.DynamicallyLinkedLibrary));

    var withAnalyzers = compilation.WithAnalyzers(
        [new TaskResultBlockAnalyzer()]);

    // Les erreurs de compilation empechent le modele semantique de resoudre
    // les symboles (donc l'analyseur de trancher) : on les rend visibles.
    foreach (var e in compilation.GetDiagnostics().Where(d => d.Severity == DiagnosticSeverity.Error))
        Console.WriteLine($"    (erreur de compilation sous-jacente : {e.GetMessage()})");

    var diagnostics = (await withAnalyzers.GetAllDiagnosticsAsync())
        .Where(d => d.Id == TaskResultBlockAnalyzer.DiagnosticId)
        .OrderBy(d => d.Location.SourceSpan.Start)
        .ToList();

    var label = Path.GetFileName(path);
    if (diagnostics.Count == 0)
    {
        Console.WriteLine($"[{label}] VERDICT : PROPRE -- aucun blocage synchrone detecte");
    }
    else
    {
        Console.WriteLine($"[{label}] VERDICT : {diagnostics.Count} diagnostic(s) {TaskResultBlockAnalyzer.DiagnosticId}");
        foreach (var d in diagnostics)
        {
            var line = d.Location.GetLineSpan();
            Console.WriteLine($"    {d.Id} @ {line.StartLinePosition.Line + 1}:{line.StartLinePosition.Character + 1}  {d.GetMessage()}");
        }
    }
}
return 0;
