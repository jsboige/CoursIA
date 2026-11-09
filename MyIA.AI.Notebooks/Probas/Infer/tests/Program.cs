// FactorGraphHelper.Selection.Tests — harness de selection des graphes de
// facteurs Infer.NET (portee par carnet + refus du .svg etranger, remede #25293,
// defaut #25276). Console Exe : le processus rend 0 si toutes les asserts
// Require(...) passent, 1 sinon. Versionne pour que la sortie CI soit rattachable
// a une iteration donnee du harness.
//
// Cas ports de #25293 (credit Git : Jean-Sylvain Boige) + cas d'isolation de
// segment (le filtre historique Contains(scope) sur le chemin entier n'isolait
// pas une portee exacte).

static void Require(bool condition, string message)
{
    if (!condition)
    {
        throw new InvalidOperationException(message);
    }
}

Console.WriteLine("[FactorGraphHelper.Selection.Tests v1.0.0]");

var originalDirectory = Environment.CurrentDirectory;
var testDirectory = Path.Combine(Path.GetTempPath(), "factor-graph-selection-" + Guid.NewGuid().ToString("N"));
Directory.CreateDirectory(testDirectory);

try
{
    Environment.CurrentDirectory = testDirectory;
    var sourceDirectory = Path.Combine(testDirectory, "GeneratedSource");
    Directory.CreateDirectory(sourceDirectory);

    var modelA = Path.Combine(testDirectory, "Model_A.gv");
    var modelB = Path.Combine(sourceDirectory, "Model_B.gv");

    // Simule deux noyaux entrelaces qui produisent des modeles dans les deux
    // emplacements scrutes, avec un ordre de timestamps volontairement trompeur.
    await Task.WhenAll(
        Task.Run(() => File.WriteAllText(modelA, "digraph { carnet_a [label=\"CarnetA\"] }")),
        Task.Run(() => File.WriteAllText(modelB, "digraph { carnet_b [label=\"CarnetB\"] }")));
    File.SetLastWriteTimeUtc(modelA, DateTime.UtcNow.AddMinutes(-2));
    File.SetLastWriteTimeUtc(modelB, DateTime.UtcNow.AddMinutes(-1));

    var ambiguous = FactorGraphHelper.ConvertAndGetLatestGvHtml();
    Require(ambiguous.Contains("ambigu", StringComparison.OrdinalIgnoreCase), "Deux fichiers .gv doivent refuser un choix implicite.");
    Require(ambiguous.Contains(modelA, StringComparison.Ordinal), "Le diagnostic doit nommer le premier graphe.");
    Require(ambiguous.Contains(modelB, StringComparison.Ordinal), "Le diagnostic doit nommer le second graphe.");

    var selectedA = FactorGraphHelper.ConvertAndGetGvHtml(modelA);
    var selectedB = FactorGraphHelper.ConvertAndGetGvHtml(modelB);
    if (FactorGraphHelper.IsGraphvizAvailable())
    {
        Require(selectedA.Contains("CarnetA", StringComparison.Ordinal), "La sélection explicite doit rendre le graphe A.");
        Require(!selectedA.Contains("CarnetB", StringComparison.Ordinal), "Le graphe A ne doit pas contenir le modèle B.");
        Require(selectedB.Contains("CarnetB", StringComparison.Ordinal), "La sélection explicite doit rendre le graphe B.");
        Require(!selectedB.Contains("CarnetA", StringComparison.Ordinal), "Le graphe B ne doit pas contenir le modèle A.");
    }

    File.Delete(modelA);
    File.Delete(modelB);
    File.Delete(Path.ChangeExtension(modelA, ".svg"));
    File.Delete(Path.ChangeExtension(modelB, ".svg"));
    var sameFolderA = Path.Combine(testDirectory, "Model_SameA.svg");
    var sameFolderB = Path.Combine(testDirectory, "Model_SameB.svg");
    File.WriteAllText(sameFolderA, "<svg><text>SameA</text></svg>");
    File.WriteAllText(sameFolderB, "<svg><text>SameB</text></svg>");
    var svgAmbiguous = FactorGraphHelper.GetLatestFactorGraphHtml();
    Require(svgAmbiguous.Contains("ambigu", StringComparison.OrdinalIgnoreCase), "Deux SVG dans le meme dossier doivent aussi etre signales comme ambigus.");

    File.Delete(sameFolderB);
    File.SetLastWriteTimeUtc(sameFolderA, DateTime.UtcNow.AddYears(-1));
    var singleSvg = FactorGraphHelper.GetLatestFactorGraphHtml();
    Require(singleSvg.Contains("SameA", StringComparison.Ordinal), "Un unique SVG doit rester affichable quel que soit son timestamp.");

    var originalPath = Environment.GetEnvironmentVariable("PATH");
    var graphvizCacheField = typeof(FactorGraphHelper).GetField(
        "_graphvizAvailable",
        System.Reflection.BindingFlags.NonPublic | System.Reflection.BindingFlags.Static)
        ?? throw new InvalidOperationException("Le cache Graphviz attendu est introuvable.");
    var previousGraphvizCache = graphvizCacheField.GetValue(null);
    try
    {
        var emptyPath = Path.Combine(testDirectory, "empty-path");
        Directory.CreateDirectory(emptyPath);
        Environment.SetEnvironmentVariable("PATH", emptyPath);
        graphvizCacheField.SetValue(null, false);

        var sourceModel = Path.Combine(testDirectory, "Model_Source.gv");
        var foreignSvg = Path.Combine(testDirectory, "Model_Foreign.svg");
        File.WriteAllText(sourceModel, "digraph { source [label=\"SourceModel\"] }");
        File.WriteAllText(foreignSvg, "<svg><text>ForeignModel</text></svg>");

        var mismatched = FactorGraphHelper.GetLatestFactorGraphHtml();
        Require(mismatched.Contains("aucun SVG ne correspond", StringComparison.OrdinalIgnoreCase), "Sans Graphviz, un SVG d'un autre modele doit etre refuse.");
        Require(mismatched.Contains(sourceModel, StringComparison.Ordinal), "Le diagnostic doit nommer le .gv sans cache correspondant.");
        Require(mismatched.Contains(foreignSvg, StringComparison.Ordinal), "Le diagnostic doit nommer le SVG sans correspondance.");
        Require(!mismatched.Contains("ForeignModel", StringComparison.Ordinal), "Le contenu d'un SVG sans correspondance ne doit pas etre affiche.");

        File.Delete(foreignSvg);
        var matchingSvg = Path.ChangeExtension(sourceModel, ".svg");
        File.WriteAllText(matchingSvg, "<svg><text>MatchingSourceModel</text></svg>");
        var matched = FactorGraphHelper.GetLatestFactorGraphHtml();
        Require(matched.Contains("MatchingSourceModel", StringComparison.Ordinal), "Sans Graphviz, le cache SVG au chemin correspondant doit rester utilisable.");

        File.Delete(sourceModel);
        File.Delete(matchingSvg);
        var legacySvg = FactorGraphHelper.GetLatestFactorGraphHtml();
        Require(legacySvg.Contains("SameA", StringComparison.Ordinal), "Sans source .gv, un SVG unique conserve le fallback legacy.");
    }
    finally
    {
        Environment.SetEnvironmentVariable("PATH", originalPath);
        graphvizCacheField.SetValue(null, previousGraphvizCache);
    }

    // Isolation de segment (defaut Contains(scope) sur le chemin entier,
    // #25293/#25276) : la portee "A" ne doit matcher que le segment exact "A",
    // ni "AA", ni un segment qui CONTIENT "A".
    var segA = Path.Combine(testDirectory, "GeneratedSource", "A", "Model_a.gv");
    var segAA = Path.Combine(testDirectory, "GeneratedSource", "AA", "Model_aa.gv");
    var segParentA = Path.Combine(testDirectory, "GeneratedSource", "parentAchild", "Model_p.gv");
    var segCandidates = new[] { segA, segAA, segParentA };
    var hitA = FactorGraphHelper.SelectFactorGraphFile(segCandidates, "A", out int hitCountA);
    Require(hitCountA == 1 && string.Equals(hitA, segA, StringComparison.OrdinalIgnoreCase),
        "La portee \"A\" doit isoler le segment exact \"A\" (ni \"AA\", ni \"parentAchild\").");
    var hitAA = FactorGraphHelper.SelectFactorGraphFile(segCandidates, "AA", out _);
    Require(string.Equals(hitAA, segAA, StringComparison.OrdinalIgnoreCase),
        "La portee \"AA\" doit isoler le segment exact \"AA\" (pas \"A\").");
    var hitParent = FactorGraphHelper.SelectFactorGraphFile(segCandidates, "parentAchild", out _);
    Require(string.Equals(hitParent, segParentA, StringComparison.OrdinalIgnoreCase),
        "La portee \"parentAchild\" doit isoler ce segment, pas ses soeurs.");

    Console.WriteLine("FactorGraphHelper selection checks passed.");
}
finally
{
    Environment.CurrentDirectory = originalDirectory;
    Directory.Delete(testDirectory, recursive: true);
}
