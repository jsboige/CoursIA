static void Require(bool condition, string message)
{
    if (!condition)
    {
        throw new InvalidOperationException(message);
    }
}

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

    Console.WriteLine("FactorGraphHelper selection checks passed.");
}
finally
{
    Environment.CurrentDirectory = originalDirectory;
    Directory.Delete(testDirectory, recursive: true);
}
