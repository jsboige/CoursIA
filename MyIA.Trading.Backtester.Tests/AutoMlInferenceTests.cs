using System;
using System.IO;
using Microsoft.ML;
using Microsoft.ML.AutoML;
using Xunit;

namespace MyIA.Trading.Backtester.Tests
{
    /// <summary>
    /// Replique du mini-test d'integration du cadrage E2 (docs/reference/backtester-e2-cadrage.md, 2.2) :
    /// l'usage AutoML reel du port (InferColumns) + entrainement lineaire (SdcaMaximumEntropy)
    /// sur un CSV inline separable, assert MicroAccuracy > 0.9.
    ///
    /// Ce test fige la paire preview Microsoft.ML.AutoML 0.24.0-preview.26160.2 +
    /// Microsoft.ML 6.0.0-preview.26160.2 : la substitution du fork (AutoML 0.20.1, 2022) n'est
    /// pas un re-packaging — l'API 0.20.x ColumnInferenceResults.TextLoaderEventArgs a disparu
    /// en 0.24, remplacee par TextLoaderOptions (CS1061 mesure au compilateur au geste 2).
    /// </summary>
    public sealed class AutoMlInferenceTests : IDisposable
    {
        private readonly string _csvPath = Path.Combine(Path.GetTempPath(), $"backtester-s22-{Guid.NewGuid():N}.csv");

        [Fact]
        public void InferColumns_And_TrainSdcaMaximumEntropy_ReachesMicroAccuracyAbove09()
        {
            var mlContext = new MLContext(seed: 0);
            File.WriteAllText(_csvPath, BuildSeparableThreeClassCsv());

            // API 0.24-preview, verifiee par reflexion runtime + sonde empirique :
            // - ColumnInferenceApi (extension MLContext, 9 args avec hasHeader) est internal -> inutilisable.
            // - AutoCatalog.InferColumns(path, labelColumnName, separatorChar) DETECTE le header
            //   automatiquement (parametre hasHeader supprime de la signature 0.20.x) : sur un CSV
            //   "Label,F1,F2" avec header, l'inference rend Label + Features(F1,F2) groupes.
            var inference = mlContext.Auto().InferColumns(
                _csvPath,
                labelColumnName: "Label",
                separatorChar: ',');
            Assert.NotNull(inference.TextLoaderOptions);

            var textLoader = mlContext.Data.CreateTextLoader(inference.TextLoaderOptions);
            var dataView = textLoader.Load(_csvPath);
            var split = mlContext.Data.TrainTestSplit(dataView, testFraction: 0.25, seed: 0);

            var pipeline = mlContext.Transforms.Conversion.MapValueToKey("Label")
                .Append(mlContext.MulticlassClassification.Trainers.SdcaMaximumEntropy())
                .Append(mlContext.Transforms.Conversion.MapKeyToValue("PredictedLabel"));
            var model = pipeline.Fit(split.TrainSet);

            var predictions = model.Transform(split.TestSet);
            var metrics = mlContext.MulticlassClassification.Evaluate(predictions);

            Assert.True(metrics.MicroAccuracy > 0.9,
                $"MicroAccuracy={metrics.MicroAccuracy:0.000} attendu > 0.9 (donnees separables lineairement)");
        }

        private static string BuildSeparableThreeClassCsv()
        {
            var lines = new System.Collections.Generic.List<string> { "Label,F1,F2" };
            for (int i = 0; i < 8; i++)
            {
                lines.Add($"0,0.{i % 10}1,0.{(i * 3) % 10}2");
                lines.Add($"1,5.{i % 10}1,5.{(i * 3) % 10}2");
                lines.Add($"2,10.{i % 10}1,10.{(i * 3) % 10}2");
            }
            return string.Join(Environment.NewLine, lines);
        }

        public void Dispose()
        {
            if (File.Exists(_csvPath))
            {
                File.Delete(_csvPath);
            }
        }
    }
}
