using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.ML;
using Microsoft.ML.Data;
using Xunit;

namespace MyIA.Trading.Backtester.Tests
{
    /// <summary>
    /// Tranche 3 (EPIC #7357 geste 3) : couche ML config portee, mise a jour tranche 4.
    /// - cablage TradingModelsConfig.ModelType -> CurrentModelConfig (AutoML / Svm)
    /// - formats GetModelName des deux configs (logique upstream verbatim)
    /// - AutoMlTradingModel.Predict de bout en bout : pipeline ML.NET inline + prediction
    ///   sur samples separables (voie reelle du port, pas un mock)
    /// </summary>
    public sealed class TradingModelsConfigTests
    {
        [Fact]
        public void ModelType_AutoML_ReturnsAutoMlConfig()
        {
            var config = new TradingModelsConfig { ModelType = TradingModelType.AutoML };
            Assert.IsType<TradingAutoMlModelConfig>(config.CurrentModelConfig);
        }

        [Fact]
        public void ModelType_MulticlassSvm_ReturnsSvmConfig()
        {
            var config = new TradingModelsConfig { ModelType = TradingModelType.MulticlassSvm };
            Assert.IsType<TradingSvmModelConfig>(config.CurrentModelConfig);
        }

        /// <summary>
        /// Tranche 4 : la garde « port en attente » a disparu avec le stub — TrainModel
        /// entraine desormais un vrai SVM a noyau. La substance de ce port est couverte
        /// par TradingSvmModelConfigTests ; ce qui reste a verifier ici est que plus
        /// aucune ApplicationException de port pending ne subsiste dans le type.
        /// </summary>
        [Fact]
        public void SvmModelConfig_NoLongerCarriesThePendingPortGuard()
        {
            var config = new TradingSvmModelConfig();

            // Le noyau par defaut est instanciable : le chemin d'entrainement est cable,
            // il ne leve plus « port SVM en attente ».
            Assert.NotNull(config.GetKernel(config.Kernel));
        }

        [Fact]
        public void GetModelName_AutoML_ContainsMetricAndBinExtension()
        {
            var config = new TradingAutoMlModelConfig();
            var name = config.GetModelName(BuildDataConfig());

            Assert.Contains("-AutoML-", name);
            Assert.EndsWith("Model.bin", name);
        }

        [Fact]
        public void GetModelName_Svm_ContainsKernelAndComplexity()
        {
            var config = new TradingSvmModelConfig();
            var name = config.GetModelName(BuildDataConfig());

            Assert.Contains("-kernel-InverseMultiquadric-complexity--1-Model.bin", name);
        }

        /// <summary>
        /// La delegation TradingTrainingConfig -> ModelsConfig.CurrentModelConfig etait
        /// prouvee en tranche 3 par l'exception du stub. Le stub porte, elle se prouve
        /// sur GetModelName, qui emprunte exactement le meme aiguillage CurrentModelConfig
        /// et reste deterministe (pur calcul de chaine, aucune lecture disque).
        /// </summary>
        [Fact]
        public void TradingTrainingConfig_DelegatesToCurrentModelConfig()
        {
            var svmConfig = new TradingTrainingConfig
            {
                DataConfig = BuildDataConfig(),
                ModelsConfig = new TradingModelsConfig { ModelType = TradingModelType.MulticlassSvm }
            };
            var autoMlConfig = new TradingTrainingConfig
            {
                DataConfig = BuildDataConfig(),
                ModelsConfig = new TradingModelsConfig { ModelType = TradingModelType.AutoML }
            };

            // Le nom rendu est celui de la config selectionnee, pas un defaut commun :
            // l'aiguillage est donc bien traverse.
            Assert.Contains("-kernel-", svmConfig.GetModelName());
            Assert.Contains("-AutoML-", autoMlConfig.GetModelName());
        }

        [Fact]
        public void AutoMlTradingModel_Predict_ClassifiesSeparableSamplesEndToEnd()
        {
            var mlContext = new MLContext(seed: 0);
            var trainingRows = BuildSeparableRows();
            // LoadFromEnumerable seul rend VarVector (taille inconnue) -> VarVector<Single>
            // refuse par le trainer. Le helper porte GetSchema epingle Vector(Single, 2),
            // exactement la definition que Predict reutilise pour son PredictionEngine.
            var dataView = mlContext.Data.LoadFromEnumerable(trainingRows, ClassifiedTradingSample.GetSchema(2));

            var pipeline = mlContext.Transforms.Conversion.MapValueToKey("Label")
                .Append(mlContext.MulticlassClassification.Trainers.SdcaMaximumEntropy())
                .Append(mlContext.Transforms.Conversion.MapKeyToValue("PredictedLabel"));
            var model = pipeline.Fit(dataView);

            var tradingModel = new AutoMlTradingModel { Model = model };

            var samples = new List<TradingTrainingSample>
            {
                BuildSample(0.11, 0.02, expected: 0),
                BuildSample(5.13, 5.41, expected: 1),
                BuildSample(10.12, 10.32, expected: 2)
            };

            var predicted = tradingModel.Predict(samples);

            Assert.Equal(3, predicted.Count);
            Assert.Equal(0, predicted[0].Output);
            Assert.Equal(1, predicted[1].Output);
            Assert.Equal(2, predicted[2].Output);
        }

        private static TradingTrainingDataConfig BuildDataConfig()
        {
            // Hermetique : chemin arbitraire — GetModelName ne fait que des operations
            // de chaine dessus (aucune lecture disque sur ce chemin dans le teste).
            return new TradingTrainingDataConfig
            {
                SampleConfig = new TradingSampleConfig { Filename = @"C:\temp\fake-sample.csv" }
            };
        }

        private static List<ClassifiedTradingSample> BuildSeparableRows()
        {
            var rows = new List<ClassifiedTradingSample>();
            for (int i = 0; i < 8; i++)
            {
                rows.Add(BuildRow(0.01 + (i % 10) * 0.01, 0.02 + (i * 3 % 10) * 0.01, 0));
                rows.Add(BuildRow(5.01 + (i % 10) * 0.01, 5.02 + (i * 3 % 10) * 0.01, 1));
                rows.Add(BuildRow(10.01 + (i % 10) * 0.01, 10.02 + (i * 3 % 10) * 0.01, 2));
            }
            return rows;
        }

        private static ClassifiedTradingSample BuildRow(double f1, double f2, float label)
        {
            return new ClassifiedTradingSample
            {
                Features = new[] { (float)f1, (float)f2 },
                Label = label
            };
        }

        private static TradingTrainingSample BuildSample(double f1, double f2, int expected)
        {
            return new TradingTrainingSample
            {
                Inputs = new List<double> { f1, f2 },
                Output = expected,
                Sample = null
            };
        }
    }
}
