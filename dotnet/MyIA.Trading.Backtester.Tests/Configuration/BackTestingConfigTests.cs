using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Microsoft.ML.AutoML;
using Xunit;

namespace MyIA.Trading.Backtester.Tests.Configuration
{
    /// <summary>
    /// Tests de la tranche 6B-2 (EPIC #7357) : configuration de l'orchestrateur
    /// de backtesting et expansion des grilles AutoML/SVM sans acces disque.
    /// </summary>
    public sealed class BackTestingConfigTests
    {
        private sealed class CapturingBackTestingConfig : BackTestingConfig
        {
            public List<TradingTrainingConfig> CapturedConfigurations { get; } = new();

            protected override BackTestingSettings CreateBackTestingSettings(
                TradingTrainingConfig trainingConfig, Action<string> logger)
            {
                CapturedConfigurations.Add(trainingConfig);
                return new BackTestingSettings { TrainingConfig = trainingConfig };
            }
        }

        [Fact]
        public void Constructor_ProvidesOperationalDefaults()
        {
            var config = new BackTestingConfig();

            Assert.Equal(int.MaxValue, config.MaxNb);
            Assert.Equal(BackTestingMode.SVMModels, config.Mode);
            Assert.Equal(ConfigMode.List, config.ConfigMode);
            Assert.True(config.CreateAll);
            Assert.Equal(100, config.BestNb);
            Assert.Equal(TimeSpan.FromHours(12), config.BoostedPrediction);
            Assert.Equal(5m, config.BoostedThresold);
            Assert.Equal(5m, config.BoostedStopLoss);
            Assert.NotNull(config.TrainingConfig);
            Assert.NotEmpty(config.Simulations);
        }

        [Fact]
        public void FileBasedSimulation_InheritsSimulationDefaultsAndAcceptsDatasource()
        {
            var before = DateTime.Now.Subtract(TimeSpan.FromDays(60));
            var simulation = new FileBasedSimulation { DatasourcePath = @"C:\feeds\ticks.bin.7z" };
            var after = DateTime.Now.Subtract(TimeSpan.FromDays(60));

            Assert.Equal(@"C:\feeds\ticks.bin.7z", simulation.DatasourcePath);
            Assert.InRange(simulation.StartDate, before, after);
            Assert.Equal(TimeSpan.FromMinutes(5), simulation.BotPeriod);
            Assert.True(simulation.FastSimulation);
        }

        [Fact]
        public void CombinationMode_ExpandsAutoMlAndSvmConfigurationsFromIndependentClones()
        {
            var trainStart = new DateTime(2020, 1, 1);
            var trainEnd = new DateTime(2021, 1, 1);
            var testStart = new DateTime(2021, 2, 1);
            var testEnd = new DateTime(2022, 2, 1);
            var sourceStart = new DateTime(2013, 5, 1);
            var config = new CapturingBackTestingConfig
            {
                ConfigMode = ConfigMode.Combination,
                TrainPeriods = new() { Tuple.Create(trainStart, trainEnd) },
                TestPeriods = new() { Tuple.Create(testStart, testEnd) },
                PredictionModes = new() { PredictionMode.ThresholdPeak },
                PredictionTimes = new() { TimeSpan.FromHours(18) },
                Thresholds = new() { 7m },
                TrainingSizes = new() { 120 },
                TestSizes = new() { 40 },
                TrainingTimeouts = new() { TimeSpan.FromSeconds(30) },
                ClassificationMetrics = new() { MulticlassClassificationMetric.MicroAccuracy },
                Kernels = new() { KnownKernel.Polynomial3 },
                Complexities = new() { 2.5 },
                TrainingConfig = new TradingTrainingConfig
                {
                    DataConfig = new TradingTrainingDataConfig { TrainStartDate = sourceStart }
                }
            };

            var settings = config.GetBackTestingSettings(_ => { });

            Assert.Equal(2, settings.Count);
            Assert.Equal(2, config.CapturedConfigurations.Count);
            Assert.Equal(
                new[] { TradingModelType.AutoML, TradingModelType.MulticlassSvm },
                config.CapturedConfigurations.Select(item => item.ModelsConfig.ModelType));

            foreach (var generated in config.CapturedConfigurations)
            {
                Assert.Equal(trainStart, generated.DataConfig.TrainStartDate);
                Assert.Equal(trainEnd, generated.DataConfig.TrainEndDate);
                Assert.Equal(testStart, generated.DataConfig.TestStartDate);
                Assert.Equal(testEnd, generated.DataConfig.TestEndDate);
                Assert.Equal(PredictionMode.ThresholdPeak, generated.DataConfig.PredictionMode);
                Assert.Equal(TimeSpan.FromHours(18), generated.DataConfig.OutputPrediction);
                Assert.Equal(7m, generated.DataConfig.OutputThresold);
                Assert.Equal(120, generated.DataConfig.TrainNb);
                Assert.Equal(40, generated.DataConfig.TestNb);
                Assert.NotSame(config.TrainingConfig, generated);
                Assert.NotSame(config.TrainingConfig.DataConfig, generated.DataConfig);
            }

            var autoMl = config.CapturedConfigurations.Single(
                item => item.ModelsConfig.ModelType == TradingModelType.AutoML);
            Assert.Equal(TimeSpan.FromSeconds(30), autoMl.ModelsConfig.AutomMlModelConfig.TrainingTimeout);
            Assert.Equal(
                MulticlassClassificationMetric.MicroAccuracy,
                autoMl.ModelsConfig.AutomMlModelConfig.OptimizingMetric);

            var svm = config.CapturedConfigurations.Single(
                item => item.ModelsConfig.ModelType == TradingModelType.MulticlassSvm);
            Assert.Equal(KnownKernel.Polynomial3, svm.ModelsConfig.SvmModelConfig.Kernel);
            Assert.Equal(2.5, svm.ModelsConfig.SvmModelConfig.Complexity);

            Assert.Equal(sourceStart, config.TrainingConfig.DataConfig.TrainStartDate);
        }

        [Fact]
        public void CombinationMode_MultipliesEveryGridDimension()
        {
            var config = new CapturingBackTestingConfig
            {
                ConfigMode = ConfigMode.Combination,
                TrainPeriods = new() { Tuple.Create(DateTime.MinValue, new DateTime(2020, 1, 1)) },
                TestPeriods = new() { Tuple.Create(new DateTime(2020, 2, 1), DateTime.MaxValue) },
                PredictionModes = new() { PredictionMode.Exact, PredictionMode.Peak },
                PredictionTimes = new() { TimeSpan.FromHours(1), TimeSpan.FromHours(2) },
                Thresholds = new() { 5m },
                TrainingSizes = new() { 100 },
                TestSizes = new() { 20 },
                TrainingTimeouts = new() { TimeSpan.FromSeconds(10), TimeSpan.FromSeconds(20) },
                ClassificationMetrics = new() { MulticlassClassificationMetric.MacroAccuracy },
                Kernels = new() { KnownKernel.NormalizedPolynomial3 },
                Complexities = new() { 1.0, 2.0 }
            };

            var settings = config.GetBackTestingSettings(_ => { });

            // 2 prediction modes * 2 horizons * (2 AutoML + 2 SVM) = 16.
            Assert.Equal(16, settings.Count);
        }

        [Fact]
        public void GetBackTestingFileNames_IncludeDatasourceDatesAndBestCount()
        {
            var config = new BackTestingConfig { BestNb = 25 };
            config.TrainingConfig.DataConfig.SampleConfig.Filename = @"C:\samples\trades.bin.7z";
            var simulation = new FileBasedSimulation
            {
                DatasourcePath = @"C:\feeds\krakenEUR.bin.7z",
                StartDate = new DateTime(2021, 1, 2),
                EndDate = new DateTime(2023, 10, 20)
            };
            var root = config.TrainingConfig.DataConfig.SampleConfig.GetRootFolder();
            var datasource = Path.GetFileName(simulation.DatasourcePath);

            Assert.Equal(
                $"{root}Backtests\\{datasource}-2021-1-02--2023-10-20-models.json",
                config.GetBackTestingFileName(simulation));
            Assert.Equal(
                $"{root}Backtests\\{datasource}-2021-1-02--2023-10-20--Best-25-models.json",
                config.GetBackTestingBestFileName(simulation));
        }

        [Fact]
        public void ListMode_AppliesPeriodsAndPredictionModesToIndependentPresets()
        {
            var trainPeriod = Tuple.Create(new DateTime(2019, 1, 1), new DateTime(2020, 1, 1));
            var testPeriod = Tuple.Create(new DateTime(2020, 2, 1), new DateTime(2021, 2, 1));
            var config = new CapturingBackTestingConfig
            {
                ConfigMode = ConfigMode.List,
                TrainPeriods = new() { trainPeriod },
                TestPeriods = new() { testPeriod },
                PredictionModes = new() { PredictionMode.Peak }
            };

            var settings = config.GetBackTestingSettings(_ => { });

#if DEBUG
            Assert.Equal(6, settings.Count);
#else
            Assert.Equal(9, settings.Count);
#endif
            Assert.All(config.CapturedConfigurations, generated =>
            {
                Assert.Equal(trainPeriod.Item1, generated.DataConfig.TrainStartDate);
                Assert.Equal(trainPeriod.Item2, generated.DataConfig.TrainEndDate);
                Assert.Equal(testPeriod.Item1, generated.DataConfig.TestStartDate);
                Assert.Equal(testPeriod.Item2, generated.DataConfig.TestEndDate);
                Assert.Equal(PredictionMode.Peak, generated.DataConfig.PredictionMode);
            });
            Assert.Equal(settings.Count, config.CapturedConfigurations.Distinct().Count());
        }

        [Fact]
        public void GetBackTestingSettings_RejectsUnknownConfigMode()
        {
            var config = new BackTestingConfig { ConfigMode = (ConfigMode)99 };

            Assert.Throws<ArgumentOutOfRangeException>(() => config.GetBackTestingSettings(_ => { }));
        }
    }
}
