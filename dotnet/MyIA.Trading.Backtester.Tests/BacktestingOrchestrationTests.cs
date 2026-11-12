using System;
using System.Collections.Generic;
using System.Globalization;
using System.IO;
using MyIA.Trading.Backtester;
using Xunit;

namespace MyIA.Trading.Backtester.Tests
{
    /// <summary>
    /// Tranche 6B-3 (#7357) : tests smoke de l'orchestrateur BackTesting porte.
    /// RunSimulation couvre la chaine complete : TradeHelper.Load (CSV) -> wallets
    /// clones via DeepClone -> baseline Hodl + ModelStrategy stub -> SimulationInfo
    /// (6A). RunSimple couvre la boucle SimpleStopStrategy et le clonage du wallet
    /// initial a chaque iteration.
    /// </summary>
    public sealed class BacktestingOrchestrationTests : IDisposable
    {
        private readonly string _dataDir;

        public BacktestingOrchestrationTests()
        {
            _dataDir = Path.Combine(Path.GetTempPath(), "bt6b3_" + Guid.NewGuid().ToString("N"));
            Directory.CreateDirectory(_dataDir);
        }

        public void Dispose()
        {
            try
            {
                Directory.Delete(_dataDir, recursive: true);
            }
            catch (IOException)
            {
            }
        }

        private string WriteTradesCsv(int count)
        {
            var path = Path.Combine(_dataDir, "trades.csv");
            var baseTime = 1600000000L;
            var lines = new List<string>();
            for (int i = 0; i < count; i++)
            {
                long unix = baseTime + i * 600;
                decimal price = 100m + (i % 20);
                decimal amount = 0.5m + (i % 3) * 0.1m;
                lines.Add(string.Format(CultureInfo.InvariantCulture, "{0},{1},{2}", unix, price, amount));
            }

            File.WriteAllLines(path, lines);
            return path;
        }

        private static SimulationInfo CreateFastSimulation(DateTime firstTrade, DateTime lastTrade)
        {
            return new SimulationInfo
            {
                StartDate = firstTrade.AddSeconds(-1),
                EndDate = lastTrade.AddSeconds(-1),
                BotPeriod = TimeSpan.FromMinutes(5),
                // FastSimulation + SkippedVariationRate eleve saute les steps tant que
                // le prix n'a pas varie du taux demande : inadapte a un CSV synthetique
                // a ~19% de variation. Simulation pas-a-pas, chaque trade est servi.
                FastSimulation = false
            };
        }

        private static DateTime TradeTime(int index)
        {
            return DateTimeOffset.FromUnixTimeSeconds(1600000000L + index * 600).UtcDateTime;
        }

        private sealed class IdentityModel : ITradingModel
        {
            public int CallCount { get; private set; }

            public IList<TradingTrainingSample> Predict(IList<TradingTrainingSample> inputs)
            {
                CallCount++;
                return inputs;
            }
        }

        [Fact]
        public void RunSimulation_WithStubModel_ReturnsHistoryAndConsultsModel()
        {
            var csv = WriteTradesCsv(60);
            var sampleConfig = new TradingSampleConfig
            {
                Filename = csv,
                SaveSamples = false,
                // Defauts concus pour des annees de donnees (30 j / 1 j) : reduits a la
                // portee du CSV synthetique (10 h, un trade / 10 min) pour que
                // CreateInput trouve un trade a chaque pas de la fenetre. SampleConfig
                // sert au chargement CSV ; la fenetre qui compte pour la prediction est
                // celle du TrainingConfig porte par ModelStrategy, d'ou l'assignation.
                LeftWindow = TimeSpan.FromMinutes(20),
                ConstantSliceSpan = TimeSpan.FromMinutes(1)
            };
            var trainingConfig = new TradingTrainingConfig();
            trainingConfig.DataConfig.SampleConfig = sampleConfig;
            var model = new IdentityModel();
            var simulation = CreateFastSimulation(TradeTime(0), TradeTime(59));
            var logs = new List<string>();
            var backtesting = new BackTesting();

            var history = backtesting.RunSimulation(simulation, model, sampleConfig, trainingConfig, logs.Add);

            Assert.NotNull(history);
            Assert.NotNull(history.LastWallet);
            Assert.True(model.CallCount > 0, string.Join(Environment.NewLine, logs));
            Assert.Contains(logs, log => log.Contains("starting Machine learning simulation"));
        }

        [Fact]
        public void RunSimple_ExecutesHodlAndStopSimulationsWithoutError()
        {
            var csv = WriteTradesCsv(40);
            var backtesting = new BackTesting();
            backtesting.Config.TrainingConfig.DataConfig.SampleConfig.Filename = csv;
            var simulation = CreateFastSimulation(TradeTime(0), TradeTime(39));
            var logs = new List<string>();

            backtesting.RunSimple(logs.Add, simulation);

            Assert.Contains(logs, log => log.Contains("starting Hodl simulation"));
            Assert.Contains(logs, log => log.Contains("starting Stop simulation"));
        }
    }
}
