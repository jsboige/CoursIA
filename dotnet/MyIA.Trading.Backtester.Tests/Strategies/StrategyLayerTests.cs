using System;
using System.Collections.Generic;
using System.Linq;
using Accord;
using Accord.MachineLearning;
using Accord.MachineLearning.VectorMachines;
using Accord.MachineLearning.VectorMachines.Learning;
using Accord.Statistics.Kernels;
using FileHelpers;
using Xunit;

namespace MyIA.Trading.Backtester.Tests.Strategies
{
    /// <summary>
    /// Tests de la tranche 6B-1 (EPIC #7357) : couche strategies et resultats
    /// portee du fork MyIntelligenceAgency/Lean (sha 612dddf9) — MultiClassBoost,
    /// ModelStrategy, BoostedStrategy, HodlStrategy, SimpleStopStrategy,
    /// BackTestingSettings, CompareBackTestings, BacktestResult.
    /// </summary>
    public sealed class StrategyLayerTests
    {
        private sealed class FixedClassifier : IClassifier<double[], int>
        {
            private readonly int _label;

            public FixedClassifier(int label)
            {
                _label = label;
            }

            public int Decide(double[] input)
            {
                return _label;
            }

            public int[] Decide(double[][] input)
            {
                return input.Select(_ => _label).ToArray();
            }

            public int[] Decide(double[][] input, int[] result)
            {
                for (int i = 0; i < input.Length; i++)
                {
                    result[i] = _label;
                }

                return result;
            }

            public int Transform(double[] input)
            {
                return _label;
            }

            public int[] Transform(double[][] input)
            {
                return input.Select(_ => _label).ToArray();
            }

            public int[] Transform(double[][] input, int[] result)
            {
                for (int i = 0; i < input.Length; i++)
                {
                    result[i] = _label;
                }

                return result;
            }

            public int NumberOfClasses { get; set; }

            public int NumberOfInputs { get; set; }

            public int NumberOfOutputs { get; set; }
        }

        private sealed class FixedTradingModel : ITradingModel
        {
            private readonly double _output;

            public FixedTradingModel(double output)
            {
                _output = output;
            }

            public IList<TradingTrainingSample> Predict(IList<TradingTrainingSample> inputs)
            {
                var toReturn = new List<TradingTrainingSample>();
                foreach (var input in inputs)
                {
                    toReturn.Add(new TradingTrainingSample
                    {
                        Inputs = input.Inputs,
                        Sample = input.Sample,
                        Output = _output
                    });
                }

                return toReturn;
            }
        }

        /// <summary>
        /// Config SVM de test : l'entrainement est remplace par un mini-SVM reel
        /// (6 points, 3 classes separees, SMO — quelques millisecondes), sans
        /// aucun acces disque ni reseau — sert les tests de BackTestingSettings
        /// et BoostedStrategy. Un MSVM non entraine ne peut pas Decide (etat
        /// interne null chez Accord), d'ou l'entrainement minimal.
        /// </summary>
        private sealed class StubSvmModelConfig : TradingSvmModelConfig
        {
            public const double TrainedTestError = 0.42D;

            public override ITradingModel TrainModel(
                Action<string> logger, TradingTrainingDataConfig dataConfig, ref double testError)
            {
                testError = TrainedTestError;
                var inputs = new[]
                {
                    new[] { 0.0D, 0.0D }, new[] { 0.1D, 0.1D },
                    new[] { 5.0D, 5.0D }, new[] { 5.1D, 5.1D },
                    new[] { -5.0D, 5.0D }, new[] { -5.1D, 5.1D }
                };
                var outputs = new[] { 0, 0, 1, 1, 2, 2 };
                var teacher = new MulticlassSupportVectorLearning<IKernel>
                {
                    Learner = p => new SequentialMinimalOptimization<IKernel>
                    {
                        Complexity = 1D,
                        Kernel = new Linear()
                    }
                };
                return new SvmTradingModel { Svm = teacher.Learn(inputs, outputs) };
            }
        }

        private static BackTestingSettings BuildStubSettings()
        {
            var modelsConfig = new TradingModelsConfig { SvmModelConfig = new StubSvmModelConfig() };
            return new BackTestingSettings
            {
                TrainingConfig = new TradingTrainingConfig { ModelsConfig = modelsConfig }
            };
        }

        private static MultiClassBoost BuildBoost(params int[] labels)
        {
            var weights = new List<double>();
            var models = new List<IClassifier<double[], int>>();
            foreach (var label in labels)
            {
                weights.Add(1D);
                models.Add(new FixedClassifier(label));
            }

            return new MultiClassBoost(weights, models);
        }

        // --- MultiClassBoost -------------------------------------------------

        [Fact]
        public void MultiClassBoost_Decide_ResolvesClassByWeightedScoreThresholds()
        {
            // Difference 2 > 1 : classe 1.
            Assert.Equal(1, BuildBoost(1, 1, 2, 1).Decide(new[] { 0.1D }));
            // Difference 2 > 1 dans l'autre sens : classe 2.
            Assert.Equal(2, BuildBoost(2, 2, 1, 2).Decide(new[] { 0.1D }));
            // Egalite parfaite : neutre.
            Assert.Equal(0, BuildBoost(1, 2).Decide(new[] { 0.1D }));
            // Difference exactement 1 : le seuil upstream est strictement superieur a 1.
            Assert.Equal(0, BuildBoost(1, 1, 2).Decide(new[] { 0.1D }));
        }

        [Fact]
        public void MultiClassBoost_DecideDetail_ListsEachWeakModelDecisionInOrder()
        {
            var boost = BuildBoost(1, 0, 2);

            var details = boost.DecideDetail(new[] { 0.1D });

            Assert.Equal(new List<int> { 1, 0, 2 }, details);
        }

        [Fact]
        public void MultiClassBoost_Constructor_ThrowsWhenWeightsAndModelsDifferInCount()
        {
            var models = new List<IClassifier<double[], int>> { new FixedClassifier(1) };

            Assert.Throws<DimensionMismatchException>(
                () => new MultiClassBoost(new List<double> { 1D, 1D }, models));
        }

        [Fact]
        public void MultiClassBoost_Add_AppendsWeightedModelUsedByDecide()
        {
            var boost = BuildBoost(2);
            boost.Add(3D, new FixedClassifier(1));

            // score1 = 3, score2 = 1 : difference 2 > 1 -> classe 1.
            Assert.Equal(1, boost.Decide(new[] { 0.1D }));
            Assert.Equal(2, boost.Models.Count);
            Assert.Equal(3D, boost[1].Weight);
        }

        // --- BoostedStrategy --------------------------------------------------

        [Fact]
        public void BoostedStrategy_Constructor_BuildsNonNullBoostedEnsembleFromSvmModels()
        {
            // Preuve de la reparation du cast invariant : le corps upstream
            // (`models as IList<IClassifier<double[], int>>` rend null, IList<T>
            // etant invariant) levait NullReferenceException au premier
            // constructeur. La conversion explicite doit produire un ensemble
            // utilisable, non vide.
            var strategy = new BoostedStrategy(new List<BackTestingSettings> { BuildStubSettings() });

            // L'ensemble est verifie via Model.Classifier (le wrapper
            // ClassifierTradingModel). Le getter upstream `MultiClassBoost`
            // castait Model lui-meme en MultiClassBoost et leverait toujours
            // InvalidCastException — defaut repare, la propriete doit rendre
            // le meme ensemble.
            var wrapper = Assert.IsType<ClassifierTradingModel>(strategy.Model);
            var ensemble = Assert.IsType<MultiClassBoost>(wrapper.Classifier);
            Assert.Single(ensemble.Models);
            Assert.Equal(1D, ensemble.Models[0].Weight);
            Assert.NotNull(ensemble.Models[0].Model);

            // Propriete reparee : meme instance d'ensemble.
            Assert.Same(ensemble, strategy.MultiClassBoost);

            // DecideDetail traversable au travers de la propriete (une decision
            // par modele faible, ici le mini-SVM entraine du stub). Assertion de
            // cardinalite seulement, pas de label exact — non brittle.
            var details = strategy.MultiClassBoost.DecideDetail(new[] { 0.1D, 0.2D });
            Assert.Single(details);

            // GetResult desormais atteignable : les retours conditionnels sur
            // les scores etant commentes en upstream, il renvoie toujours 0.
            var sample = new TradingTrainingSample { Inputs = new List<double> { 0.1D, 0.2D } };
            Assert.Equal(0, strategy.GetResult(sample,
                new DateTime(2025, 1, 10, 12, 0, 0, DateTimeKind.Utc)));
        }

        // --- HodlStrategy -----------------------------------------------------

        [Fact]
        public void HodlStrategy_ComputeNewOrders_NeverIssuesOrders()
        {
            var strategy = new HodlStrategy();
            var currentOrders = new Wallet();
            var newOrders = new Wallet { PrimaryBalance = 2m, SecondaryBalance = 500m };
            var market = new MarketInfo(new DateTime(2025, 1, 10, 12, 0, 0, DateTimeKind.Utc))
            {
                Ticker = new Ticker(100m)
            };
            var context = new TradingContext(currentOrders, newOrders, market, new ExchangeInfo(),
                TradingTrend.Neutral, strategy);

            strategy.ComputeNewOrders(ref context);

            Assert.Empty(newOrders.Orders);
            Assert.Empty(currentOrders.Orders);
        }

        // --- SimpleStopStrategy -------------------------------------------------

        private static TradingContext BuildStopContext(
            Wallet newOrders, decimal price, DateTime time, SimpleStopStrategy strategy)
        {
            var market = new MarketInfo(time, new Ticker(price), null, null);
            return new TradingContext(new Wallet(), newOrders, market, new ExchangeInfo(),
                TradingTrend.Neutral, strategy);
        }

        private static void RunStop(SimpleStopStrategy strategy, ref TradingContext context)
        {
            strategy.ComputeNewOrders(ref context);
        }

        [Fact]
        public void SimpleStopStrategy_ComputeNewOrders_ThrowsWhenOpenOrdersRemain()
        {
            var strategy = new SimpleStopStrategy();
            var currentOrders = new Wallet
            {
                Orders = new List<Order> { new Order(OrderType.Buy, 100m, 1m) }
            };
            var market = new MarketInfo(new DateTime(2025, 1, 10, 12, 0, 0, DateTimeKind.Utc))
            {
                Ticker = new Ticker(100m)
            };
            var context = new TradingContext(currentOrders, new Wallet { PrimaryBalance = 1m },
                market, new ExchangeInfo(), TradingTrend.Neutral, strategy);

            Assert.Throws<InvalidOperationException>(() => RunStop(strategy, ref context));
        }

        [Fact]
        public void SimpleStopStrategy_NoOrderUntilStopIsHitThenSellsAtDiscount()
        {
            var strategy = new SimpleStopStrategy();
            var startTime = new DateTime(2025, 1, 10, 12, 0, 0, DateTimeKind.Utc);
            // Portefeuille charge en actif primaire : suivi d'un stop de vente.
            var newOrders = new Wallet { PrimaryBalance = 10m, SecondaryBalance = 100m };

            var context = BuildStopContext(newOrders, 100m, startTime, strategy);
            strategy.ComputeNewOrders(ref context);
            // Prix 100 > stop 80 : pas d'ordre.
            Assert.Empty(newOrders.Orders);

            // Chute sous le stop (80) : vente a 0.99 x prix du solde primaire.
            context = BuildStopContext(newOrders, 79m, startTime.AddHours(1), strategy);
            strategy.ComputeNewOrders(ref context);

            var sell = Assert.Single(newOrders.Orders);
            Assert.Equal(OrderType.Sell, sell.OrderType);
            Assert.Equal(79m * 0.99m, sell.Price);
            Assert.Equal(10m, sell.Amount);
        }

        [Fact]
        public void SimpleStopStrategy_RefactoryPeriodBlocksThenAllowsReEngagement()
        {
            var strategy = new SimpleStopStrategy { RefactoryPeriod = TimeSpan.FromDays(5) };
            var startTime = new DateTime(2025, 1, 10, 12, 0, 0, DateTimeKind.Utc);
            var newOrders = new Wallet { PrimaryBalance = 10m, SecondaryBalance = 100m };

            var context = BuildStopContext(newOrders, 100m, startTime, strategy);
            strategy.ComputeNewOrders(ref context);
            context = BuildStopContext(newOrders, 79m, startTime.AddHours(1), strategy);
            strategy.ComputeNewOrders(ref context);
            Assert.Single(newOrders.Orders);

            // Apres l'engagement, suivi Buy avec stop a 79 x 1.2 = 94.8. Prix 95
            // > 94.8 mais garde strictement superieure a +5 j non passee : rien.
            context = BuildStopContext(newOrders, 95m, startTime.AddHours(2), strategy);
            strategy.ComputeNewOrders(ref context);
            Assert.Single(newOrders.Orders);

            // Hors refraction (garde strictement >), fonds secondaires suffisants :
            // achat a 1.01 x prix d'un montant SecondaryBalance / prix.
            newOrders.SecondaryBalance = 5_000m;
            context = BuildStopContext(newOrders, 95m, startTime.AddHours(1).Add(TimeSpan.FromDays(5)).AddSeconds(1), strategy);
            strategy.ComputeNewOrders(ref context);

            Assert.Equal(2, newOrders.Orders.Count);
            var buy = newOrders.Orders[1];
            Assert.Equal(OrderType.Buy, buy.OrderType);
            Assert.Equal(95m * 1.01m, buy.Price);
            Assert.Equal(5_000m / (95m * 1.01m), buy.Amount);
        }

        [Fact]
        public void SimpleStopStrategy_SellStopRatchetsUpWithRisingPrices()
        {
            var strategy = new SimpleStopStrategy();
            var startTime = new DateTime(2025, 1, 10, 12, 0, 0, DateTimeKind.Utc);
            var newOrders = new Wallet { PrimaryBalance = 10m, SecondaryBalance = 100m };

            // Initialisation du suivi : stop de vente a 100 x 0.8 = 80.
            var context = BuildStopContext(newOrders, 100m, startTime, strategy);
            strategy.ComputeNewOrders(ref context);

            // Hausse a 150 : le stop de vente suit a la hausse (150 x 0.8 = 120),
            // toujours pas d'engagement tant que le prix reste au-dessus.
            context = BuildStopContext(newOrders, 150m, startTime.AddHours(1), strategy);
            strategy.ComputeNewOrders(ref context);
            Assert.Empty(newOrders.Orders);

            // Retombee a 119, sous le stop remonte : engagement de la vente.
            context = BuildStopContext(newOrders, 119m, startTime.AddHours(2), strategy);
            strategy.ComputeNewOrders(ref context);

            var sell = Assert.Single(newOrders.Orders);
            Assert.Equal(OrderType.Sell, sell.OrderType);
            Assert.Equal(119m * 0.99m, sell.Price);
        }

        // --- ModelStrategy -----------------------------------------------------

        private static TradingTrainingConfig BuildTrainingConfig()
        {
            return new TradingTrainingConfig
            {
                DataConfig = new TradingTrainingDataConfig
                {
                    SampleConfig = new TradingSampleConfig
                    {
                        LeftWindow = TimeSpan.FromDays(4),
                        ConstantSliceSpan = TimeSpan.FromDays(1),
                        SamplingMode = SamplingMode.Constant
                    }
                }
            };
        }

        private static List<OrderTrade> BuildDailyTrades(DateTime targetTime, decimal price)
        {
            var trades = new List<OrderTrade>();
            for (int offset = 4; offset >= 0; offset--)
            {
                trades.Add(new OrderTrade
                {
                    Time = targetTime.Subtract(TimeSpan.FromDays(offset)),
                    Price = price,
                    Amount = 1m
                });
            }

            return trades;
        }

        private static TradingContext BuildModelContext(
            ModelStrategy strategy, DateTime time, decimal price, Wallet newOrders,
            List<OrderTrade> recentTrades)
        {
            var market = new MarketInfo(time, new Ticker(price), null, null);
            market.RecentTrades = recentTrades;
            return new TradingContext(new Wallet(), newOrders, market, new ExchangeInfo(),
                TradingTrend.Neutral, strategy);
        }

        private static ModelStrategy BuildStrategy(double output)
        {
            return new ModelStrategy
            {
                Model = new FixedTradingModel(output),
                TrainingConfig = BuildTrainingConfig(),
                Logger = _ => { }
            };
        }

        [Fact]
        public void ModelStrategy_GetResult_ReturnsModelPredictionAsClassLabel()
        {
            var strategy = new ModelStrategy { Model = new FixedTradingModel(2) };
            var sample = new TradingTrainingSample { Inputs = new List<double> { 0.5D } };

            Assert.Equal(2, strategy.GetResult(sample, DateTime.UtcNow));
        }

        [Fact]
        public void ModelStrategy_BuySignalPlacesBuyLimitOrderAtOnePercentMargin()
        {
            var time = new DateTime(2025, 1, 10, 12, 0, 0, DateTimeKind.Utc);
            var newOrders = new Wallet { PrimaryBalance = 1m, SecondaryBalance = 1_000m };
            var strategy = BuildStrategy(1);

            var context = BuildModelContext(strategy, time, 100m, newOrders, BuildDailyTrades(time, 100m));
            strategy.ComputeNewOrders(ref context);

            var order = Assert.Single(newOrders.Orders);
            Assert.Equal(OrderType.Buy, order.OrderType);
            Assert.Equal(100m * 1.01m, order.Price);
            Assert.Equal(newOrders.SecondaryBalance / (100m * 1.01m), order.Amount);
        }

        [Fact]
        public void ModelStrategy_SellSignalPlacesSellLimitOrderAtOnePercentDiscount()
        {
            var time = new DateTime(2025, 1, 10, 12, 0, 0, DateTimeKind.Utc);
            var newOrders = new Wallet { PrimaryBalance = 10m, SecondaryBalance = 100m };
            var strategy = BuildStrategy(2);

            var context = BuildModelContext(strategy, time, 100m, newOrders, BuildDailyTrades(time, 100m));
            strategy.ComputeNewOrders(ref context);

            var order = Assert.Single(newOrders.Orders);
            Assert.Equal(OrderType.Sell, order.OrderType);
            Assert.Equal(100m * 0.99m, order.Price);
            Assert.Equal(10m, order.Amount);
        }

        [Fact]
        public void ModelStrategy_NeutralSignalPlacesNothingAndWindowBlocksRepeatSignals()
        {
            var time = new DateTime(2025, 1, 10, 12, 0, 0, DateTimeKind.Utc);
            var newOrders = new Wallet { PrimaryBalance = 1m, SecondaryBalance = 1_000m };

            var neutral = BuildStrategy(0);
            var context = BuildModelContext(neutral, time, 100m, newOrders, BuildDailyTrades(time, 100m));
            neutral.ComputeNewOrders(ref context);
            Assert.Empty(newOrders.Orders);

            // Fenetre OutputPrediction (5 h par defaut) non ecoulee apres un
            // achat : le signal suivant est ignore, aucun second ordre.
            var buyer = BuildStrategy(1);
            context = BuildModelContext(buyer, time, 100m, newOrders, BuildDailyTrades(time, 100m));
            buyer.ComputeNewOrders(ref context);
            Assert.Single(newOrders.Orders);

            var later = time.AddHours(1);
            context = BuildModelContext(buyer, later, 101m, newOrders, BuildDailyTrades(later, 101m));
            buyer.ComputeNewOrders(ref context);
            Assert.Single(newOrders.Orders);
        }

        // --- BackTestingSettings ------------------------------------------------

        [Fact]
        public void BackTestingSettings_GetResult_ReturnsLastWalletTotalAtLastTickerPrice()
        {
            var settings = new BackTestingSettings
            {
                Results = new TradingHistory
                {
                    LastWallet = new Wallet { PrimaryBalance = 2m, SecondaryBalance = 500m },
                    LastTicker = new Ticker(250m)
                }
            };

            // Total = secondaire + primaire x dernier prix = 500 + 2 x 250.
            Assert.Equal(1_000m, settings.GetResult());
        }

        [Fact]
        public void BackTestingSettings_GetModelStrategy_TrainsOnceCachesAppliesZeroReservesAndResets()
        {
            var settings = BuildStubSettings();

            var first = settings.GetModelStrategy(_ => { });
            var second = settings.GetModelStrategy(_ => { });

            Assert.NotNull(first);
            Assert.Same(first, second);
            Assert.Equal(StubSvmModelConfig.TrainedTestError, settings.TestError);
            Assert.Equal(0m, first.AskReserveRate);
            Assert.Equal(0m, first.BidReserveRate);

            // Reaffecter TrainingConfig invalide la strategie cachee.
            settings.TrainingConfig = new TradingTrainingConfig
            {
                ModelsConfig = new TradingModelsConfig { SvmModelConfig = new StubSvmModelConfig() }
            };
            var third = settings.GetModelStrategy(_ => { });
            Assert.NotSame(first, third);
        }

        // --- CompareBackTestings --------------------------------------------------

        [Fact]
        public void CompareBackTestings_EqualsMatchesModelNameAndHandlesNulls()
        {
            var comparer = new CompareBackTestings();
            var settings = new BackTestingSettings();

            Assert.True(comparer.Equals(null, null));
            Assert.False(comparer.Equals(settings, null));
            Assert.False(comparer.Equals(null, settings));

            // Noms de modeles identiques (config par defaut) : egalite + hash cohérent.
            Assert.True(comparer.Equals(settings, new BackTestingSettings()));
            Assert.Equal(comparer.GetHashCode(settings), comparer.GetHashCode(new BackTestingSettings()));

            // Taille d'ensemble d'entrainement differente -> nom different -> inegalite.
            var other = new BackTestingSettings
            {
                TrainingConfig = new TradingTrainingConfig
                {
                    DataConfig = new TradingTrainingDataConfig { TrainNb = 3_000 }
                }
            };
            Assert.False(comparer.Equals(settings, other));
        }

        // --- BacktestResult --------------------------------------------------

        [Fact]
        public void BacktestResult_DelimitedRecord_SerializesAndRoundTripsWithSemicolons()
        {
            var engine = new FileHelperEngine<BacktestResult>();
            var record = new BacktestResult
            {
                BackTestPeriod = "2018-2019",
                ModelName = "svm-kernel-test",
                TestError = 0.25D,
                Result = 1_500m,
                TradeNb = 12,
                Trade1 = "Buy@100",
                Trade2 = "Sell@120"
            };

            var csv = engine.WriteString(new[] { record });
            var lines = csv.Replace("\r\n", "\n").Split('\n');

            // WriteString n'emet pas d'en-tete par defaut : la premiere ligne est
            // l'enregistrement, delimite par des points-virgules.
            Assert.StartsWith("2018-2019;svm-kernel-test;", lines[0]);
            Assert.Contains("Buy@100", lines[0]);
            Assert.Contains("Sell@120", lines[0]);

            var parsed = engine.ReadString(csv);
            Assert.Single(parsed);
            Assert.Equal("2018-2019", parsed[0].BackTestPeriod);
            Assert.Equal("svm-kernel-test", parsed[0].ModelName);
            Assert.Equal(0.25D, parsed[0].TestError);
            Assert.Equal(1_500m, parsed[0].Result);
            Assert.Equal(12, parsed[0].TradeNb);
            Assert.Equal("Buy@100", parsed[0].Trade1);
        }
    }
}
