using System;
using System.Collections.Generic;
using System.Linq;
using MyIA.Trading.Backtester;
using Xunit;

namespace MyIA.Trading.Backtester.Tests
{
    public sealed class TradingModelConfigTests
    {
        private static TradingTrainingSample Sample(double output) => new TradingTrainingSample
        {
            Inputs = new List<double> { output },
            Output = output
        };

        /// <summary>
        /// Verifie la pondération du score d'erreur de TradingModelConfig.TestModel :
        /// good positive +1, false negative +1, false positive +1, wrong positive +2,
        /// prediction nulle correcte neutre. Score = bad - good.
        /// </summary>
        [Fact]
        public void TestModel_WeightsGoodFalseNegativeFalsePositiveAndWrongPositive()
        {
            var data = new TradingTrainTestData(0, 5);
            data.Test = new List<TradingTrainingSample>
            {
                Sample(1), // good positive : actual 1, pred 1
                Sample(0), // null correct : actual 0, pred 0 (neutre)
                Sample(1), // false negative : actual 1, pred 0
                Sample(0), // false positive : actual 0, pred 1
                Sample(1), // wrong positive : actual 1, pred 2
            };
            ITradingModel model = new EchoModel(new List<double> { 1, 0, 0, 1, 2 });

            double score = TradingModelConfig.TestModel(data, model);

            // bad = 1 (FN) + 1 (FP) + 2 (wrong positive) = 4 ; good = 1 ; attendu 4 - 1 = 3
            Assert.Equal(3, score, 10);
        }

        [Fact]
        public void TestModel_PerfectPredictionsScoreMinusCount()
        {
            var data = new TradingTrainTestData(0, 3);
            data.Test = new List<TradingTrainingSample> { Sample(1), Sample(1), Sample(2) };
            ITradingModel model = new EchoModel(new List<double> { 1, 1, 2 });

            Assert.Equal(-3, TradingModelConfig.TestModel(data, model), 10);
        }

        [Fact]
        public void FastRandom_NextRespectsExclusiveUpperBoundAndIsSeeded()
        {
            var first = new FastRandom(42);
            var second = new FastRandom(42);
            var sequenceA = new List<int>();
            var sequenceB = new List<int>();
            for (int i = 0; i < 1000; i++)
            {
                int a = first.Next(5, 10);
                sequenceA.Add(a);
                sequenceB.Add(second.Next(5, 10));
                Assert.InRange(a, 5, 9);
            }
            Assert.Equal(sequenceA, sequenceB);
        }

        [Fact]
        public void Shuffle_IsAPermutationOfTheOriginalList()
        {
            var list = Enumerable.Range(0, 100).ToList();

            list.Shuffle();

            Assert.Equal(100, list.Count);
            Assert.Equal(Enumerable.Range(0, 100).Sum(), list.Sum());
            Assert.Equal(100, list.Distinct().Count());
        }

        private sealed class EchoModel : ITradingModel
        {
            private readonly Queue<double> _predictions;

            public EchoModel(IEnumerable<double> predictions)
            {
                _predictions = new Queue<double>(predictions);
            }

            public IList<TradingTrainingSample> Predict(IList<TradingTrainingSample> inputs)
            {
                return inputs
                    .Select(input => new TradingTrainingSample { Inputs = input.Inputs, Output = _predictions.Dequeue() })
                    .ToList();
            }
        }
    }
}
