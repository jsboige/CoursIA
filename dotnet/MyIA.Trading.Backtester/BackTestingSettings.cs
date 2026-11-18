using System;
using Accord.MachineLearning;
using Accord.MachineLearning.VectorMachines;
using Accord.Statistics.Kernels;
using MyIA.Trading.Backtester;
using Newtonsoft.Json;

namespace MyIA.Trading.Backtester
{
    public class BackTestingSettings
    {
        public TradingTrainingConfig TrainingConfig
        {
            get => _trainingConfig;
            set
            {
                _Strategy = null;
                _trainingConfig = value;
            }
        }

        public double TestError { get; set; }

        public TradingHistory Results { get; set; }

        private ModelStrategy _Strategy;
        private TradingTrainingConfig _trainingConfig = new TradingTrainingConfig();

        public ModelStrategy GetModelStrategy(Action<string> logger)
        {
            if (_Strategy == null)
            {
                double testError = double.MinValue;
                ITradingModel model = TrainingConfig.TrainModel(logger,ref testError);
                TestError = testError;
                if (model != null)
                {
                    _Strategy= new ModelStrategy()
                    {
                        Model = model,
                        TrainingConfig = TrainingConfig,
                        Logger = logger,
                        AskReserveRate = 0,
                        BidReserveRate = 0
                    };
                }
            }


            return _Strategy;
        }

        public decimal GetResult()
        {
            return Results.LastWallet.GetBalance(Results.LastTicker).Total;
        }


    }
}
