using System;
using System.Linq.Expressions;
using System.Runtime.CompilerServices;
using System.Text.RegularExpressions;


namespace MyIA.Trading.Backtester
{

    public class TradingTrainingConfig
    {

        public TradingTrainingDataConfig DataConfig { get; set; } = new TradingTrainingDataConfig();

        public TradingModelsConfig ModelsConfig { get; set; } = new TradingModelsConfig();

        public decimal StopLossRate { get; set; } = 2;


        public string GetModelName()
        {
            return ModelsConfig.CurrentModelConfig.GetModelName(DataConfig);
        }

       
        public ITradingModel TrainModel(Action<string> logger, ref double testError)
        {
            return ModelsConfig.CurrentModelConfig.TrainModel(logger, DataConfig, ref testError);
        }
    }
}
