using System;

namespace MyIA.Trading.Backtester
{
    [Serializable]
    public class CompoundTradingStrategy : TradingStrategyBase
    {
        private TradingStrategies _strategies;

        public TradingStrategies Strategies
        {
            get
            {
                return this._strategies;
            }
            set
            {
                this._strategies = value;
            }
        }

        public CompoundTradingStrategy()
        {
            this._strategies = new TradingStrategies();
        }

        public override void ComputeNewOrders(ref TradingContext tContext)
        {
            this._strategies.ComputeNewOrders(ref tContext);
        }
    }
}
