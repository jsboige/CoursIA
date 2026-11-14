
using System.Collections.Generic;

namespace MyIA.Trading.Backtester
{
    public class TradingTrainTestData
    {


        public TradingTrainTestData() : this(0,0)
        {

        }

        public TradingTrainTestData(int trainingNb, int testNb)
        {
            Training = new List<TradingTrainingSample>(trainingNb);
            Test = new List<TradingTrainingSample>(testNb);
        }

        public virtual List<TradingTrainingSample> Training { get; set; }

        public virtual List<TradingTrainingSample> Test { get; set; }

    }
}
