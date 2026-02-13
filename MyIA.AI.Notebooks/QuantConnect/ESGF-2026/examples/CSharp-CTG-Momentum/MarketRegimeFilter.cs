using QuantConnect.Indicators;

namespace QuantConnect.Algorithm.CSharp
{
    public class MarketRegimeFilter
    {
        private SimpleMovingAverage _spyMovingAverage200;

        public MarketRegimeFilter(SimpleMovingAverage spyMovingAverage200)
        {
            _spyMovingAverage200 = spyMovingAverage200;
        }

        public bool RiskON(decimal spyPrice)
        {
            bool riskonSPY = false;
            if (spyPrice > _spyMovingAverage200)
                riskonSPY = true;
            return riskonSPY;
        }
    }
}
