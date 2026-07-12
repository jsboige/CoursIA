using System;
using System.Linq;
using QuantConnect.Indicators;
using QuantConnect.Data.Market;

namespace QuantConnect.Algorithm.CSharp.Helpers
{
    public class CustomMomentumIndicator : TradeBarIndicator
    {
        private Symbol _symbol;
        private int _windowSize;
        public readonly AnnualizedExponentialSlopeIndicator AnnualizedSlope;
        public readonly ExponentialMovingAverage MovingAverage;
        public readonly GapIndicator Gap;
        public readonly AverageTrueRange Atr;

        public CustomMomentumIndicator(Symbol symbol, int annualizedSlopeWindow, int movingAverageWindow, int gapWindow, int atrWindow)
            : base($"CMI({symbol}, {annualizedSlopeWindow}, {movingAverageWindow}, {gapWindow})")
        {
            _symbol = symbol;
            AnnualizedSlope = new AnnualizedExponentialSlopeIndicator(annualizedSlopeWindow);
            MovingAverage = new ExponentialMovingAverage(movingAverageWindow);
            Gap = new GapIndicator(gapWindow);
            Atr = new AverageTrueRange(atrWindow);
            _windowSize = (new int[] { movingAverageWindow, annualizedSlopeWindow, gapWindow, atrWindow }).Max();
        }

        public Symbol Symbol { get { return _symbol; } }

        public override void Reset()
        {
            AnnualizedSlope.Reset();
            MovingAverage.Reset();
            Gap.Reset();
            Atr.Reset();
            base.Reset();
        }

        protected override decimal ComputeNextValue(TradeBar input)
        {
            AnnualizedSlope.Update(input.EndTime, input.Value);
            MovingAverage.Update(input.EndTime, input.Value);
            Gap.Update(input.EndTime, input.Value);
            Atr.Update(input);
            return AnnualizedSlope;
        }

        public override bool IsReady
        {
            get { return AnnualizedSlope.IsReady && MovingAverage.IsReady && Gap.IsReady && Atr.IsReady; }
        }

        public int Window
        {
            get { return _windowSize; }
        }
    }
}
