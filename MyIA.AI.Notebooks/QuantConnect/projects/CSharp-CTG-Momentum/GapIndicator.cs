using System;
using System.Linq;
using QuantConnect.Indicators;
using MathNet.Numerics.Statistics;

namespace QuantConnect.Algorithm.CSharp.Helpers
{
    public class GapIndicator : WindowIndicator<IndicatorDataPoint>
    {
        public GapIndicator(int period) : base("GAP(" + period + ")", period) { }
        public GapIndicator(string name, int period) : base(name, period) { }
        public override bool IsReady { get { return Samples >= Period; } }
        protected override decimal ComputeNextValue(IReadOnlyWindow<IndicatorDataPoint> window, IndicatorDataPoint input)
        {
            if (window.Count < 3) return 0m;
            var diff = new double[window.Count];
            for (int i = 0; i < window.Count - 1; i++)
            {
                diff[i] = (double)((window[i + 1] - window[i]) / (window[i] == 0 ? 1 : window[i].Value));
            }
            return (decimal) diff.MaximumAbsolute();
        }
    }
}
