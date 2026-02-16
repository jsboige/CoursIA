using System;
using System.Linq;
using QuantConnect.Indicators;
using MathNet.Numerics;
using MathNet.Numerics.LinearAlgebra;

namespace QuantConnect.Algorithm.CSharp.Helpers
{
    public class AnnualizedExponentialSlopeIndicator : WindowIndicator<IndicatorDataPoint>
    {
        private readonly double[] t;

        public AnnualizedExponentialSlopeIndicator(int period) : base("AESI(" + period + ")", period)
        {
            t = Vector<double>.Build.Dense(period, i => i + 1).ToArray();
        }

        public AnnualizedExponentialSlopeIndicator(string name, int period) : base(name, period)
        {
            t = Vector<double>.Build.Dense(period, i => i + 1).ToArray();
        }

        protected override decimal ComputeNextValue(IReadOnlyWindow<IndicatorDataPoint> window, IndicatorDataPoint input)
        {
            if (window.Samples <= window.Size) return 0m;
            var series = window.OrderBy(i => i.Time).Select(i => Convert.ToDouble(Math.Log(Convert.ToDouble(i.Value)))).ToArray();
            var ols = Fit.Line(x: t, y: series);
            var intercept = ols.Item1;
            var slope = ols.Item2;
            var rsquared = GoodnessOfFit.RSquared(t.Select(x => intercept + slope * x), series);
            if (double.IsNaN(slope) || Math.Abs(slope) < 1e-25) return 0m;
            const int dayCount = 252;
            var annualSlope = ((Math.Pow(Math.Exp(slope), dayCount)) - 1) * 100;
            annualSlope = annualSlope * rsquared;
            if (annualSlope >= (double)decimal.MaxValue || annualSlope <= (double)decimal.MinValue)
                annualSlope = 0;
            return Convert.ToDecimal(annualSlope);
        }
    }
}
