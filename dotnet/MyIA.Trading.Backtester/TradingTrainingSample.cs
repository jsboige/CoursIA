using System;
using System.Collections.Generic;
using System.Linq;

namespace MyIA.Trading.Backtester
{
    public class TradingTrainingSample
    {
        public static readonly int NbClasses = 3;
        public static int NbInputs = 32;


        public List<double> Inputs { get; set; }


        //public float[] InputVector => Inputs.Select(Convert.ToSingle).ToArray();


        public double Output { get; set; }


        //public float OutputLabel => Convert.ToSingle(Output);


        public TradingSample Sample { get; set; }



    }

    public static class TradingTrainingSampleExtensions
    {
        public static double[][] GetInputMatrix(this IEnumerable<TradingTrainingSample> samples)
        {
            //return Inputs.Select(objlist => objlist.ToArray()).ToArray();
            return samples.Select(r => r.Inputs).Select(objlist => objlist.ToArray()).ToArray();
        }

        public static double[] GetOutputValues(this IEnumerable<TradingTrainingSample> samples)
        {
            //return Outputs.ToArray();
            return samples.Select(r => r.Output).ToArray();
        }

        public static int[] GetOutputClasses(this IEnumerable<TradingTrainingSample> samples)
        {
            //return Outputs.Select(obFloat => (int)obFloat).ToArray();
            return samples.Select(r => r.Output).Select(obFloat => (int)obFloat).ToArray();
        }
    }
}
