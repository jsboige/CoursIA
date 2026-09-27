using System;
using System.IO;

namespace MyIA.Trading.Backtester
{

    // Port minimal tranche 3 (EPIC #7357 geste 3) : la logique de nommage est le code
    // upstream verbatim (Kernel/Complexity inclus), mais l'entrainement SVM n'est pas
    // encore porte — la substitution kernel-SVM Accord -> ML.NET/sklearn (cadrage
    // geste 2, docs/reference/backtester-e2-cadrage.md) fera l'objet de la tranche 4.
    // L'exception est explicite pour qu'aucun appelant ne puisse confondre ce stub
    // avec un entrainement reussi.
    public enum KnownKernel
    {
        InverseMultiquadric,
        NormalizedPolynomial3,
        Polynomial3,
        TStudent2
    }

    public class TradingSvmModelConfig : TradingModelConfig
    {

        public override string GetModelName(TradingTrainingDataConfig dataConfig)
        {
            var toREturn = dataConfig.GetSampleTrainName();
            var modelName = $"{toREturn.Substring(0, toREturn.Length - Path.GetExtension(toREturn).Length)}-kernel-{Kernel}-complexity-{Complexity}-Model.bin";
            return modelName;
        }

        public override ITradingModel TrainModel(Action<string> logger, TradingTrainingDataConfig dataConfig, ref double testError)
        {
            throw new ApplicationException(
                "TradingSvmModelConfig.TrainModel : port SVM en attente (EPIC #7357 tranche 4) — substitution kernel-SVM Accord->ML.NET/sklearn cadrée au geste 2. Utiliser TradingModelType.AutoML.");
        }

        public double Complexity { get; set; } = -1;

        public KnownKernel Kernel { get; set; } = KnownKernel.InverseMultiquadric;
    }
}
