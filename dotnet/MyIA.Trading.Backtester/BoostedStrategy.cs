// Port tranche 6B-1 (EPIC #7357) : corps du fork MyIntelligenceAgency/Lean
// (branche MyIABacktesting_integration, sha 612dddf9). Trois ecarts documentes :
//   1. `Program.Log` (classe du binaire console upstream, hors perimetre du
//      port de bibliotheque) remplacee par une methode statique equivalente —
//      meme canal console, meme portee statique.
//   2. REPARATION d'un defaut upstream confirme (cf precedent CalibrateComplexity,
//      tranche 4) : le corps original construisait l'ensemble via
//      `models as IList<IClassifier<double[], int>>`. IList<T> etant invariant,
//      ce `as` rend TOUJOURS null sur un List<MulticlassSupportVectorMachine<IKernel>>,
//      et MultiClassBoost(weights, null) levait NullReferenceException sur son
//      controle de dimensions au premier constructeur. Remplace par une
//      conversion explicite `models.Cast<IClassifier<double[], int>>().ToList()`,
//      qui retablit le comportement evidemment voulu (construire l'ensemble).
//   3. REPARATION d'un second defaut upstream confirme, meme famille : le getter
//      original `MultiClassBoost => (MultiClassBoost) Model` castait Model
//      lui-meme, alors que le constructeur y range un wrapper ClassifierTradingModel
//      dont la propriete Classifier porte l'ensemble — InvalidCastException
//      systematique, rendant GetResult inatteignable. Le getter lit desormais
//      `((ClassifierTradingModel)Model).Classifier` et caste ce classifieur.
using System;
using System.Collections.Generic;
using System.Globalization;
using System.Linq;
using Accord.MachineLearning;
using Accord.MachineLearning.Boosting;
using Accord.Statistics;
using MyIA.Trading.Backtester;

namespace MyIA.Trading.Backtester
{
    public class BoostedStrategy : ModelStrategy
    {

        private static void Log(string message)
        {
            Console.WriteLine(message);
        }

        public BoostedStrategy(List<BackTestingSettings> configs)
        {
            _Configs = configs;
            var models = _Configs.Select(objBack => objBack.GetModelStrategy(Log).Model).Cast<SvmTradingModel>().Select(objTradingModel=> objTradingModel.Svm).ToList();
            var weights = _Configs.Select(objBack => 1D).ToList();
            Model = new ClassifierTradingModel()
                {Classifier = new MultiClassBoost(weights, models.Cast<IClassifier<double[], int>>().ToList())};
        }

        private List<BackTestingSettings> _Configs;

        private Dictionary<int, Tuple<int,DateTime>> TargetDates = new  Dictionary<int, Tuple<int, DateTime>>();

        public MultiClassBoost MultiClassBoost => (MultiClassBoost)((ClassifierTradingModel)Model).Classifier;

        public override int GetResult(TradingTrainingSample objInputs, DateTime time)
        {

            var details = MultiClassBoost.DecideDetail(objInputs.Inputs.ToArray());
            for (var index = 0; index < details.Count; index++)
            {
                Tuple<int, DateTime> target;
                if (!TargetDates.TryGetValue(index, out target) || target.Item2 < time)
                {
                    var classified = details[index];
                    var config = _Configs[index];
                    if (classified != 0)
                    {
                        //target = new Tuple<int, DateTime>(classified, time.Add(config.TrainingConfig.OutputPrediction));
                        target = new Tuple<int, DateTime>(classified, time);//.Add(TimeSpan.FromHours(2)));
                        TargetDates[index] = target;
                    }
                }
            }

            var score1 = TargetDates.Count(objPair => objPair.Value.Item1 == 1 && objPair.Value.Item2 >= time);
            var score2 = TargetDates.Count(objPair => objPair.Value.Item1 == 2 && objPair.Value.Item2 >= time);
            //if ((TargetOrder == null || TargetOrder.OrderType == OrderType.Sell) &&  score2 > 4)
            //{
            //    Program.Log($"Date: {time.ToString(CultureInfo.InvariantCulture)} Engaging 2 with score diff: score1 = {score1}, score2 ={score2} ");
            //    return 2;
            //}
            //if ((TargetOrder == null || TargetOrder.OrderType == OrderType.Buy) && score1 > 15 && score2 < 2)
            //{
            //    Program.Log($"Date: {time.ToString(CultureInfo.InvariantCulture)} Engaging 1 with score diff: score1 = {score1}, score2 ={score2} ");
            //    return 1;
            //}

            //if ((TargetOrder == null || TargetOrder.OrderType == OrderType.Sell) && 4*score2 - score1 > 2 )
            //{
            //    Program.Log($"Date: {time.ToString(CultureInfo.InvariantCulture)} Engaging 2 with score diff: score1 = {score1}, score2 ={score2} ");
            //    return 2;
            //}
            //if ((TargetOrder == null || TargetOrder.OrderType == OrderType.Buy) && score1 - 4 * score2 > 2)
            //{
            //    Program.Log($"Date: {time.ToString(CultureInfo.InvariantCulture)} Engaging 1 with score diff: score1 = {score1}, score2 ={score2} ");
            //    return 1;
            //}


            if (time > _TargetReportTime)
            {
                Log($"Date: {time.ToString(CultureInfo.InvariantCulture)} score1 = {score1}, score2 ={score2} ");
                _TargetReportTime.Add(TimeSpan.FromHours(2));
            }


            return 0;


        }

        private DateTime _TargetReportTime = DateTime.MinValue;

    }


}