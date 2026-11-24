using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using MyIA.Trading.Converter;
using Newtonsoft.Json;

namespace MyIA.Trading.Backtester
{
    public enum PredictionMode
    {
        /// <summary>
        /// Exact prediction mode means the price will be compared to the target price at the exact time of the prediction
        /// </summary>
        Exact,
        /// <summary>
        /// Peak prediction mode means the price will be compared to the peak price in the next OutputPrediction time span
        /// </summary>
        Peak,
        /// <summary>
        /// ThresholdPeak prediction mode means the price will be compared to the peak price in the next OutputPrediction time span that is above the OutputThresold relative to the target price
        /// </summary>
        ThresholdPeak
    }

    public class TradingTrainingDataConfig
    {

        public TradingSampleConfig SampleConfig { get; set; } = new TradingSampleConfig();
        public DateTime TrainStartDate { get; set; } = new DateTime(2013, 05, 1);
        public DateTime TrainEndDate { get; set; } = new DateTime(2018, 5, 1);

        public DateTime TestStartDate { get; set; } = new DateTime(2018, 05, 1);
        public DateTime TestEndDate { get; set; } = new DateTime(2019, 7, 1);

        //[JsonIgnore()]
        //public Tuple<DateTime, DateTime> TrainPeriod { get; set; } = new Tuple<DateTime, DateTime>(DateTime.MinValue, DateTime.MaxValue);



        //[JsonIgnore()]
        //public Tuple<DateTime, DateTime> TestPeriod { get; set; } = new Tuple<DateTime, DateTime>(DateTime.MinValue, DateTime.MaxValue);

        public decimal PriceCoef { get; set; } = 10;

        [JsonIgnore]
        public Func<TradingSample, List<double>> InputDataFunction { get; set; }

        public TimeSpan OutputPrediction { get; set; } = TimeSpan.FromHours(5);

        public decimal OutputThresold { get; set; } = 5;

        /// <summary>
        /// Exact prediction mode means the price will be compared to the target price at the exact time of the prediction
        /// Peak prediction mode means the price will be compared to the peak price in the next OutputPrediction time span
        /// ThresholdPeak prediction mode means the price will be compared to the peak price in the next OutputPrediction time span that is above the OutputThresold relative to the target price
        /// </summary>
        public PredictionMode PredictionMode { get; set; } = PredictionMode.Exact;


        public int NbClasses { get; set; } = 3;



        public bool SaveTrainingData { get; set; } = false;

        public bool SaveTrainingSets { get; set; } = false;





        public double ClassifiedRate { get; set; } = 0;

        public int TrainNb { get; set; } = 2000;

        public int TestNb { get; set; } = 500;
        public bool EnsureModelTested { get; set; } = false;


        public string GetFilenameBase()
        {
            string toReturn = $"{SampleConfig.GetRootFolder()}Train\\pred-{(int)OutputPrediction.TotalHours}h-thres-{(int)OutputThresold}-span-{TrainStartDate:yyyy-M-dd}-{TrainEndDate:yyyy-M-dd}-test-{TestStartDate:yyyy-M-dd}-{TestEndDate:yyyy-M-dd}";
            if (PredictionMode!=PredictionMode.Exact)
            {
                toReturn = $"{SampleConfig.GetRootFolder()}Train\\mode-{(int)PredictionMode}-pred-{(int)OutputPrediction.TotalHours}h-thres-{(int)OutputThresold}-span-{TrainStartDate:yyyy-M-dd}-{TrainEndDate:yyyy-M-dd}-test-{TestStartDate:yyyy-M-dd}-{TestEndDate:yyyy-M-dd}";
            }
            return toReturn;
        }

        public string GetSampleDataName()
        {
            var toReturn = $"{GetFilenameBase()}-Complete-TrainData.bin.lz4";
            return toReturn;
        }




        public string GetSampleTrainName()
        {
            return $"{GetFilenameBase()}-sets-{TrainNb}-{TestNb}-CRate-{ClassifiedRate}-TrainData.bin";
        }


        private static object _LockTrainingFile = new object();



        public TradingTrainTestData GetTrainingSets(Action<string> logger)
        {

            var trainFileName = GetSampleTrainName();
            TradingTrainTestData trainingAndTestSets;
            string jsonString;
            if (SaveTrainingSets && File.Exists(trainFileName))
            {
                lock (_LockTrainingFile)
                {

                    trainingAndTestSets =
                        TradeConverter.LoadFile<TradingTrainTestData>(logger, trainFileName,
                            TradeHelper.DeSerializationConfig);
                }

                logger($"Loaded {trainFileName}");

            }
            else
            {
                lock (_LockTrainingFile)
                {



                    var completeTrainingData = GetCompleteTrainingSet(logger);


                    logger($"Prepared Data for {trainFileName}");
                    trainingAndTestSets = this.CreateTrainingAndTestSets(TrainNb, TestNb, completeTrainingData, logger);
                    logger($"Created train and test sets for {trainFileName}");

                    if (SaveTrainingSets)
                    {
                        TradeConverter.SaveFile(trainingAndTestSets, trainFileName, "", logger, TradeHelper.SerializationConfig);
                    }

                }

                logger($"Created {trainFileName}");
            }

            return trainingAndTestSets;
        }


        private static readonly Dictionary<string, List<TradingTrainingSample>> _CachedTrainingData = new Dictionary<string, List<TradingTrainingSample>>();


        public List<TradingTrainingSample> GetCompleteTrainingSet(Action<string> logger)
        {
            List<TradingTrainingSample> toReturn;
            var completeSetName = GetSampleDataName();
            if (!_CachedTrainingData.TryGetValue(completeSetName, out toReturn))
            {
                if (SaveTrainingData && File.Exists(completeSetName))
                {
                    toReturn = TradeConverter.LoadFile<List<TradingTrainingSample>>(logger, completeSetName,
                        TradeHelper.DeSerializationConfig);
                }
                else
                {
                    var samples = SampleConfig.Load(logger);
                    samples = samples.Where(objSample =>
                        (objSample.TargetTrade.Time > TrainStartDate && objSample.TargetTrade.Time < TrainEndDate)
                        || (objSample.TargetTrade.Time > TestStartDate && objSample.TargetTrade.Time < TestEndDate)).ToList();
                    logger($"Filtered Data for {completeSetName}");
                    toReturn = CreateTrainingSet(samples);
                    if (SaveTrainingData)
                    {
                        TradeConverter.SaveFile(toReturn, completeSetName, "", logger, TradeHelper.SerializationConfig);
                    }
                }

                _CachedTrainingData[completeSetName] = toReturn;
            }


            return toReturn;
        }


        public TradingTrainTestData CreateTrainingAndTestSets(int trainingNb, int testNb, List<TradingTrainingSample> completeData, Action<string> logger)
        {

            var idxSet = new Dictionary<int, bool>();
            var filteredTrainIdx = completeData
                .Where(r => r.Sample.TargetTrade.Time > TrainStartDate && r.Sample.TargetTrade.Time < TrainEndDate)
                .Select((objDate, idx) => idx).ToList();
            var noByPass = TestStartDate > TrainEndDate;
            logger($"Filtered Data for training set");
            if (ClassifiedRate <= 0)
            {
                //Train set
                filteredTrainIdx.Shuffle();
                for (int i = 0; i < trainingNb; i++)
                {
                    idxSet[filteredTrainIdx[i]] = true;
                }
                logger($"Created training set");
                //Test set
                var filteredTestIdx = completeData
                    .Where(r => r.Sample.TargetTrade.Time > TestStartDate && r.Sample.TargetTrade.Time < TestEndDate)
                    .Select((objSample, idx) => idx).ToList();
                logger($"Filtered Data for test set");
                filteredTestIdx.Shuffle();

                int iTest = 0, countTests = 0;
                while (countTests < testNb)
                {
                    if (noByPass || !idxSet.ContainsKey(filteredTestIdx[iTest]))
                    {
                        idxSet[filteredTestIdx[iTest]] = false;
                        countTests++;
                    }

                    iTest++;
                }
                logger($"Created test set");
            }
            else
            {
                //Train set
                double nbPerClass;
                GetFilteredClassesTrainSet(trainingNb, completeData, filteredTrainIdx, true, ref idxSet);

                //Test set
                var filteredTestIdx = completeData
                    .Where((r, idx) => r.Sample.TargetTrade.Time > TestStartDate && r.Sample.TargetTrade.Time < TestEndDate && (noByPass || !idxSet.ContainsKey(idx)))
                    .Select((objSample, idx) => idx).ToList();
                GetFilteredClassesTrainSet(testNb, completeData, filteredTestIdx, false, ref idxSet);

            }

            var toReturn = new TradingTrainTestData(trainingNb, testNb);
            foreach (var keyPair in idxSet)
            {
                if (keyPair.Value)
                {
                    toReturn.Training.Add(completeData[keyPair.Key]);
                }
                else
                {
                    toReturn.Test.Add(completeData[keyPair.Key]);
                }
            }

            return toReturn;
        }

        private void GetFilteredClassesTrainSet(int trainingNb, List<TradingTrainingSample> completeData, List<int> filteredTrainIdx, bool isTrain, ref Dictionary<int, bool> idxSet)
        {
            var filteredClasses = new List<List<int>>();
            for (int iClass = 0; iClass < NbClasses; iClass++)
            {
                var filteredClassI = filteredTrainIdx.Where(idx => Math.Abs(completeData[idx].Output - iClass) < 0.1).ToList();
                filteredClassI.Shuffle();
                filteredClasses.Add(filteredClassI);
            }

            var nbPerClass = Math.Abs(trainingNb * ClassifiedRate / (100 * (NbClasses - 1)));
            for (int iClass = 1; iClass < NbClasses; iClass++)
            {
                nbPerClass = Math.Min(nbPerClass, filteredClasses[iClass].Count);
            }

            for (int i = 0; i < nbPerClass; i++)
            {
                for (int iClass = 1; i < NbClasses; i++)
                {
                    idxSet[filteredClasses[iClass][i]] = isTrain;
                }
            }

            var leftNb = trainingNb - idxSet.Count(objPair => objPair.Value);
            for (int i = 0; i < leftNb; i++)
            {
                idxSet[filteredClasses[0][i]] = isTrain;
            }
        }


        public List<TradingTrainingSample> CreateTrainingSet(List<TradingSample> samples)
        {
            var toReturn = new List<TradingTrainingSample>(samples.Count);


            //var maxValue = samples.Max(objSample => objSample.Inputs.Max(objTrade => objTrade.Price));
            //var minValue = samples.Min(objSample => objSample.Inputs.Min(objTrade => objTrade.Price));


            foreach (var bitcoinSample in samples)
            {

                var tradingData = this.GetTrainingData(bitcoinSample);
                toReturn.Add(tradingData);

            }

            return toReturn;
        }

        public TradingTrainingSample GetTrainingData(TradingSample objSample)
        {
            var toReturn = new TradingTrainingSample
            {
                Inputs = GetInputData(objSample),
                Sample = objSample
            };
            if (objSample.Outputs.Count > 0)
            {
                toReturn.Output = GetOutputData(objSample);
            }

            return toReturn;
        }

        public List<double> GetInputData(TradingSample objSample)
        {
            if (InputDataFunction != null)
            {
                return InputDataFunction(objSample);
            }

            //return objSample.Inputs.Select(trade => 10*((float) (trade.Price/objSample.TargetTrade.Price)-1)).ToList();
            //return objSample.Inputs.Select(trade => (double)trade.Price ).ToList();
            return objSample.Inputs.Select(trade => (double)this.PriceCoef * ((double)(trade.Price / objSample.TargetTrade.Price) - 1)).ToList();
        }

        public double GetOutputData(TradingSample objSample)
        {
            var percentageThreshold = OutputThresold / 100;

            DateTime peakTime;
            switch (PredictionMode)
            {
                case PredictionMode.Exact:
                    var exactPrediction = objSample.Outputs[this.OutputPrediction];
                    if (exactPrediction.Price / objSample.TargetTrade.Price > (1 + percentageThreshold))
                    {
                        return 1;
                    }

                    if (exactPrediction.Price / objSample.TargetTrade.Price < (1 - percentageThreshold))
                    {
                        return 2;
                    }
                    break;
                case PredictionMode.Peak:
                    peakTime = objSample.TargetTrade.Time.Add(OutputPrediction);
                    var nextPeak = objSample.Peaks[OutputThresold];
                    if (nextPeak.Time < peakTime)
                    {

                        if (nextPeak.Price / objSample.TargetTrade.Price > (1 + percentageThreshold))
                        {
                            return 1;
                        }

                        if (nextPeak.Price / objSample.TargetTrade.Price < (1 - percentageThreshold))
                        {
                            return 2;
                        }
                    }
                    break;
                case PredictionMode.ThresholdPeak:
                    peakTime = objSample.TargetTrade.Time.Add(OutputPrediction);
                    var nextThresholdPeak = objSample.ThresholdPeaks[OutputThresold];
                    if (nextThresholdPeak.Time < peakTime)
                    {
                        if (nextThresholdPeak.Price / objSample.TargetTrade.Price > (1 + percentageThreshold))
                        {
                            return 1;
                        }

                        if (nextThresholdPeak.Price / objSample.TargetTrade.Price < (1 - percentageThreshold))
                        {
                            return 2;
                        }
                    }
                    break;
                default:
                    throw new ArgumentOutOfRangeException();
            }


            return 0;



            //return 10 * (float)((objSample.Outputs[config.OutputPrediction].Price / objSample.TargetTrade.Price)-1) + 0.5F;
            //return (float) objSample.Outputs[trainingConfig.OutputPrediction].Price;
        }


    }
}
