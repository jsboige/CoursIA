using System;
using System.Collections.Generic;
using System.IO;
using System.Threading.Tasks;

namespace MyIA.Trading.Backtester
{
    public interface ITradingModel
    {
        IList<TradingTrainingSample> Predict(IList<TradingTrainingSample> inputs);
    }

    public abstract class TradingModelConfig
    {

        public string GetModelExceptionFileName(TradingTrainingDataConfig dataConfig)
        {
            return GetModelName(dataConfig) + "Fail.txt";
        }


        public TimeSpan TrainingTimeout { get; set; } = TimeSpan.FromSeconds(20);

        public abstract string GetModelName(TradingTrainingDataConfig dataConfig);

        public abstract ITradingModel TrainModel(Action<string> logger, TradingTrainingDataConfig dataConfig, ref double testError);

        public static bool ExecuteWithTimeLimit(TimeSpan timeSpan, Action codeBlock)
        {
            try
            {
                Task task = Task.Factory.StartNew(codeBlock);
                task.Wait(timeSpan);
                return task.IsCompleted;
            }
            catch (AggregateException ae)
            {
                throw ae.InnerExceptions[0];
            }
        }

        protected void WriteExceptionFile(Action<string> logger, string exceptionFileName, string exceptionMessage)
        {
            logger(exceptionMessage);
            new FileInfo(exceptionFileName).Directory.Create();
            File.WriteAllText(exceptionFileName, exceptionMessage);
        }

        private static double DoubleEpsilon = 10E-10;

        public static double TestModel(TradingTrainTestData objTrainingData, ITradingModel model)
        {
            //testError = GeneralConfusionMatrix.Estimate(machine, xTest, yTest).Error;
            
            
            var decisions = model.Predict(objTrainingData.Test);
            int good = 0, bad = 0;

            for (int i = 0; i < decisions.Count; i++)
            {
                var actual = objTrainingData.Test[i].Output;
                var prediction = decisions[i].Output;
                if (Math.Abs(prediction - actual) > DoubleEpsilon)
                {
                    if (Math.Abs(actual) > DoubleEpsilon)
                    {
                        if (Math.Abs(prediction) < DoubleEpsilon)
                        {
                            //false negative, count 1
                            bad++;
                        }
                        else
                        {
                            //wrong positive
                            //Opposite prediction, count 2
                            bad += 2;
                        }
                    }
                    else
                    {
                        //false positive, count 1
                        bad++;
                    }
                }
                else
                {
                    if (Math.Abs(prediction) > DoubleEpsilon)
                    {
                        //Good positive
                        good++;
                    }
                }
            }
            return bad - good;
        }
    }
}
