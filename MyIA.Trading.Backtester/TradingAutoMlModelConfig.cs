using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Globalization;
using System.IO;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using System.Transactions;
using System.Xml.Serialization;
using Microsoft.ML;
using Microsoft.ML.AutoML;
//using Microsoft.ML.AutoML;
using Microsoft.ML.Data;
using Newtonsoft.Json;

namespace MyIA.Trading.Backtester
{

    public class AutoMlTradingModel : ITradingModel
    {

        [XmlIgnore]
        [JsonIgnore]
        public ITransformer Model { get; set; }

        public IList<TradingTrainingSample> Predict(IList<TradingTrainingSample> inputs)
        {
            if (_PredictionEngine == null)
            {
                var nbInputs = inputs.First().Inputs.Count;
                var mlContext = new MLContext();

                var predictionEngineOptions = new Microsoft.ML.PredictionEngineOptions()
                {
                    InputSchemaDefinition = ClassifiedTradingSample.GetSchema(nbInputs)
                };

                //var pipeLine =  Model.Append(mlContext.Transforms.Conversion.MapKeyToValue(outputColumnName: nameof(ClassifiedTradingSample.Output), inputColumnName: "Label"));
                _PredictionEngine = mlContext.Model.CreatePredictionEngine<ClassifiedTradingSample, ClassifiedTradingPrediction>(Model, predictionEngineOptions);
                //var keyValues = default(VBuffer<float>);
                //Model.GetOutputSchema(Model.s)[nameof(TradingTrainingSample.Output)].GetKeyValues<float>(ref keyValues);
                //var keys = keyValues.Items().ToDictionary(x => (int)x.Value, x => x.Key);
            }
            var toReturn = new List<TradingTrainingSample>(inputs.Count);
            foreach (var sample in inputs)
            {
                var newSample = new TradingTrainingSample() { Inputs = sample.Inputs, Sample = sample.Sample };
                var sampleML = new ClassifiedTradingSample()
                {
                    Features = sample.Inputs.Select(i => Convert.ToSingle(i)).ToArray(),
                    Label = Convert.ToInt32(sample.Output)//.ToString()
                };
                //inputs.Rows[i].Output = int.Parse(_PredictionEngine.Predict(sampleML).Output, CultureInfo.InvariantCulture);
                var prediction = _PredictionEngine.Predict(sampleML);
                newSample.Output = prediction.PredictedLabel;
                toReturn.Add(newSample);
            }

            return toReturn;

        }

        private PredictionEngine<ClassifiedTradingSample, ClassifiedTradingPrediction> _PredictionEngine;


    }



    public class TradingAutoMlModelConfig : TradingModelConfig
    {


        public MulticlassClassificationMetric OptimizingMetric { get; set; } =
            MulticlassClassificationMetric.MacroAccuracy;





        public override string GetModelName(TradingTrainingDataConfig dataConfig)
        {
            var toREturn = dataConfig.GetSampleTrainName();
            var modelName = $"{toREturn.Substring(0, toREturn.Length - Path.GetExtension(toREturn).Length)}-AutoML-{this.TrainingTimeout.TotalSeconds}s-{this.OptimizingMetric}-Model.bin";
            return modelName;
        }



        public override ITradingModel TrainModel(Action<string> logger, TradingTrainingDataConfig dataConfig, ref double testError)
        {
            var objTransformer = TrainModelInternal(logger, dataConfig, ref testError);
            if (objTransformer == null)
            {
                //throw new InvalidOperationException("no transformer learnt");
                return null;
            }
            return new AutoMlTradingModel() { Model = objTransformer };
        }

        private ITransformer TrainModelInternal(Action<string> logger, TradingTrainingDataConfig dataConfig, ref double testingError)
        {


            ITransformer toReturn = null;
            var exceptionFileName = GetModelExceptionFileName(dataConfig);
            if (File.Exists(exceptionFileName))
            {
                logger($"Skipping previously failed Model: {exceptionFileName}");
                return null;
            }

            var mlContext = new MLContext();
            TradingTrainTestData data = null;

            var modelName = GetModelName(dataConfig);
            if (File.Exists(modelName))
            {
                logger($"Loading Saved Model: {modelName}");
                toReturn = LoadModel(mlContext, modelName);
            }
            if (toReturn == null)
            {
                logger($"Training new Model: {modelName}");
                data = dataConfig.GetTrainingSets(logger);
                var nbInputs = data.Training.First().Inputs.Count;
                logger($"nb Inputs {nbInputs}");

                //if (data.Training.Any(r => r.Inputs.Count != nbInputs))
                //{
                //    Debugger.Break();
                //}

                try
                {
                    logger($"AutoMl Learn start");
                    toReturn = AutoMLTrainingMain(logger, modelName, data);

                }
                catch (Exception e)
                {
                    string exceptionMessage = e.ToString();
                    logger($"AutoML Training Exception: {exceptionMessage}");
                    WriteExceptionFile(logger, exceptionFileName, exceptionMessage);
                    toReturn = null;
                }


                if (toReturn == null)
                {
                    return toReturn;
                }







                logger("AutoMl Training finished");
            }

            if (dataConfig.EnsureModelTested && testingError < 0)
            {
                if (data == null)
                {
                    data = dataConfig.GetTrainingSets(logger);
                }
                var tester = new AutoMlTradingModel() { Model = toReturn };
                testingError = TestModel(data, tester);
            }


            return toReturn;

        }

        public enum TradingTrend
        {
            Neutral = 0,
            Bull = 1,
            Bear = 2,
        }


        private ITransformer AutoMLTrainingMain(Action<string> logger, string modelPath, TradingTrainTestData data)
        {
            var nbInputs = data.Training.First().Inputs.Count;

            var mlContext = new MLContext();

            // Load data from memory data.
            var trainAutoMl = data.Training.Select(r => new ClassifiedTradingSample()
            {
                Features = r.Inputs.Select(Convert.ToSingle).ToArray(),
                Label = /*(TradingTrend)*/ Convert.ToInt32(r.Output)//.ToString(CultureInfo.InvariantCulture)
            }).ToList();
            var testAutoMl = data.Test.Select(r => new ClassifiedTradingSample()
            {
                Features = r.Inputs.Select(Convert.ToSingle).ToArray(),
                Label = /*(TradingTrend)*/ Convert.ToInt32(r.Output)//.ToString(CultureInfo.InvariantCulture)
            });
            var trainTest = trainAutoMl.Concat(testAutoMl).ToList();

            // Create a data view.
            var trainTestDataView = mlContext.Data.LoadFromEnumerable<ClassifiedTradingSample>(trainTest, ClassifiedTradingSample.GetSchema(nbInputs));
            var trainDataView = mlContext.Data.TakeRows(trainTestDataView, trainAutoMl.Count);
            var testDataView = mlContext.Data.SkipRows(trainTestDataView, trainAutoMl.Count);

            //var toReturn = LoadModel(mlContext, modelPath, out var dataViewSchema);

            //if (toReturn==null)
            //{
            //var testDataView = mlContext.Data.LoadFromEnumerable<AutoMLClassTradingSample>(testAutoMl, schemaDef);
            //testDataView = multiColumnKeyPipeline.Fit(testDataView).Transform(testDataView);


            // Run an AutoML experiment on the dataset.
            var experimentResult = RunAutoMLExperiment(mlContext, trainDataView, testDataView);

            //// Evaluate the model and print metrics.
            EvaluateModel(mlContext, experimentResult.BestRun.Model, experimentResult.BestRun.TrainerName, testDataView);


            var toReturn = experimentResult.BestRun.Model;

            var dataViewSchema = trainTestDataView.Schema;

            //// Save / persist the best model to a.ZIP file.
            SaveModel(mlContext, modelPath, toReturn, dataViewSchema);

            // Make a single test prediction loading the model from .ZIP file.
            TestSomePredictions(mlContext, toReturn, data);

            //// Paint regression distribution chart for a number of elements read from a Test DataSet file.
            //PlotRegressionChart(mlContext, TestDataPath, 100, args);

            //// Re-fit best pipeline on train and test data, to produce 
            //// a model that is trained on as much data as is available.
            //// This is the final model that can be deployed to production.
            //var refitModel = RefitBestPipeline(mlContext, experimentResult, columnInference);

            //// Save the re-fit model to a.ZIP file.
            //SaveModel(mlContext, refitModel);

            //}



            return toReturn;

        }


        private ExperimentResult<Microsoft.ML.Data.MulticlassClassificationMetrics> RunAutoMLExperiment(MLContext mlContext,
           IDataView trainData, IDataView testData)
        {
            // STEP 1: Display first few rows of the training data.
            ConsoleHelper.ShowDataViewInConsole(mlContext, trainData);

            // STEP 2: Build a pre-featurizer for use in the AutoML experiment.
            // (Internally, AutoML uses one or more train/validation data splits to 
            // evaluate the models it produces. The pre-featurizer is fit only on the 
            // training data split to produce a trained transform. Then, the trained transform 
            // is applied to both the train and validation data splits.)


            IEstimator<ITransformer> preFeaturizer = null;
            //IEstimator<ITransformer> preFeaturizer =
            //    mlContext.Transforms.Conversion.MapValueToKey("Label", nameof(ClassifiedTradingSample.Output));



            // STEP 3: Customize column information returned by InferColumns API.
            //ColumnInformation columnInformation = columnInference.ColumnInformation;
            //columnInformation.CategoricalColumnNames.Remove("payment_type");
            //columnInformation.IgnoredColumnNames.Add("payment_type");
            //var preProcessingPipeline =



            // STEP 4: Initialize a cancellation token source to stop the experiment.
            var cts = new CancellationTokenSource();

            // STEP 5: Initialize our user-defined progress handler that AutoML will 
            // invoke after each model it produces and evaluates.
            //var progressHandler = new RegressionExperimentProgressHandler();
            var progressHandler = new MulticlassExperimentProgressHandler();

            // STEP 6: Create experiment settings
            var experimentSettings = CreateExperimentSettings(mlContext, cts);

            // STEP 7: Run AutoML regression experiment.
            var experiment = mlContext.Auto().CreateMulticlassClassificationExperiment(experimentSettings);


            ConsoleHelper.ConsoleWriteHeader("=============== Running AutoML experiment ===============");
            //Console.WriteLine($"Running AutoML regression experiment...");
            var stopwatch = Stopwatch.StartNew();
            // Cancel experiment after the user presses any key.
            CancelExperimentAfterAnyKeyPress(cts);
            ExperimentResult<Microsoft.ML.Data.MulticlassClassificationMetrics> experimentResult = experiment.Execute(trainData, testData, labelColumnName: nameof(ClassifiedTradingSample.Label), preFeaturizer: preFeaturizer, progressHandler: progressHandler);
            Console.WriteLine($"{experimentResult.RunDetails.Count()} models were returned after {stopwatch.Elapsed.TotalSeconds:0.00} seconds{Environment.NewLine}");

            // Print top models found by AutoML.
            PrintTopModels(experimentSettings, experimentResult);

            return experimentResult;
        }


        /// <summary>
        /// Create AutoML regression experiment settings.
        /// </summary>
        private MulticlassExperimentSettings CreateExperimentSettings(MLContext mlContext,
            CancellationTokenSource cts)
        {
            var experimentSettings = new MulticlassExperimentSettings();
            experimentSettings.MaxExperimentTimeInSeconds = (uint)this.TrainingTimeout.TotalSeconds;
            experimentSettings.CancellationToken = cts.Token;

            // Set the metric that AutoML will try to optimize over the course of the experiment.
            experimentSettings.OptimizingMetric = OptimizingMetric;

            // Set the cache directory to null.
            // This will cause all models produced by AutoML to be kept in memory 
            // instead of written to disk after each run, as AutoML is training.
            // (Please note: for an experiment on a large dataset, opting to keep all 
            // models trained by AutoML in memory could cause your system to run out 
            // of memory.)
            experimentSettings.CacheDirectoryName = null;


            // Don't use LbfgsPoissonRegression and OnlineGradientDescent trainers during this experiment.
            // (These trainers sometimes underperform on this dataset.)
            //experimentSettings.Trainers.Remove(MulticlassClassificationTrainer.FastForestOva);

            return experimentSettings;
        }

        private static void CancelExperimentAfterAnyKeyPress(CancellationTokenSource cts)
        {
            Task.Run(() =>
            {
                Console.WriteLine("Press any key to stop the experiment run...");
                Console.ReadKey();
                cts.Cancel();
            });
        }

        /// <summary>
        /// Print top models from AutoML experiment.
        /// </summary>
        private static void PrintTopModels(MulticlassExperimentSettings experimentSettings,
            ExperimentResult<MulticlassClassificationMetrics> experimentResult)
        {
            var orderingDico = new Dictionary<MulticlassClassificationMetric, Func<RunDetail, Single>>();
            // Get top few runs ranked by root mean squared error.
            var topRuns = experimentResult.RunDetails
                .Where(r => r.ValidationMetrics != null && !double.IsNaN(r.ValidationMetrics.MacroAccuracy))
                .OrderBy(r => r.ValidationMetrics.MacroAccuracy).Take(3);

            Console.WriteLine($"Top models ranked by {experimentSettings.OptimizingMetric} --");
            ConsoleHelper.PrintMulticlassClassificationMetricsHeader();
            for (var i = 0; i < topRuns.Count(); i++)
            {
                var run = topRuns.ElementAt(i);
                ConsoleHelper.PrintIterationMetrics(i + 1, run.TrainerName, run.ValidationMetrics, run.RuntimeInSeconds);
            }
        }


        /// <summary>
        /// Evaluate the model and print metrics.
        /// </summary>
        private static void EvaluateModel(MLContext mlContext, ITransformer model, string trainerName,
            IDataView testDataView)
        {
            ConsoleHelper.ConsoleWriteHeader("===== Evaluating model's accuracy with test data =====");
            IDataView predictions = model.Transform(testDataView);
            var metrics = mlContext.MulticlassClassification.Evaluate(predictions);
            ConsoleHelper.PrintMulticlassClassificationMetrics(trainerName, metrics);
        }


        /// <summary>
        /// Save/persist the best model to a .ZIP file
        /// </summary>
        private void SaveModel(MLContext mlContext, string modelPath, ITransformer model, DataViewSchema schema)
        {
            ConsoleHelper.ConsoleWriteHeader("=============== Saving the model ===============");

            new FileInfo(modelPath).Directory.Create();
            mlContext.Model.Save(model, schema, modelPath);
            Console.WriteLine($"The model is saved to {modelPath}");
        }



        private static Dictionary<string, ITransformer> _CachedModels = new Dictionary<string, ITransformer>();


        /// <summary>
        /// Save/persist the best model to a .ZIP file
        /// </summary>
        private ITransformer LoadModel(MLContext mlContext, string modelPath)//, out DataViewSchema schema )
        {

            ConsoleHelper.ConsoleWriteHeader("=============== Loading the model ===============");

            ITransformer toReturn = null;
            if (File.Exists(modelPath))
            {
                if (!_CachedModels.TryGetValue(modelPath, out toReturn))
                {
                    toReturn = mlContext.Model.Load(modelPath, out var schema);
                    _CachedModels[modelPath] = toReturn;
                }


            }
            //else
            //{
            //    schema = null;
            //}
            Console.WriteLine($"The model is correctly loaded {modelPath}");
            return toReturn;
        }


        private static void TestSomePredictions(MLContext mlContext, ITransformer trainedModel, TradingTrainTestData data)
        {
            ConsoleHelper.ConsoleWriteHeader("=============== Testing prediction engine ===============");

            var trader = new AutoMlTradingModel() { Model = trainedModel };

            // Sample: 

            var nbPerSet = 10;


            Console.WriteLine("=============== Train data ===============");

            var trainData = data.Training.Take(nbPerSet).ToList();

            var trainPredictions = trader.Predict(trainData);

            for (int i = 0; i < trainData.Count; i++)
            {
                Console.WriteLine("**********************************************************************");
                Console.WriteLine($"Predicted Class: {trainPredictions[i].Output}, actual Class: {trainData[i].Output}");
                Console.WriteLine("**********************************************************************");
            }

            Console.WriteLine("=============== Test data ===============");

            var testData = data.Test.Take(nbPerSet).ToList();

            var testPredictions = trader.Predict(testData);

            for (int i = 0; i < trainData.Count; i++)
            {
                Console.WriteLine("**********************************************************************");
                Console.WriteLine($"Predicted Class: {testPredictions[i].Output}, actual Class: {testData[i].Output}");
                Console.WriteLine("**********************************************************************");
            }


        }

    }


    public class ClassifiedTradingSample
    {
        private static SchemaDefinition _schemaDef;
        public const int NbClasses = 3;
        //public const int NbInputs = 32;

        public static SchemaDefinition GetSchema(int nbInputs)
        {

            if (_schemaDef == null)
            {
                _schemaDef = SchemaDefinition.Create(typeof(ClassifiedTradingSample));

                // Specify the right vector size.
                _schemaDef[nameof(ClassifiedTradingSample.Features)].ColumnType = new VectorDataViewType(NumberDataViewType.Single, nbInputs);
                _schemaDef[nameof(ClassifiedTradingSample.Label)].ColumnType = NumberDataViewType.Single; //TextDataViewType.Instance; //new VectorDataViewType(NumberDataViewType.Int32, TradingTrainingSample.NbClasses);//= NumberDataViewType.Single;
                //schemaDef["Score"].ColumnType = new VectorDataViewType(NumberDataViewType.Single, TradingTrainingSample.NbClasses);    
            }
            return _schemaDef;

        }


        [VectorType]
        [ColumnName("Features")]
        public float[] Features { get; set; } 


        //[ColumnName("Label")]
        public float Label { get; set; }


        //[VectorType(3)]
        //[ColumnName("Score")]
        //public float[] Score { get; set; } = new float[3];


    }


    public class ClassifiedTradingPrediction
    {



        [VectorType(3)]//
        //[ColumnName("Score")]
        public float[] Score { get; set; } //= new float[3];


        public float PredictedLabel { get; set; }

        //public int PredictedClassIdx
        //{
        //    get
        //    {
        //        return Array.IndexOf(Score, Score.Max());
        //    }
        //}


    }



}
