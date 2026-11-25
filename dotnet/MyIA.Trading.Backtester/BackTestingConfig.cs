using System;
using System.Collections.Generic;
using System.IO;
using Microsoft.ML.AutoML;

namespace MyIA.Trading.Backtester
{
    // Port tranche 6B-2 (EPIC #7357) depuis MyIntelligenceAgency/Lean
    // (branche MyIABacktesting_integration, sha 612dddf9). Les presets DEBUG/Release
    // sont conserves verbatim. Seule adaptation : ReflectionHelper.CloneObject,
    // fourni par Aricie, est remplace par l'extension DeepClone deja portee.
    public enum BackTestingMode
    {
        SVMModels,
        Boosting
    }

    public enum ConfigMode
    {
        Combination,
        List
    }


    public class FileBasedSimulation:SimulationInfo
    {

        public string DatasourcePath { get; set; }


    }


    public class BackTestingConfig
    {

        public int MaxNb { get; set; } = int.MaxValue;

        public BackTestingMode Mode { get; set; } = BackTestingMode.SVMModels;



#if DEBUG
        public ConfigMode ConfigMode { get; set; } = ConfigMode.List;
        //public ConfigMode ConfigMode { get; set; } = ConfigMode.Combination;

#else
        public ConfigMode ConfigMode { get; set; } = ConfigMode.List;
        //public ConfigMode ConfigMode { get; set; } = ConfigMode.Combination;


#endif




        public TimeSpan BoostedPrediction { get; set; } = TimeSpan.FromHours(12);

        public decimal BoostedThresold { get; set; } = 5;
        public decimal BoostedStopLoss { get; set; } = 5;

        public bool LoadBest { get; set; } = false;

        public bool LoadAll { get; set; } = false;

        public bool CreateAll { get; set; } = true;

        //public int MaxTestError { get; set; } = 10;

        public bool UpdateAllFile { get; set; } = true;

        public bool UpdateBestFile { get; set; } = true;

        public int BestNb { get; set; } = 100;

        public bool AddCalibratedComplexities { get; set; } = false;

//        public SimulationInfo Simulation { get; set; } = new SimulationInfo()
//        {

//#if DEBUG
//            //StartDate = new DateTime(2015, 1, 1),
//            //EndDate = new DateTime(2018, 1, 1),
//            StartDate = new DateTime(2018, 1, 1),
//            EndDate = new DateTime(2020, 5, 1),

//#else

//            //StartDate = new DateTime(2015, 1, 1),
//            //EndDate = new DateTime(2018, 1, 1),
//            StartDate = new DateTime(2018, 1, 1),
//            EndDate = new DateTime(2020, 5, 1),


//#endif



//            //FastSimulation = false,
//        };



        public TradingTrainingConfig TrainingConfig { get; set; } = new TradingTrainingConfig();



        public List<FileBasedSimulation> Simulations = new List<FileBasedSimulation>(new []
        {

#if DEBUG

            new FileBasedSimulation(){DatasourcePath =@"A:\TradingTests\krakenEUR.bin.7z", StartDate = new DateTime(2021, 1, 1), EndDate = new DateTime(2023, 10, 20),},
            //new FileBasedSimulation(){DatasourcePath =@"A:\TradingTests\bitstampUSD.bin.7z", StartDate = new DateTime(2015, 1, 1), EndDate = new DateTime(2018, 1, 1),},
            //new FileBasedSimulation(){DatasourcePath =@"A:\TradingTests\zaifJPY.2018-2020.0.5.bin.lz4", StartDate = new DateTime(2018, 1, 1), EndDate = new DateTime(2020, 5, 1),},
            //new FileBasedSimulation(){DatasourcePath =@"A:\TradingTests\bitstampUSD.bin.7z", StartDate = new DateTime(2018, 1, 1), EndDate = new DateTime(2020, 5, 1),},
            //new FileBasedSimulation(){DatasourcePath =@"A:\TradingTests\krakenEUR.bin.7z", StartDate = new DateTime(2015, 1, 1), EndDate = new DateTime(2018, 1, 1),},

#else
            new FileBasedSimulation(){DatasourcePath =@"A:\TradingTests\krakenEUR.bin.7z", StartDate = new DateTime(2018, 1, 1), EndDate = new DateTime(2020, 5, 1),},
            new FileBasedSimulation(){DatasourcePath =@"A:\TradingTests\bitstampUSD.bin.7z", StartDate = new DateTime(2015, 1, 1), EndDate = new DateTime(2018, 1, 1),},
            new FileBasedSimulation(){DatasourcePath =@"A:\TradingTests\zaifJPY.2018-2020.0.5.bin.lz4", StartDate = new DateTime(2018, 1, 1), EndDate = new DateTime(2020, 5, 1),},
            new FileBasedSimulation(){DatasourcePath =@"A:\TradingTests\bitstampUSD.bin.7z", StartDate = new DateTime(2018, 1, 1), EndDate = new DateTime(2020, 5, 1),},
            new FileBasedSimulation(){DatasourcePath =@"A:\TradingTests\krakenEUR.bin.7z", StartDate = new DateTime(2015, 1, 1), EndDate = new DateTime(2018, 1, 1),},


#endif




        });


        public List<int> TrainingSizes { get; set; } = new List<int>(new int[]
        {


#if DEBUG

            5000,
            //16000,
            30000

#else
            //1000,
            5000,
            16000,
            30000


#endif


        });

        public List<int> TestSizes { get; set; } = new List<int>(new int[]
        {
            //500,
            5000,
        });


        public List<TimeSpan> PredictionTimes { get; set; } = new List<TimeSpan>(new[]{




#if DEBUG

            TimeSpan.FromHours(24),
            TimeSpan.FromHours(48),
            //TimeSpan.FromDays(10),
            //TimeSpan.FromDays(20),

#else
            TimeSpan.FromHours(24),
            TimeSpan.FromHours(48),
            TimeSpan.FromDays(10),
            TimeSpan.FromDays(20),


#endif



        });

        public List<Decimal> Thresholds { get; set; } = new List<decimal>(new[]
        {


#if DEBUG

            //5M,
            10M,
            //20M,

#else
            //5M,
            10M,
            20M,


#endif


        });


        public List<PredictionMode> PredictionModes { get; set; } = new List<PredictionMode>(new[]
        {

#if DEBUG

             PredictionMode.Exact,
            //PredictionMode.Peak,
            PredictionMode.ThresholdPeak

#else
            PredictionMode.Exact,
            PredictionMode.Peak,
            PredictionMode.ThresholdPeak

#endif


        });

        public List<Tuple<DateTime, DateTime>> TrainPeriods { get; set; } = new List<Tuple<DateTime, DateTime>>(new[]
        {
            new Tuple<DateTime, DateTime>(new DateTime(2014, 5, 1), new DateTime(2018, 1, 1)),

            //new Tuple<DateTime, DateTime>(new DateTime(2018, 1, 1), new DateTime(2020, 5, 1)),

        });

        public List<Tuple<DateTime, DateTime>> TestPeriods { get; set; } = new List<Tuple<DateTime, DateTime>>(new[]
        {



#if DEBUG

            //new Tuple<DateTime, DateTime>(new DateTime(2014, 5, 1), new DateTime(2018, 1, 1)),
            new Tuple<DateTime, DateTime>(new DateTime(2018, 1, 1), new DateTime(2020, 5, 1)),

#else
            //new Tuple<DateTime, DateTime>(new DateTime(2014, 5, 1), new DateTime(2018, 1, 1)),
            new Tuple<DateTime, DateTime>(new DateTime(2018, 1, 1), new DateTime(2020, 5, 1)),
#endif



        });

        public List<double> Complexities { get; set; } = new List<double>(new[]
        {

#if DEBUG

            0.023,  0.105
            //, 3, 51

#else
            0.023,  0.105, 3, 51
#endif


        });


        public List<KnownKernel> Kernels { get; set; } = new List<KnownKernel>(new KnownKernel[]
        {
            // KnownKernel.InverseMultiquadric,
            //KnownKernel.TStudent2,
            //new Laplacian(),
            KnownKernel.NormalizedPolynomial3,
            //KnownKernel.Polynomial3,
            //new Polynomial(4)
        });

        public List<TimeSpan> TrainingTimeouts { get; set; } = new List<TimeSpan>(new TimeSpan[]
        {

#if DEBUG

            //TimeSpan.FromSeconds(10),
            TimeSpan.FromMinutes(2),
            TimeSpan.FromMinutes(10),


#else
            TimeSpan.FromSeconds(10),
            TimeSpan.FromMinutes(2),
            TimeSpan.FromMinutes(10),
#endif



        });

        public List<MulticlassClassificationMetric> ClassificationMetrics { get; set; } = new List<MulticlassClassificationMetric>(new MulticlassClassificationMetric[]
        {

#if DEBUG

             MulticlassClassificationMetric.MacroAccuracy,
            //MulticlassClassificationMetric.MicroAccuracy,
            //MulticlassClassificationMetric.LogLoss,
            //MulticlassClassificationMetric.LogLossReduction

#else
            MulticlassClassificationMetric.MacroAccuracy,
            MulticlassClassificationMetric.MicroAccuracy,
            MulticlassClassificationMetric.LogLoss,
            MulticlassClassificationMetric.LogLossReduction

#endif




        });




        public List<BackTestingSettings> GetBackTestingSettings(Action<string> logger)
        {

            var toReturn = new List<BackTestingSettings>();

            ////To prevent parallel race to base data
            //var initModel = TrainingConfig.TrainModel(logger);

            switch (ConfigMode)
            {
                case ConfigMode.Combination:
                    foreach (var trainPeriod in TrainPeriods)
                    {
                        foreach (var testPeriod in TestPeriods)
                        {
                            foreach (var predictMode in PredictionModes)
                            {
                                foreach (var predictionTime in PredictionTimes)
                                {
                                    foreach (var thresold in Thresholds)
                                    {

                                        foreach (var trainingSize in TrainingSizes)
                                        {
                                            foreach (var testSize in TestSizes)
                                            {

                                                var newTraining = TrainingConfig.DeepClone();
                                                newTraining.DataConfig.TrainStartDate = trainPeriod.Item1;
                                                newTraining.DataConfig.TrainEndDate = trainPeriod.Item2;
                                                newTraining.DataConfig.TestStartDate = testPeriod.Item1;
                                                newTraining.DataConfig.TestEndDate = testPeriod.Item2;

                                                newTraining.DataConfig.OutputPrediction = predictionTime;
                                                newTraining.DataConfig.OutputThresold = thresold;
                                                newTraining.DataConfig.PredictionMode = predictMode;

                                                newTraining.DataConfig.TrainNb = trainingSize;
                                                newTraining.DataConfig.TestNb = testSize;


                                                foreach (var trainingTimeout in TrainingTimeouts)
                                                {
                                                    foreach (var classificationMetric in ClassificationMetrics)
                                                    {
                                                        var newModelTraining = newTraining.DeepClone();
                                                        newModelTraining.ModelsConfig.ModelType = TradingModelType.AutoML;
                                                        newModelTraining.ModelsConfig.CurrentModelConfig
                                                            .TrainingTimeout = trainingTimeout;
                                                        newModelTraining.ModelsConfig.AutomMlModelConfig
                                                            .OptimizingMetric = classificationMetric;

                                                        var toAdd = CreateBackTestingSettings(newModelTraining, logger);
                                                        if (toAdd != null)
                                                        {
                                                            toReturn.Add(toAdd);
                                                            logger($"Added new Model Backtest Settings: {newModelTraining.GetModelName()}");
                                                        }
                                                    }
                                                }



                                                foreach (var kernel in Kernels)
                                                {
                                                    foreach (var complexity in Complexities)
                                                    //Parallel.ForEach(Complexities, complexity =>
                                                    {

                                                        var newModelTraining = newTraining.DeepClone();
                                                        newModelTraining.ModelsConfig.ModelType = TradingModelType.MulticlassSvm;


                                                        newModelTraining.ModelsConfig.SvmModelConfig.Complexity = complexity;
                                                        newModelTraining.ModelsConfig.SvmModelConfig.Kernel = kernel;

                                                        var toAdd = CreateBackTestingSettings(newModelTraining, logger);
                                                        if (toAdd != null)
                                                        {
                                                            toReturn.Add(toAdd);
                                                            logger($"Added new Model Backtest Settings: {newModelTraining.GetModelName()}");
                                                        }
                                                    }
                                                } //);
                                            }
                                        }

                                    }
                                }
                            }
                        }
                    }
                    break;
                case ConfigMode.List:
                    var configList = new List<TradingTrainingConfig>();

#if DEBUG


                    configList.Add(new TradingTrainingConfig() { DataConfig = new TradingTrainingDataConfig() { OutputPrediction = TimeSpan.FromHours(48), OutputThresold = 10, TrainNb = 16000 }, ModelsConfig = new TradingModelsConfig() { SvmModelConfig = new TradingSvmModelConfig() { Kernel = KnownKernel.NormalizedPolynomial3, Complexity = 0.023 } } });
                    configList.Add(new TradingTrainingConfig() { DataConfig = new TradingTrainingDataConfig() { OutputPrediction = TimeSpan.FromHours(48), OutputThresold = 10, TrainNb = 16000 }, ModelsConfig = new TradingModelsConfig() { SvmModelConfig = new TradingSvmModelConfig() { Kernel = KnownKernel.NormalizedPolynomial3, Complexity = 0.105 } } });
                    configList.Add(new TradingTrainingConfig() { DataConfig = new TradingTrainingDataConfig() { OutputPrediction = TimeSpan.FromHours(48), OutputThresold = 10, TrainNb = 16000 }, ModelsConfig = new TradingModelsConfig() { SvmModelConfig = new TradingSvmModelConfig() { Kernel = KnownKernel.NormalizedPolynomial3, Complexity = 3 } } });
                    configList.Add(new TradingTrainingConfig() { DataConfig = new TradingTrainingDataConfig() { OutputPrediction = TimeSpan.FromHours(48), OutputThresold = 10, TrainNb = 16000 }, ModelsConfig = new TradingModelsConfig() { SvmModelConfig = new TradingSvmModelConfig() { Kernel = KnownKernel.NormalizedPolynomial3, Complexity = 51 } } });
                    configList.Add(new TradingTrainingConfig() { DataConfig = new TradingTrainingDataConfig() { OutputPrediction = TimeSpan.FromHours(48), OutputThresold = 10, TrainNb = 30000, TestNb = 5000 }, ModelsConfig = new TradingModelsConfig() { ModelType = TradingModelType.AutoML, AutomMlModelConfig = new TradingAutoMlModelConfig() } });
                    configList.Add(new TradingTrainingConfig() { DataConfig = new TradingTrainingDataConfig() { OutputPrediction = TimeSpan.FromHours(48), OutputThresold = 10, TrainNb = 1000, TestNb = 500 }, ModelsConfig = new TradingModelsConfig() { ModelType = TradingModelType.AutoML, AutomMlModelConfig = new TradingAutoMlModelConfig() } });

                    //configList.Add(new TradingTrainingConfig() { DataConfig = new TradingTrainingDataConfig() { OutputPrediction = TimeSpan.FromHours(48), OutputThresold = 10, TrainNb = 16000 }, ModelsConfig = new TradingModelsConfig() { SvmModelConfig = new TradingSvmModelConfig() { Kernel = KnownKernel.NormalizedPolynomial3, Complexity = 0.105 } } });

                    //configList.Add(new TradingTrainingConfig() { DataConfig = new TradingTrainingDataConfig() { OutputPrediction = TimeSpan.FromHours(48), OutputThresold = 10, TrainNb = 16000 }, ModelsConfig = new TradingModelsConfig() { SvmModelConfig = new TradingSvmModelConfig() { Kernel = KnownKernel.NormalizedPolynomial3, Complexity = 100 } } });



                    //configList.Add(new TradingTrainingConfig() { DataConfig = new TradingTrainingDataConfig() { OutputPrediction = TimeSpan.FromHours(48), OutputThresold = 10, TrainNb = 16000 }, ModelsConfig = new TradingModelsConfig() { SvmModelConfig = new TradingSvmModelConfig() { Kernel = KnownKernel.NormalizedPolynomial3, Complexity = 0.0099 } } });
                    //configList.Add(new TradingTrainingConfig() { DataConfig = new TradingTrainingDataConfig() { OutputPrediction = TimeSpan.FromHours(48), OutputThresold = 10, TrainNb = 16000 }, ModelsConfig = new TradingModelsConfig() { SvmModelConfig = new TradingSvmModelConfig() { Kernel = KnownKernel.NormalizedPolynomial3, Complexity = 0.009901 } } });
                    //configList.Add(new TradingTrainingConfig() { DataConfig = new TradingTrainingDataConfig() { OutputPrediction = TimeSpan.FromHours(48), OutputThresold = 10, TrainNb = 16000 }, ModelsConfig = new TradingModelsConfig() { SvmModelConfig = new TradingSvmModelConfig() { Kernel = KnownKernel.NormalizedPolynomial3, Complexity = 0.023 } } });
                    //configList.Add(new TradingTrainingConfig() { DataConfig = new TradingTrainingDataConfig() { OutputPrediction = TimeSpan.FromHours(48), OutputThresold = 10, TrainNb = 16000 }, ModelsConfig = new TradingModelsConfig() { SvmModelConfig = new TradingSvmModelConfig() { Kernel = KnownKernel.NormalizedPolynomial3, Complexity = 0.023001 } } });
                    //configList.Add(new TradingTrainingConfig() { DataConfig = new TradingTrainingDataConfig() { OutputPrediction = TimeSpan.FromHours(48), OutputThresold = 10, TrainNb = 16000 }, ModelsConfig = new TradingModelsConfig() { SvmModelConfig = new TradingSvmModelConfig() { Kernel = KnownKernel.NormalizedPolynomial3, Complexity = 0.0701 } } });
                    //configList.Add(new TradingTrainingConfig() { DataConfig = new TradingTrainingDataConfig() { OutputPrediction = TimeSpan.FromHours(48), OutputThresold = 10, TrainNb = 16000 }, ModelsConfig = new TradingModelsConfig() { SvmModelConfig = new TradingSvmModelConfig() { Kernel = KnownKernel.NormalizedPolynomial3, Complexity = 0.105 } } });
                    //configList.Add(new TradingTrainingConfig() { DataConfig = new TradingTrainingDataConfig() { OutputPrediction = TimeSpan.FromHours(48), OutputThresold = 10, TrainNb = 16000 }, ModelsConfig = new TradingModelsConfig() { SvmModelConfig = new TradingSvmModelConfig() { Kernel = KnownKernel.NormalizedPolynomial3, Complexity = 0.105001 } } });
                    //configList.Add(new TradingTrainingConfig() { DataConfig = new TradingTrainingDataConfig() { OutputPrediction = TimeSpan.FromHours(48), OutputThresold = 10, TrainNb = 16000 }, ModelsConfig = new TradingModelsConfig() { SvmModelConfig = new TradingSvmModelConfig() { Kernel = KnownKernel.NormalizedPolynomial3, Complexity = 3 } } });
                    //configList.Add(new TradingTrainingConfig() { DataConfig = new TradingTrainingDataConfig() { OutputPrediction = TimeSpan.FromHours(48), OutputThresold = 10, TrainNb = 16000 }, ModelsConfig = new TradingModelsConfig() { SvmModelConfig = new TradingSvmModelConfig() { Kernel = KnownKernel.NormalizedPolynomial3, Complexity = 3.000001 } } });
                    //configList.Add(new TradingTrainingConfig() { DataConfig = new TradingTrainingDataConfig() { OutputPrediction = TimeSpan.FromHours(48), OutputThresold = 10, TrainNb = 16000 }, ModelsConfig = new TradingModelsConfig() { SvmModelConfig = new TradingSvmModelConfig() { Kernel = KnownKernel.NormalizedPolynomial3, Complexity = 51 } } });
                    //configList.Add(new TradingTrainingConfig() { DataConfig = new TradingTrainingDataConfig() { OutputPrediction = TimeSpan.FromHours(48), OutputThresold = 10, TrainNb = 16000 }, ModelsConfig = new TradingModelsConfig() { SvmModelConfig = new TradingSvmModelConfig() { Kernel = KnownKernel.NormalizedPolynomial3, Complexity = 97 } } });

#else

                    configList.Add(new TradingTrainingConfig() { DataConfig = new TradingTrainingDataConfig() { OutputPrediction = TimeSpan.FromHours(48), OutputThresold = 10, TrainNb = 30000, TestNb = 5000 }, ModelsConfig = new TradingModelsConfig() { ModelType = TradingModelType.AutoML, AutomMlModelConfig = new TradingAutoMlModelConfig() { TrainingTimeout = TimeSpan.FromMinutes(30), OptimizingMetric = MulticlassClassificationMetric.MacroAccuracy } } });
                    configList.Add(new TradingTrainingConfig() { DataConfig = new TradingTrainingDataConfig() { OutputPrediction = TimeSpan.FromHours(48), OutputThresold = 10, TrainNb = 30000, TestNb = 5000 }, ModelsConfig = new TradingModelsConfig() { ModelType = TradingModelType.AutoML, AutomMlModelConfig = new TradingAutoMlModelConfig() { TrainingTimeout = TimeSpan.FromMinutes(30), OptimizingMetric = MulticlassClassificationMetric.LogLoss } } });
                    configList.Add(new TradingTrainingConfig() { DataConfig = new TradingTrainingDataConfig() { OutputPrediction = TimeSpan.FromHours(48), OutputThresold = 10, TrainNb = 30000, TestNb = 5000 }, ModelsConfig = new TradingModelsConfig() { ModelType = TradingModelType.AutoML, AutomMlModelConfig = new TradingAutoMlModelConfig() { TrainingTimeout = TimeSpan.FromMinutes(30), OptimizingMetric = MulticlassClassificationMetric.LogLossReduction } } });
                    configList.Add(new TradingTrainingConfig() { DataConfig = new TradingTrainingDataConfig() { OutputPrediction = TimeSpan.FromHours(48), OutputThresold = 10, TrainNb = 30000, TestNb = 5000 }, ModelsConfig = new TradingModelsConfig() { ModelType = TradingModelType.AutoML, AutomMlModelConfig = new TradingAutoMlModelConfig() { TrainingTimeout = TimeSpan.FromMinutes(30), OptimizingMetric = MulticlassClassificationMetric.MicroAccuracy } } });
                    configList.Add(new TradingTrainingConfig() { DataConfig = new TradingTrainingDataConfig() { OutputPrediction = TimeSpan.FromHours(48), OutputThresold = 10, TrainNb = 30000, TestNb = 5000 }, ModelsConfig = new TradingModelsConfig() { ModelType = TradingModelType.AutoML, AutomMlModelConfig = new TradingAutoMlModelConfig() { TrainingTimeout = TimeSpan.FromMinutes(30), OptimizingMetric = MulticlassClassificationMetric.TopKAccuracy } } });




                    //configList.Add(new TradingTrainingConfig() { DataConfig = new TradingTrainingDataConfig() { OutputPrediction = TimeSpan.FromHours(48), OutputThresold = 10, TrainNb = 16000 }, ModelsConfig = new TradingModelsConfig() { SvmModelConfig = new TradingSvmModelConfig() { Kernel = KnownKernel.NormalizedPolynomial3, Complexity = 0.0099 } } });
                    //configList.Add(new TradingTrainingConfig() { DataConfig = new TradingTrainingDataConfig() { OutputPrediction = TimeSpan.FromHours(48), OutputThresold = 10, TrainNb = 16000 }, ModelsConfig = new TradingModelsConfig() { SvmModelConfig = new TradingSvmModelConfig() { Kernel = KnownKernel.NormalizedPolynomial3, Complexity = 0.009901 } } });
                    configList.Add(new TradingTrainingConfig() { DataConfig = new TradingTrainingDataConfig() { OutputPrediction = TimeSpan.FromHours(48), OutputThresold = 10, TrainNb = 16000 }, ModelsConfig = new TradingModelsConfig() { SvmModelConfig = new TradingSvmModelConfig() { Kernel = KnownKernel.NormalizedPolynomial3, Complexity = 0.023 } } });
                    //configList.Add(new TradingTrainingConfig() { DataConfig = new TradingTrainingDataConfig() { OutputPrediction = TimeSpan.FromHours(48), OutputThresold = 10, TrainNb = 16000 }, ModelsConfig = new TradingModelsConfig() { SvmModelConfig = new TradingSvmModelConfig() { Kernel = KnownKernel.NormalizedPolynomial3, Complexity = 0.023001 } } });
                    //configList.Add(new TradingTrainingConfig() { DataConfig = new TradingTrainingDataConfig() { OutputPrediction = TimeSpan.FromHours(48), OutputThresold = 10, TrainNb = 16000 }, ModelsConfig = new TradingModelsConfig() { SvmModelConfig = new TradingSvmModelConfig() { Kernel = KnownKernel.NormalizedPolynomial3, Complexity = 0.0701 } } });
                    configList.Add(new TradingTrainingConfig() { DataConfig = new TradingTrainingDataConfig() { OutputPrediction = TimeSpan.FromHours(48), OutputThresold = 10, TrainNb = 16000 }, ModelsConfig = new TradingModelsConfig() { SvmModelConfig = new TradingSvmModelConfig() { Kernel = KnownKernel.NormalizedPolynomial3, Complexity = 0.105 } } });
                    //configList.Add(new TradingTrainingConfig() { DataConfig = new TradingTrainingDataConfig() { OutputPrediction = TimeSpan.FromHours(48), OutputThresold = 10, TrainNb = 16000 }, ModelsConfig = new TradingModelsConfig() { SvmModelConfig = new TradingSvmModelConfig() { Kernel = KnownKernel.NormalizedPolynomial3, Complexity = 0.105001 } } });
                    configList.Add(new TradingTrainingConfig() { DataConfig = new TradingTrainingDataConfig() { OutputPrediction = TimeSpan.FromHours(48), OutputThresold = 10, TrainNb = 16000 }, ModelsConfig = new TradingModelsConfig() { SvmModelConfig = new TradingSvmModelConfig() { Kernel = KnownKernel.NormalizedPolynomial3, Complexity = 3 } } });
                    //configList.Add(new TradingTrainingConfig() { DataConfig = new TradingTrainingDataConfig() { OutputPrediction = TimeSpan.FromHours(48), OutputThresold = 10, TrainNb = 16000 }, ModelsConfig = new TradingModelsConfig() { SvmModelConfig = new TradingSvmModelConfig() { Kernel = KnownKernel.NormalizedPolynomial3, Complexity = 3.000001 } } });
                    configList.Add(new TradingTrainingConfig() { DataConfig = new TradingTrainingDataConfig() { OutputPrediction = TimeSpan.FromHours(48), OutputThresold = 10, TrainNb = 16000 }, ModelsConfig = new TradingModelsConfig() { SvmModelConfig = new TradingSvmModelConfig() { Kernel = KnownKernel.NormalizedPolynomial3, Complexity = 51 } } });
                    //configList.Add(new TradingTrainingConfig() { DataConfig = new TradingTrainingDataConfig() { OutputPrediction = TimeSpan.FromHours(48), OutputThresold = 10, TrainNb = 16000 }, ModelsConfig = new TradingModelsConfig() { SvmModelConfig = new TradingSvmModelConfig() { Kernel = KnownKernel.NormalizedPolynomial3, Complexity = 97 } } });


#endif

                    foreach (var trainPeriod in TrainPeriods)
                    {
                        foreach (var testPeriod in TestPeriods)
                        {
                            foreach (var predictMode in PredictionModes)
                            {

                                foreach (var config in configList)
                                {
                                    var newConfig = config.DeepClone();
                                    newConfig.DataConfig.TrainStartDate = trainPeriod.Item1;
                                    newConfig.DataConfig.TrainEndDate = trainPeriod.Item2;
                                    newConfig.DataConfig.TestStartDate = testPeriod.Item1;
                                    newConfig.DataConfig.TestEndDate = testPeriod.Item2;
                                    newConfig.DataConfig.PredictionMode = predictMode;

                                    var toAdd = CreateBackTestingSettings(newConfig, logger);
                                    if (toAdd != null)
                                    {
                                        logger($"Adding new Model Backtest Settings: {newConfig.GetModelName()}");
                                        toReturn.Add(toAdd);
                                    }

                                }

                            }

                        }
                    }

                    break;
                default:
                    throw new ArgumentOutOfRangeException();
            }


            return toReturn;
        }

        protected virtual BackTestingSettings CreateBackTestingSettings(
            TradingTrainingConfig trainingConfig, Action<string> logger)
        {
            var settings = new BackTestingSettings { TrainingConfig = trainingConfig };
            return settings.GetModelStrategy(logger) == null ? null : settings;
        }

        public string GetBackTestingFileName(FileBasedSimulation objSimulationInfo)
        {
            var toReturn = TrainingConfig.DataConfig.SampleConfig.GetRootFolder();
            return $"{toReturn}Backtests\\{Path.GetFileName(objSimulationInfo.DatasourcePath)}-{objSimulationInfo.StartDate:yyyy-M-dd-}-{objSimulationInfo.EndDate:yyyy-M-dd-}models.json";
        }

        public string GetBackTestingBestFileName(FileBasedSimulation objSimulationInfo)
        {
            var toReturn = TrainingConfig.DataConfig.SampleConfig.GetRootFolder();
            return $"{toReturn}Backtests\\{Path.GetFileName(objSimulationInfo.DatasourcePath)}-{objSimulationInfo.StartDate:yyyy-M-dd-}-{objSimulationInfo.EndDate:yyyy-M-dd-}-Best-{BestNb}-models.json";
        }
    }
}
