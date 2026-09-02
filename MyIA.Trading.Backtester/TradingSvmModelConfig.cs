using System;
using System.Collections.Generic;
using System.IO;
using System.Xml.Serialization;
using Accord.MachineLearning;
using Accord.MachineLearning.VectorMachines;
using Accord.MachineLearning.VectorMachines.Learning;
using Accord.Statistics.Analysis;
using Accord.Statistics.Kernels;
using Newtonsoft.Json;

namespace MyIA.Trading.Backtester
{

    // Port tranche 4 (EPIC #7357) : le corps SVM du fork MyIntelligenceAgency/Lean
    // (branche MyIABacktesting_integration, sha 612dddf9) est porte ici. La tranche 3
    // avait laisse TrainModel en stub explicite ; il entraine desormais reellement.
    //
    // Substitution : AUCUNE. Le SVM a noyau du fork tourne tel quel sur net9.0 avec
    // Accord.NET 3.8.2-alpha (la version du fork) — restore + build + execution
    // verifies (voir docs/reference/backtester-e2-svm-kernel.md et le corps de la PR).
    // C'est la resolution de l'hypothese « Accord -> ML.NET/sklearn » du commentaire
    // de tranche 3 : ML.NET n'a pas de SVM a noyau, et il n'a pas eu a en fournir un.
    //
    // Trois ecarts DELIBERES avec l'upstream, tous documentes ici :
    //   1. `using DotNetNuke.Services.Log.EventLog` supprime — import jamais utilise
    //      dans le corps (1 seule occurrence : le using lui-meme). C'est l'abandon des
    //      6 DLL Aricie PKP prescrit par l'Option C tranchee par le user le 2026-07-19.
    //   2. L'ordre des membres de `KnownKernel` est celui deja committe en tranche 3,
    //      PAS celui de l'upstream (qui place TStudent2 en 2e). Reordonner changerait
    //      silencieusement la valeur entiere de chaque membre pour toute config deja
    //      serialisee : le nom est stable, l'ordinal ne l'est pas.
    //   3. `CalibrateComplexity` : le bloc sous limite de temps est repare. Voir le
    //      commentaire detaille sur la methode — en l'etat upstream elle ne calibre
    //      rien et renvoie toujours sa valeur initiale.
    public enum KnownKernel
    {
        InverseMultiquadric,
        NormalizedPolynomial3,
        Polynomial3,
        TStudent2
    }

    /// <summary>
    /// Enveloppe <see cref="ITradingModel"/> autour d'un classifieur Accord quelconque :
    /// convertit les echantillons de trading en matrice d'entrees, delegue la decision au
    /// classifieur, et re-emballe les sorties dans des <see cref="TradingTrainingSample"/>.
    /// </summary>
    public class ClassifierTradingModel : ITradingModel
    {

        [XmlIgnore]
        [JsonIgnore]
        public IClassifier<double[], int> Classifier { get; set; }

        public IList<TradingTrainingSample> Predict(IList<TradingTrainingSample> inputs)
        {
            var inputsMatrix = inputs.GetInputMatrix();
            var output = Classifier.Decide(inputsMatrix);

            var toReturn = new List<TradingTrainingSample>(inputs.Count);
            for (var index = 0; index < inputs.Count; index++)
            {
                var sample = inputs[index];
                var newSample = new TradingTrainingSample() { Inputs = sample.Inputs, Sample = sample.Sample };

                newSample.Output = output[index];
                toReturn.Add(newSample);
            }

            return toReturn;
        }

    }

    /// <summary>
    /// Specialisation SVM multiclasse de <see cref="ClassifierTradingModel"/>.
    /// </summary>
    public class SvmTradingModel : ClassifierTradingModel
    {

        public MulticlassSupportVectorMachine<IKernel> Svm
        {
            get => (MulticlassSupportVectorMachine<IKernel>)Classifier;
            set => Classifier = value;
        }
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
            var objSvm = TrainModelInternal(logger, dataConfig, ref testError);
            if (objSvm != null)
            {
                return new SvmTradingModel() { Svm = objSvm };
            }

            return null;
        }

        public double Complexity { get; set; } = -1;

        public KnownKernel Kernel { get; set; } = KnownKernel.InverseMultiquadric;

        public IKernel GetKernel(KnownKernel objKnownKernel)
        {
            switch (objKnownKernel)
            {
                case KnownKernel.InverseMultiquadric:
                    return new InverseMultiquadric();
                case KnownKernel.NormalizedPolynomial3:
                    return new NormalizedPolynomial(3);
                case KnownKernel.Polynomial3:
                    return new Polynomial(3);
                case KnownKernel.TStudent2:
                    return new TStudent(2);
            }

            throw new ApplicationException($"Kernel {objKnownKernel} not accounted for");
        }

        private static Dictionary<string, MulticlassSupportVectorMachine<IKernel>> _CachedModels = new Dictionary<string, MulticlassSupportVectorMachine<IKernel>>();

        private MulticlassSupportVectorMachine<IKernel> TrainModelInternal(Action<string> logger, TradingTrainingDataConfig dataConfig, ref double testingError)
        {

            var modelName = GetModelName(dataConfig);

            MulticlassSupportVectorMachine<IKernel> toReturn = null;
            var exceptionFileName = GetModelExceptionFileName(dataConfig);
            if (File.Exists(exceptionFileName))
            {
                logger($"Skipping previously failed Model: {exceptionFileName}");
                return null;
            }

            if (File.Exists(modelName))
            {
                logger($"Loading Saved Model: {modelName}");
                if (!_CachedModels.TryGetValue(modelName, out toReturn))
                {
                    toReturn = Accord.IO.Serializer.Load<MulticlassSupportVectorMachine<IKernel>>(modelName);
                    _CachedModels[modelName] = toReturn;
                }
            }

            TradingTrainTestData data = null;
            if (toReturn == null)
            {
                logger($"Training new Model: {modelName}");
                data = dataConfig.GetTrainingSets(logger);
                var xTrain = data.Training.GetInputMatrix();
                var yTrain = data.Training.GetOutputClasses();
                var xTest = data.Test.GetInputMatrix();
                var yTest = data.Test.GetOutputClasses();

                var objKernel = GetKernel(Kernel);
                if (Complexity < 0)
                {
                    Complexity = CalibrateComplexity(data, objKernel);
                    logger($"SVM complexity calibrated: {Complexity}");
                }
                else
                {
                    logger($"SVM complexity defined : {Complexity}");
                }

                var teacher = new MulticlassSupportVectorLearning<IKernel>()
                {
                    Learner = (p) => new SequentialMinimalOptimization<IKernel>()
                    {
                        Complexity = Complexity,
                        UseKernelEstimation = true,
                        Kernel = objKernel
                    }
                };

                var startTime = DateTime.Now;
                bool completed = ExecuteWithTimeLimit(TrainingTimeout, () =>
                {
                    try
                    {
                        logger($"Learn start");
                        toReturn = teacher.Learn(xTrain, yTrain);
                    }
                    catch (Exception e)
                    {
                        string exceptionMessage = e.ToString();
                        WriteExceptionFile(logger, exceptionFileName, exceptionMessage);
                        toReturn = null;
                    }
                });

                if (!completed)
                {
                    var exceptionMessage = $"Training timed out: {DateTime.Now.Subtract(startTime).TotalSeconds}s";
                    WriteExceptionFile(logger, exceptionFileName, exceptionMessage);
                    toReturn = null;
                }

                if (toReturn == null)
                {
                    return toReturn;
                }

                double trainError = GeneralConfusionMatrix.Estimate(toReturn, xTrain, yTrain).Error;
                double testError = GeneralConfusionMatrix.Estimate(toReturn, xTest, yTest).Error;
                logger($"SVM train error: {trainError} | test error: {testError}");

                // Calibration probabiliste des sorties (Platt scaling) : requise pour que
                // MulticlassSupportVectorMachine.Probabilities() soit exploitable, cf SvmBenchmark.
                var ml = new MulticlassSupportVectorLearning<IKernel>()
                {
                    Model = toReturn,

                    Learner = (p) => new ProbabilisticOutputCalibration<IKernel>()
                    {
                        Model = p.Model
                    }
                };
                ml.Learn(xTrain, yTrain);

                if (!File.Exists(modelName))
                {
                    (new FileInfo(modelName)).Directory.Create();
                    Accord.IO.Serializer.Save<MulticlassSupportVectorMachine<IKernel>>(toReturn, modelName);
                }

                logger("SVM Training finished");
            }

            if (dataConfig.EnsureModelTested && testingError < 0)
            {
                if (data == null)
                {
                    data = dataConfig.GetTrainingSets(logger);
                }
                testingError = TestModel(data, new ClassifierTradingModel() { Classifier = toReturn });
            }

            return toReturn;

        }

        /// <summary>
        /// Diagnostic console : entraine le modele puis detaille, echantillon par echantillon,
        /// les bonnes decisions, faux positifs, faux negatifs et decisions opposees.
        /// </summary>
        public void SvmBenchmark(TradingTrainingDataConfig dataConfig, Action<string> logger)
        {

            var bitcoinTrain = dataConfig.GetTrainingSets(logger);

            logger("Entering SVM Benchmark");
            double testingError = double.MinValue;
            var machine = TrainModelInternal(logger, dataConfig, ref testingError);
            if (machine == null)
            {
                logger("SVM Benchmark aborted: no model was learnt");
                return;
            }

            var xTrain = bitcoinTrain.Training.GetInputMatrix();
            var yTrain = bitcoinTrain.Training.GetOutputClasses();
            var xTest = bitcoinTrain.Test.GetInputMatrix();
            var yTest = bitcoinTrain.Test.GetOutputClasses();

            double trainError = GeneralConfusionMatrix.Estimate(machine, xTrain, yTrain).Error;
            double testError = GeneralConfusionMatrix.Estimate(machine, xTest, yTest).Error;

            var ml = new MulticlassSupportVectorLearning<IKernel>()
            {
                Model = machine,

                Learner = (p) => new ProbabilisticOutputCalibration<IKernel>()
                {
                    Model = p.Model
                }
            };
            ml.Learn(xTrain, yTrain);

            logger("SVM Training finished");

            var decisions = machine.Decide(xTrain);
            var predictionProbas = machine.Probabilities(xTrain);
            int j = 1, k = 1, l = 1, m = 1;
            for (int i = 0; i < decisions.Length; i++)
            {
                if (decisions[i] != yTrain[i])
                {
                    logger($"Bad Prediction {i}:  {JsonConvert.SerializeObject(decisions[i])} vs y: {yTrain[i].ToString()} ({JsonConvert.SerializeObject(predictionProbas[i])})");
                    j++;
                }
            }

            logger($"SVM Training Error: {trainError}");
            logger($"SVM test Error: {testError}");

            decisions = machine.Decide(xTest);
            predictionProbas = machine.Probabilities(xTest);
            j = 1;
            for (int i = 0; i < decisions.Length; i++)
            {
                if (decisions[i] != yTest[i])
                {
                    if (yTest[i] != 0)
                    {
                        if (decisions[i] == 0)
                        {
                            logger($"False Negative {i}:  {JsonConvert.SerializeObject(decisions[i])} vs y: {yTest[i].ToString()} ({JsonConvert.SerializeObject(predictionProbas[i])})");
                            j++;
                        }
                        else
                        {
                            logger($"Bad Decision {i}:  {JsonConvert.SerializeObject(decisions[i])} vs y: {yTest[i].ToString()} ({JsonConvert.SerializeObject(predictionProbas[i])})");
                            m++;
                        }
                    }
                    else
                    {
                        logger($"False Positive {i}:  {JsonConvert.SerializeObject(decisions[i])} vs y: {yTest[i].ToString()} ({JsonConvert.SerializeObject(predictionProbas[i])})");
                        k++;
                    }
                }
                else
                {
                    if (decisions[i] != 0)
                    {
                        logger($"Good decision {i}:  {JsonConvert.SerializeObject(decisions[i])} vs y: {yTest[i].ToString()} ({JsonConvert.SerializeObject(predictionProbas[i])})");
                        l++;
                    }
                }
            }

            logger($"Good decisions {l} vs {j + k + m} = {m} Bad + {k} False Positive + {j} False Negative");

        }

        /// <summary>
        /// Recherche la complexite (parametre C du SMO) minimisant le score de test, par
        /// exploration geometrique puis bissection entre les bornes retenues.
        /// </summary>
        /// <remarks>
        /// ECART DELIBERE AVEC L'UPSTREAM (ecart 3, cf en-tete de fichier). Dans le fork, le
        /// bloc passe a <see cref="TradingModelConfig.ExecuteWithTimeLimit"/> se contentait de
        /// re-instancier `teacher` sans jamais appeler `Learn` :
        ///
        ///     () => { try { teacher = new MulticlassSupportVectorLearning&lt;IKernel&gt;(); } catch { } }
        ///
        /// `machine` restait donc `null` a chaque iteration, `machine.Decide(xTrain)` levait une
        /// NullReferenceException aussitot avalee par le `catch` englobant, et `testError`
        /// n'etait jamais mis a jour : `testError &lt; currentResult` etant toujours faux
        /// (double.MaxValue), `bestComplexity` conservait sa valeur initiale. La methode
        /// renvoyait donc TOUJOURS 0.0001, tout en journalisant « SVM complexity calibrated ».
        /// Porter ce corps tel quel aurait livre une calibration qui n'en est pas une, sous un
        /// message affirmant le contraire. L'appel d'entrainement evidemment voulu est retabli,
        /// et l'absence de modele est traitee explicitement au lieu d'etre masquee par une NRE.
        /// Le defaut upstream est signale a part (voir le corps de la PR).
        /// </remarks>
        public double CalibrateComplexity(TradingTrainTestData objTrainingData, IKernel objKernel)
        {
            var xTrain = objTrainingData.Training.GetInputMatrix();
            var yTrain = objTrainingData.Training.GetOutputClasses();

            double currentComplexity = 0.0001;
            double maxComplexity = 1000D;
            double minComplexity = currentComplexity;
            double bestComplexity = currentComplexity;

            double currentResult = double.MaxValue;
            Boolean maxedOut = false;
            double testError = double.MaxValue;
            var coef = 100D;

            for (int idx = 0; idx < 25; idx++)
            {
                var teacher = new MulticlassSupportVectorLearning<IKernel>();
                teacher.Learner = (p) => new SequentialMinimalOptimization<IKernel>()
                {
                    Complexity = currentComplexity,
                    UseKernelEstimation = true,
                    Kernel = objKernel
                };
                MulticlassSupportVectorMachine<IKernel> machine = null;
                try
                {
                    bool completed = ExecuteWithTimeLimit(TrainingTimeout,
                        () =>
                        {
                            try
                            {
                                machine = teacher.Learn(xTrain, yTrain);
                            }
                            catch (Exception)
                            {
                                machine = null;
                            }
                        });
                    if (!completed)
                    {
                        break;
                    }

                    if (machine == null)
                    {
                        // Cette complexite ne produit pas de modele : la traiter comme un
                        // plafond atteint plutot que comme une amelioration.
                        maxedOut = true;
                    }
                    else
                    {
                        var ml = new MulticlassSupportVectorLearning<IKernel>()
                        {
                            Model = machine,

                            Learner = (p) => new ProbabilisticOutputCalibration<IKernel>()
                            {
                                Model = p.Model
                            }
                        };
                        ml.Learn(xTrain, yTrain);

                        var trainDecisions = machine.Decide(xTrain);
                        int j = 0;
                        for (int i = 0; i < trainDecisions.Length; i++)
                        {
                            if (trainDecisions[i] != yTrain[i])
                            {
                                j++;
                            }
                        }
                        if (j == 0)
                        {
                            maxedOut = true;
                        }

                        testError = TestModel(objTrainingData, new ClassifierTradingModel() { Classifier = machine });
                    }
                }
                catch (Exception)
                {
                    maxedOut = true;
                }

                if (testError <= currentResult)
                {
                    if (currentComplexity >= bestComplexity)
                    {
                        if (testError < currentResult)
                        {
                            minComplexity = Math.Max(minComplexity, bestComplexity);
                            bestComplexity = currentComplexity;
                            currentResult = testError;
                        }
                    }
                    else
                    {
                        maxComplexity = Math.Min(maxComplexity, bestComplexity);
                        bestComplexity = currentComplexity;
                        currentResult = testError;
                    }
                }
                else
                {
                    if (currentComplexity < bestComplexity)
                    {
                        minComplexity = Math.Max(minComplexity, currentComplexity);
                    }
                    else
                    {
                        if (maxedOut)
                        {
                            if (currentComplexity > bestComplexity)
                            {
                                maxComplexity = Math.Min(maxComplexity, currentComplexity);
                            }
                        }
                    }
                }

                if (!maxedOut)
                {
                    currentComplexity *= coef;
                }
                else
                {
                    if (currentComplexity > bestComplexity)
                    {
                        currentComplexity = (bestComplexity + minComplexity) / 2;
                    }
                    else
                    {
                        currentComplexity = (bestComplexity + maxComplexity) / 2;
                    }
                }
            }

            return bestComplexity;
        }

    }
}
