using System;
using System.Collections.Generic;
using System.Linq;
using Accord.MachineLearning.VectorMachines;
using Accord.MachineLearning.VectorMachines.Learning;
using Accord.Statistics.Analysis;
using Accord.Statistics.Kernels;
using Xunit;

namespace MyIA.Trading.Backtester.Tests
{
    /// <summary>
    /// Tranche 4 (EPIC #7357 geste 3) : corps SVM porte depuis le fork upstream.
    /// Ces tests portent sur la SUBSTANCE du port — que le SVM a noyau apprenne
    /// reellement une frontiere non lineairement separable — et pas seulement sur le
    /// cablage. Chaque assertion positive est appariee a une mutation qui ne change
    /// QUE le champ teste (le noyau), et qui doit la faire tomber : un test qui ne
    /// peut pas echouer ne mesure rien.
    /// </summary>
    public sealed class TradingSvmModelConfigTests
    {
        /// <summary>
        /// XOR : quatre paquets aux coins, classe 1 sur une diagonale, classe 0 sur
        /// l'autre. Aucun hyperplan ne les separe — c'est precisement le probleme que
        /// l'astuce du noyau resout, et le cas degenere que Prong B interdit d'eviter.
        /// </summary>
        private static List<TradingTrainingSample> BuildXorSamples()
        {
            var samples = new List<TradingTrainingSample>();
            var offsets = new[] { -0.06, -0.02, 0.02, 0.06 };
            foreach (var dx in offsets)
            {
                foreach (var dy in offsets)
                {
                    samples.Add(BuildSample(0.0 + dx, 0.0 + dy, 0));
                    samples.Add(BuildSample(1.0 + dx, 1.0 + dy, 0));
                    samples.Add(BuildSample(0.0 + dx, 1.0 + dy, 1));
                    samples.Add(BuildSample(1.0 + dx, 0.0 + dy, 1));
                }
            }
            return samples;
        }

        private static TradingTrainingSample BuildSample(double x, double y, int label)
        {
            return new TradingTrainingSample
            {
                Inputs = new List<double> { x, y },
                Output = label
            };
        }

        /// <summary>
        /// Bruit deterministe et portable. Volontairement PAS System.Random : son
        /// algorithme n'est pas garanti stable d'une version de runtime a l'autre, et un
        /// test de calibration doit rendre le meme nombre demain.
        /// </summary>
        private static double Jitter(int i, int salt, double spread)
        {
            unchecked
            {
                uint h = (uint)(i * 2654435761u + salt * 40503u);
                h ^= h >> 13; h *= 2246822519u; h ^= h >> 16;
                return ((h % 1000) / 1000.0 - 0.5) * spread;
            }
        }

        /// <summary>
        /// XOR aux paquets ELARGIS jusqu'au chevauchement (spread 1.1). C'est la seule
        /// famille sur laquelle la calibration a quelque chose a calibrer : sur un XOR
        /// net, mesure, la complexite d'amorce 0.0001 classe deja parfaitement, donc la
        /// conserver est le bon resultat — et une garde posee la-dessus serait aveugle.
        /// </summary>
        private static List<TradingTrainingSample> BuildOverlappingXorSamples()
        {
            var samples = new List<TradingTrainingSample>();
            const double spread = 1.1;
            for (int i = 0; i < 30; i++)
            {
                void Add(double cx, double cy, int label, int salt)
                {
                    samples.Add(BuildSample(cx + Jitter(i, salt, spread), cy + Jitter(i, salt + 1, spread), label));
                }
                Add(0, 0, 0, 1); Add(1, 1, 0, 3); Add(0, 1, 1, 5); Add(1, 0, 1, 7);
            }
            return samples;
        }

        private static TradingTrainTestData BuildOverlappingXorData()
        {
            var samples = BuildOverlappingXorSamples();
            return new TradingTrainTestData(samples.Count, samples.Count)
            {
                Training = samples,
                Test = samples
            };
        }

        private static MulticlassSupportVectorMachine<IKernel> Learn(IKernel kernel, double complexity, double[][] x, int[] y)
        {
            var teacher = new MulticlassSupportVectorLearning<IKernel>()
            {
                Learner = (p) => new SequentialMinimalOptimization<IKernel>()
                {
                    Complexity = complexity,
                    UseKernelEstimation = true,
                    Kernel = kernel
                }
            };
            return teacher.Learn(x, y);
        }

        /// <summary>
        /// Le port entraine un vrai SVM a noyau : sur XOR, l'InverseMultiquadric du
        /// fork atteint 0 erreur, et le modele est consommable via l'enveloppe
        /// ITradingModel portee (ClassifierTradingModel.Predict).
        /// </summary>
        [Fact]
        public void SvmTradingModel_LearnsXorAndPredictsThroughTradingModelWrapper()
        {
            var config = new TradingSvmModelConfig();
            var samples = BuildXorSamples();
            var x = samples.GetInputMatrix();
            var y = samples.GetOutputClasses();

            var machine = Learn(config.GetKernel(KnownKernel.InverseMultiquadric), 1.0, x, y);

            Assert.Equal(0.0, GeneralConfusionMatrix.Estimate(machine, x, y).Error, 10);

            // L'enveloppe portee doit rendre les memes decisions, echantillon par echantillon.
            var model = new SvmTradingModel { Svm = machine };
            var predicted = model.Predict(samples);

            Assert.Equal(samples.Count, predicted.Count);
            for (int i = 0; i < samples.Count; i++)
            {
                Assert.Equal(samples[i].Output, predicted[i].Output);
            }
        }

        /// <summary>
        /// MUTATION DE CONTROLE du test precedent : meme donnees, meme pipeline, meme
        /// complexite — seul le noyau change (Linear). XOR n'etant pas lineairement
        /// separable, l'erreur DOIT etre non nulle. Sans ce negatif, le test ci-dessus
        /// serait compatible avec un probleme trivial ou n'importe quoi passe.
        /// </summary>
        [Fact]
        public void LinearKernel_FailsOnXor_ProvingTheKernelIsWhatCarriesTheResult()
        {
            var samples = BuildXorSamples();
            var x = samples.GetInputMatrix();
            var y = samples.GetOutputClasses();

            var machine = Learn(new Linear(), 1.0, x, y);

            Assert.True(
                GeneralConfusionMatrix.Estimate(machine, x, y).Error > 0.0,
                "Un noyau lineaire ne peut pas separer XOR : une erreur nulle signalerait un probleme degenere.");
        }

        /// <summary>
        /// GetKernel est la surface de substitution du port : chaque membre de
        /// KnownKernel doit rendre le noyau Accord correspondant, et un membre hors
        /// domaine doit lever plutot que retomber silencieusement sur un defaut.
        /// </summary>
        [Fact]
        public void GetKernel_MapsEveryKnownKernelMemberToItsAccordCounterpart()
        {
            var config = new TradingSvmModelConfig();

            Assert.IsType<InverseMultiquadric>(config.GetKernel(KnownKernel.InverseMultiquadric));
            Assert.IsType<NormalizedPolynomial>(config.GetKernel(KnownKernel.NormalizedPolynomial3));
            Assert.IsType<Polynomial>(config.GetKernel(KnownKernel.Polynomial3));
            Assert.IsType<TStudent>(config.GetKernel(KnownKernel.TStudent2));

            // Tous les membres declares sont couverts : si quelqu'un en ajoute un sans
            // etendre GetKernel, ce compte tombe et le test le dit.
            Assert.Equal(4, Enum.GetValues(typeof(KnownKernel)).Length);

            Assert.Throws<ApplicationException>(() => config.GetKernel((KnownKernel)999));
        }

        /// <summary>
        /// Les degres passes aux noyaux parametres sont ceux que le NOM du membre
        /// annonce. Une inversion Polynomial(3)/TStudent(2) serait invisible au test
        /// de type ci-dessus.
        /// </summary>
        [Fact]
        public void GetKernel_UsesTheDegreeAnnouncedByTheMemberName()
        {
            var config = new TradingSvmModelConfig();

            Assert.Equal(3, ((Polynomial)config.GetKernel(KnownKernel.Polynomial3)).Degree);
            Assert.Equal(3, ((NormalizedPolynomial)config.GetKernel(KnownKernel.NormalizedPolynomial3)).Degree);
            Assert.Equal(2, ((TStudent)config.GetKernel(KnownKernel.TStudent2)).Degree);
        }

        /// <summary>
        /// L'ordre des membres de KnownKernel est celui deja committe en tranche 3, PAS
        /// celui de l'upstream (qui place TStudent2 en 2e position). Ce test epingle les
        /// valeurs entieres : les reordonner casserait toute config deja serialisee, et
        /// le ferait silencieusement. Ecart delibere 2, cf en-tete de TradingSvmModelConfig.
        /// </summary>
        [Fact]
        public void KnownKernel_OrdinalsArePinned_BecauseTheyAreSerialised()
        {
            Assert.Equal(0, (int)KnownKernel.InverseMultiquadric);
            Assert.Equal(1, (int)KnownKernel.NormalizedPolynomial3);
            Assert.Equal(2, (int)KnownKernel.Polynomial3);
            Assert.Equal(3, (int)KnownKernel.TStudent2);
        }

        /// <summary>
        /// GARDE DE REGRESSION DE L'ECART 3. Le corps upstream de CalibrateComplexity
        /// remplacait `teacher` dans le bloc sous limite de temps sans jamais appeler
        /// Learn : `machine` restait null, la NRE suivante etait avalee, testError ne
        /// bougeait jamais de double.MaxValue, et la methode renvoyait TOUJOURS sa
        /// valeur initiale 0.0001 — sous un log affirmant « SVM complexity calibrated ».
        ///
        /// La garde est posee sur des donnees ou elle DISCRIMINE, ce qui a ete mesure et
        /// non suppose : sur ce jeu, le corps repare rend 706.88 et le corps upstream
        /// 0.0001 ; sur un XOR net les deux rendent 0.0001 et la garde ne prouverait
        /// rien. Un controle qu'on n'a pas vu echouer ne controle pas.
        /// </summary>
        [Fact]
        public void CalibrateComplexity_ActuallyExploresAndDoesNotReturnItsSeedValue()
        {
            var config = new TradingSvmModelConfig();

            var complexity = config.CalibrateComplexity(
                BuildOverlappingXorData(), config.GetKernel(KnownKernel.InverseMultiquadric));

            Assert.True(
                complexity > 0.0001,
                $"CalibrateComplexity a rendu {complexity}, sa valeur d'amorce : le bloc d'entrainement n'a pas tourne (defaut upstream, ecart 3).");
        }

        /// <summary>
        /// La calibration doit AMELIORER ce qu'elle optimise. Le score de
        /// TradingModelConfig.TestModel (bad - good, plus bas = meilleur) doit etre
        /// strictement meilleur a la complexite calibree qu'a la complexite d'amorce —
        /// sans quoi la boucle explorerait sans jamais choisir.
        /// </summary>
        [Fact]
        public void CalibratedComplexity_ScoresBetterThanTheSeedComplexity()
        {
            var config = new TradingSvmModelConfig();
            var data = BuildOverlappingXorData();
            var x = data.Training.GetInputMatrix();
            var y = data.Training.GetOutputClasses();
            var kernel = config.GetKernel(KnownKernel.InverseMultiquadric);

            var calibrated = config.CalibrateComplexity(data, kernel);

            double seedScore = TradingModelConfig.TestModel(
                data, new ClassifierTradingModel { Classifier = Learn(kernel, 0.0001, x, y) });
            double calibratedScore = TradingModelConfig.TestModel(
                data, new ClassifierTradingModel { Classifier = Learn(kernel, calibrated, x, y) });

            Assert.True(
                calibratedScore < seedScore,
                $"score calibre {calibratedScore} vs amorce {seedScore} : la calibration n'a rien ameliore.");
        }
    }
}
