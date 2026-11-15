using MyIA.AI.Shared.Search.Probability;
using Xunit;

namespace MyIA.AI.Shared.Tests.Search.Probability;

/// <summary>
/// Verifications du bloc temporel (EPIC #7265, B2 tranche 2a, issue #21909).
/// </summary>
/// <remarks>
/// Le modele de reference est le monde des parapluies d'AIMA (ch. 15) : deux etats
/// caches (pluie / soleil), deux observations (parapluie porte / non porte) :
/// <c>P(R_0) = 0.5</c>, <c>P(R_t | R_{t-1}) = 0.7</c>, <c>P(U_t | R_t) = 0.9</c>,
/// <c>P(U_t | S_t) = 0.2</c>. Ses valeurs sont calculables a la main, ce qui fait
/// du test une verification et non une simple capture de comportement.
/// </remarks>
public sealed class TemporalModelsTests
{
    private const int Umbrella = 0;
    private const int NoUmbrella = 1;

    private static HiddenMarkovModel Rain() => new(
        transition: new[,]
        {
            { 0.7, 0.3 },
            { 0.3, 0.7 },
        },
        sensor: new[,]
        {
            { 0.9, 0.2 },
            { 0.1, 0.8 },
        },
        prior: [0.5, 0.5]);

    private static void AssertDistribution(double[] actual, double[] expected, double tolerance = 1e-4)
    {
        Assert.Equal(expected.Length, actual.Length);
        Assert.Equal(1.0, actual.Sum(), 6);
        for (int i = 0; i < expected.Length; i++)
            Assert.Equal(expected[i], actual[i], tolerance);
    }

    [Fact]
    public void Filter_SurDeuxObservations_RendLaDistributionAttendue()
    {
        double[] filtered = Rain().Filter([Umbrella, Umbrella]);

        // f_1 = [9/11, 2/11] puis f_2 = [0.621/0.703, 0.082/0.703]
        AssertDistribution(filtered, [6.21 / 7.03, 0.82 / 7.03]);
    }

    [Fact]
    public void ForwardMessages_CommencentParLaLoiAPriori()
    {
        double[][] messages = Rain().ForwardMessages([Umbrella, NoUmbrella]);

        Assert.Equal(3, messages.Length);
        AssertDistribution(messages[0], [0.5, 0.5]);
        AssertDistribution(messages[1], [9.0 / 11.0, 2.0 / 11.0]);
    }

    [Fact]
    public void BackwardMessages_SontDesDistributionsEtFinissentUniformes()
    {
        HiddenMarkovModel model = Rain();
        double[][] backward = model.BackwardMessages([Umbrella, Umbrella]);

        AssertDistribution(backward[^1], [0.5, 0.5]);
        foreach (double[] message in backward)
            Assert.Equal(1.0, message.Sum(), 6);
    }

    [Fact]
    public void Smooth_CoincideAvecLEnumerationExhaustive()
    {
        HiddenMarkovModel model = Rain();
        int[] evidence = [Umbrella, Umbrella, NoUmbrella];

        double[][] smoothed = model.Smooth(evidence);

        // Oracle independant : la marginale exacte, obtenue en enumerant les
        // 2^4 trajectoires possibles. Il ne partage aucune ligne de calcul avec
        // l'algorithme forward-backward qu'il verifie.
        for (int step = 0; step <= evidence.Length; step++)
            AssertDistribution(smoothed[step], MarginalByEnumeration(model, evidence, step), 1e-9);
    }

    [Fact]
    public void Smooth_UtiliseLesObservationsPosterieures()
    {
        HiddenMarkovModel model = Rain();
        int[] evidence = [Umbrella, Umbrella];

        double[] filtered = model.Filter(evidence);
        double[] smoothedAtOrigin = model.Smooth(evidence)[0];

        // A l'origine, le lissage voit deux observations quand le filtrage n'en voit
        // qu'une : les deux estimations divergent, c'est tout l'objet du lissage.
        Assert.NotEqual(filtered[0], smoothedAtOrigin[0], 6);
        AssertDistribution(smoothedAtOrigin, MarginalByEnumeration(model, evidence, 0), 1e-9);
    }

    /// <summary>
    /// Marginale exacte <c>P(X_time | e_{1:t})</c> par enumeration de toutes les
    /// trajectoires d'etats — oracle volontairement naif, sans message ni normalisation
    /// intermediaire, pour que le test du lissage ne se verifie pas lui-meme.
    /// </summary>
    private static double[] MarginalByEnumeration(HiddenMarkovModel model, int[] evidence, int time)
    {
        int states = model.StateCount;
        double[] prior = model.Prior;
        double[,] transition = model.Transition;
        double[,] sensor = model.Sensor;
        var marginal = new double[states];
        var path = new int[evidence.Length + 1];

        void Walk(int step, double weight)
        {
            if (step == evidence.Length + 1)
            {
                marginal[path[time]] += weight;
                return;
            }

            for (int state = 0; state < states; state++)
            {
                path[step] = state;
                double next = step == 0
                    ? weight * prior[state]
                    : weight * transition[path[step - 1], state] * sensor[evidence[step - 1], state];
                Walk(step + 1, next);
            }
        }

        Walk(0, 1.0);

        double total = marginal.Sum();
        return marginal.Select(value => value / total).ToArray();
    }

    [Fact]
    public void FixedLagSmooth_AuDernierPas_CoincideAvecLeLissageComplet()
    {
        HiddenMarkovModel model = Rain();
        int[] evidence = [Umbrella, Umbrella, NoUmbrella, Umbrella];
        const int lag = 2;

        double[][] smoothed = model.Smooth(evidence);
        double[] lagged = model.FixedLagSmooth(evidence, lag)[^1];

        // Au pas courant, la fenetre de retard couvre tout le futur disponible :
        // l'estimation en ligne vaut alors le lissage hors ligne.
        AssertDistribution(lagged, smoothed[evidence.Length - lag], 1e-9);
    }

    [Fact]
    public void FixedLagSmooth_NUtiliseQueLeFuturDeLaFenetre()
    {
        HiddenMarkovModel model = Rain();
        int[] evidence = [Umbrella, Umbrella, NoUmbrella];
        const int lag = 2;

        // Le premier resultat estime X_0 avec e_{1:2} seulement : il doit valoir le
        // lissage du prefixe de longueur `lag`, donc ignorer l'observation 3.
        double[] premier = model.FixedLagSmooth(evidence, lag)[0];
        double[] prefixe = model.Smooth(evidence[..lag])[0];

        AssertDistribution(premier, prefixe, 1e-9);
    }

    [Fact]
    public void FixedLagSmooth_SansAssezDObservations_NeRendRien()
    {
        double[][] lagged = Rain().FixedLagSmooth([Umbrella], 3);

        Assert.Empty(lagged);
    }

    [Fact]
    public void Constructeur_RefuseUneTransitionQuiNeSommePasAUn()
    {
        var transition = new[,]
        {
            { 0.7, 0.4 },
            { 0.3, 0.7 },
        };

        var error = Assert.Throws<ArgumentException>(() => new HiddenMarkovModel(
            transition,
            new[,] { { 0.9, 0.2 }, { 0.1, 0.8 } },
            [0.5, 0.5]));

        Assert.Contains("ne somme pas a 1", error.Message);
    }

    [Fact]
    public void Filter_SurUneObservationImpossible_LevePlutotQueDeRendreUneDistributionArbitraire()
    {
        var model = new HiddenMarkovModel(
            new[,] { { 1.0, 0.0 }, { 0.0, 1.0 } },
            new[,] { { 1.0, 0.0 }, { 0.0, 1.0 } },
            [1.0, 0.0]);

        // L'etat initial est 0 avec certitude ; l'observation 1 y est impossible.
        Assert.Throws<InvalidOperationException>(() => model.Filter([1]));
    }

    [Fact]
    public void ParticleFilter_ApprocheLeFiltrageExact()
    {
        HiddenMarkovModel model = Rain();
        int[] evidence = [Umbrella, Umbrella, Umbrella, NoUmbrella, Umbrella];

        double[] exact = model.Filter(evidence);
        var filter = new ParticleFilter(model, particleCount: 20000, seed: 42);
        foreach (int observation in evidence)
            filter.Update(observation);

        AssertDistribution(filter.Distribution(), exact, tolerance: 0.03);
    }

    [Fact]
    public void ParticleFilter_EstReproductibleALaGraine()
    {
        HiddenMarkovModel model = Rain();
        var first = new ParticleFilter(model, particleCount: 500, seed: 7);
        var second = new ParticleFilter(model, particleCount: 500, seed: 7);

        foreach (var filter in new[] { first, second })
        {
            filter.Update(Umbrella);
            filter.Update(NoUmbrella);
            filter.Update(Umbrella);
        }

        Assert.Equal(first.States, second.States);
        AssertDistribution(first.Distribution(), second.Distribution(), 1e-12);
    }

    [Fact]
    public void ParticleFilter_ReechantillonneQuandLaMasseEffectiveSEffondre()
    {
        HiddenMarkovModel model = Rain();
        var filter = new ParticleFilter(model, particleCount: 1000, seed: 3);
        int[] evidence = Enumerable.Repeat(Umbrella, 12).ToArray();

        // Des parapluies repetes concentrent la masse : l'ESS doit rester sain
        // parce que le reechantillonnage le remonte, jamais s'effondrer a zero.
        foreach (int observation in evidence)
        {
            filter.Update(observation);
            Assert.True(filter.EffectiveSampleSize > 0);
        }

        // Le filtrage converge vers une probabilite de pluie inferieure a 1
        // (la vraisemblance n'est pas deterministe) : on compare a l'exact.
        AssertDistribution(filter.Distribution(), model.Filter(evidence), tolerance: 0.05);
    }
}
