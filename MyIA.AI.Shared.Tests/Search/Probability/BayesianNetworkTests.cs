using System;
using System.Collections.Generic;
using System.Linq;
using MyIA.AI.Shared.Search.Probability;
using Xunit;

namespace MyIA.AI.Shared.Tests.Search.Probability;

/// <summary>
/// Tests du reseau bayesien discret, sur le monde des cambriolages d'AIMA (ch. 13).
/// </summary>
/// <remarks>
/// Les valeurs attendues ne sont pas recopiees d'un tableau : elles sont recalculees ici par
/// une somme en chaine ecrite a la main (constantes explicites, deux boucles imbriquees), qui
/// n'emprunte ni l'enumeration ni les tables du reseau. Un test qui appellerait le reseau pour
/// connaitre sa propre reponse ne prouverait rien.
/// </remarks>
public sealed class BayesianNetworkTests
{
    private const string True = "true";
    private const string False = "false";

    private static readonly string[] Binary = { True, False };

    private static BayesianNetwork Burglary()
    {
        return new BayesianNetwork(new[]
        {
            new BayesianNetwork.Node("Cambriolage", Binary, Array.Empty<string>(), new[] { 0.001, 0.999 }),
            new BayesianNetwork.Node("Seisme", Binary, Array.Empty<string>(), new[] { 0.002, 0.998 }),
            new BayesianNetwork.Node(
                "Alarme",
                Binary,
                new[] { "Cambriolage", "Seisme" },
                new[]
                {
                    0.95, 0.05,   // cambriolage = vrai, seisme = vrai
                    0.94, 0.06,   // cambriolage = vrai, seisme = faux
                    0.29, 0.71,   // cambriolage = faux, seisme = vrai
                    0.001, 0.999, // cambriolage = faux, seisme = faux
                }),
            new BayesianNetwork.Node(
                "JeanAppelle",
                Binary,
                new[] { "Alarme" },
                new[] { 0.90, 0.10, 0.05, 0.95 }),
            new BayesianNetwork.Node(
                "MarieAppelle",
                Binary,
                new[] { "Alarme" },
                new[] { 0.70, 0.30, 0.01, 0.99 }),
        });
    }

    [Fact]
    public void Joint_SurToutesLesAffectations_SommeAUn()
    {
        BayesianNetwork network = Burglary();
        double total = 0;

        foreach (Dictionary<string, string> assignment in AllAssignments(network))
        {
            total += network.JointProbability(assignment);
        }

        Assert.True(Math.Abs(total - 1.0) < 1e-9, $"la loi jointe somme a {total} au lieu de 1");
    }

    [Fact]
    public void Posterior_SurLesDeuxAppels_CoincideAvecLaSommeEnChaine()
    {
        BayesianNetwork network = Burglary();
        var evidence = new Dictionary<string, string>
        {
            ["JeanAppelle"] = True,
            ["MarieAppelle"] = True,
        };

        double[] posterior = network.Posterior(network.IndexOf("Cambriolage"), evidence);
        double expected = ProbabilityOfBurglaryGiven(true, true, true);

        AssertDistribution(new[] { expected, 1 - expected }, posterior, 1e-9);
        // Valeur publiee par AIMA (ch. 13, exemple du cambriolage) : <0.284, 0.716>.
        Assert.Equal(0.284, posterior[0], 3);
    }

    [Fact]
    public void Posterior_SurUnSeulAppel_CoincideAvecLaSommeEnChaine()
    {
        BayesianNetwork network = Burglary();
        var evidence = new Dictionary<string, string> { ["JeanAppelle"] = True };

        double[] posterior = network.Posterior(network.IndexOf("Cambriolage"), evidence);
        // Marie n'est pas observee : elle est marginalisee, pas mise a « n'appelle pas ».
        double expected = ProbabilityOfBurglaryGiven(true, true, null);

        AssertDistribution(new[] { expected, 1 - expected }, posterior, 1e-9);
        Assert.Equal(0.016, posterior[0], 3);
    }

    [Fact]
    public void Posterior_SansEvidence_RendLaLoiAPriori()
    {
        BayesianNetwork network = Burglary();

        double[] posterior = network.Posterior(
            network.IndexOf("Cambriolage"),
            new Dictionary<string, string>());

        AssertDistribution(new[] { 0.001, 0.999 }, posterior, 1e-12);
    }

    [Fact]
    public void Posterior_SurUneVariableTerminale_RendLeConditionnementCalculeAMain()
    {
        BayesianNetwork network = Burglary();
        var evidence = new Dictionary<string, string> { ["Cambriolage"] = True };

        double[] posterior = network.Posterior(network.IndexOf("JeanAppelle"), evidence);

        // P(jean | cambriolage) = somme sur le seisme de P(seisme) x [ P(alarme | b, seisme) x 0.90
        //                                                              + (1 - P(alarme | b, seisme)) x 0.05 ].
        double alarmeVraiSeismeVrai = 0.95;
        double alarmeVraiSeismeFaux = 0.94;
        double expected = (0.002 * ((alarmeVraiSeismeVrai * 0.90) + ((1 - alarmeVraiSeismeVrai) * 0.05)))
                        + (0.998 * ((alarmeVraiSeismeFaux * 0.90) + ((1 - alarmeVraiSeismeFaux) * 0.05)));
        AssertDistribution(new[] { expected, 1 - expected }, posterior, 1e-12);
    }

    [Fact]
    public void Posterior_RefuseUneEvidenceSansAucuneAffectationCoherente()
    {
        var network = new BayesianNetwork(new[]
        {
            new BayesianNetwork.Node("Cause", Binary, Array.Empty<string>(), new[] { 1.0, 0.0 }),
            new BayesianNetwork.Node(
                "Effet",
                Binary,
                new[] { "Cause" },
                new[]
                {
                    1.0, 0.0, // cause = vrai  -> effet = vrai, certainement
                    0.0, 1.0, // cause = faux  -> effet = vrai, jamais
                }),
        });

        var evidence = new Dictionary<string, string>
        {
            ["Cause"] = False,
            ["Effet"] = True,
        };

        InvalidOperationException error = Assert.Throws<InvalidOperationException>(
            () => network.Posterior(network.IndexOf("Cause"), evidence));

        Assert.Contains("probabilite est nulle", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void Joint_RefuseUneAffectationIncomplete()
    {
        BayesianNetwork network = Burglary();
        var partial = new Dictionary<string, string> { ["Cambriolage"] = True };

        ArgumentException error = Assert.Throws<ArgumentException>(() => network.JointProbability(partial));

        Assert.Contains("affectation complete", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void Posterior_RefuseUneValeurHorsDomaine()
    {
        BayesianNetwork network = Burglary();
        var evidence = new Dictionary<string, string> { ["Cambriolage"] = "peut-etre" };

        ArgumentException error = Assert.Throws<ArgumentException>(
            () => network.Posterior(network.IndexOf("Alarme"), evidence));

        Assert.Contains("n'appartient pas au domaine", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void Constructeur_RefuseUneTableQuiNeSommePasAUn()
    {
        ArgumentException error = Assert.Throws<ArgumentException>(() => new BayesianNetwork(new[]
        {
            new BayesianNetwork.Node("Cambriolage", Binary, Array.Empty<string>(), new[] { 0.4, 0.4 }),
        }));

        Assert.Contains("ne somme pas a 1", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void Constructeur_RefuseUnParentDeclareApresSonEnfant()
    {
        ArgumentException error = Assert.Throws<ArgumentException>(() => new BayesianNetwork(new[]
        {
            new BayesianNetwork.Node(
                "Alarme",
                Binary,
                new[] { "Cambriolage" },
                new[] { 0.95, 0.05, 0.29, 0.71 }),
            new BayesianNetwork.Node("Cambriolage", Binary, Array.Empty<string>(), new[] { 0.001, 0.999 }),
        }));

        Assert.Contains("n'est pas declare avant elle", error.Message, StringComparison.Ordinal);
    }

    /// <summary>
    /// Somme en chaine ecrite a la main : P(C | jean, marie) pour le monde des cambriolages.
    /// Deux boucles imbriquees sur le seisme puis l'alarme, avec les constantes du modele
    /// recopiees depuis l'enonce — aucune lecture des tables du reseau.
    /// </summary>
    /// <remarks>
    /// La boucle rend une <b>masse jointe</b> P(c, ...), pas encore une posterior : la
    /// normalisation sur les deux valeurs de C est faite au retour, sans quoi la valeur rendue
    /// serait la probabilite jointe (~0,00059 pour les deux appels), pas le 0,284 publie par AIMA.
    ///
    /// Un appelant <c>null</c> signifie « non observe » : sa variable est marginalisee, comme le
    /// fait l'enumeration. C'est le point ou un oracle ecrit a la main se trompe le plus
    /// facilement — conditionner sur <c>marie = faux</c> n'est pas marginaliser <c>marie</c>.
    /// </remarks>
    private static double ProbabilityOfBurglaryGiven(bool burglar, bool? jeanCalls, bool? maryCalls)
    {
        double withBurglary = JointMass(true, jeanCalls, maryCalls);
        double withoutBurglary = JointMass(false, jeanCalls, maryCalls);
        return burglar
            ? withBurglary / (withBurglary + withoutBurglary)
            : withoutBurglary / (withBurglary + withoutBurglary);
    }

    private static double JointMass(bool burglar, bool? jeanCalls, bool? maryCalls)
    {
        double[] seismes = { 0.002, 0.998 };                            // vrai, faux
        double[,] alarmeSachant = { { 0.95, 0.94 }, { 0.29, 0.001 } };   // [cambriolage][seisme]
        double[] jeanSachantAlarme = { 0.90, 0.05 };
        double[] marieSachantAlarme = { 0.70, 0.01 };
        double[] cambriolages = { 0.001, 0.999 };

        int b = burglar ? 0 : 1;
        double mass = 0;

        for (int e = 0; e < 2; e++)
        {
            for (int a = 0; a < 2; a++)
            {
                // Le terme d'alarme depend de a : c'est P(alarme = a | cambriolage, seisme),
                // et non P(alarme = vrai | ...) pour les deux branches.
                double p = cambriolages[b] * seismes[e] * (a == 0 ? alarmeSachant[b, e] : 1 - alarmeSachant[b, e]);

                if (jeanCalls is bool jean)
                {
                    p *= jean
                        ? (a == 0 ? jeanSachantAlarme[0] : jeanSachantAlarme[1])
                        : (a == 0 ? 1 - jeanSachantAlarme[0] : 1 - jeanSachantAlarme[1]);
                }

                if (maryCalls is bool mary)
                {
                    p *= mary
                        ? (a == 0 ? marieSachantAlarme[0] : marieSachantAlarme[1])
                        : (a == 0 ? 1 - marieSachantAlarme[0] : 1 - marieSachantAlarme[1]);
                }

                mass += p;
            }
        }

        return mass;
    }

    private static void AssertDistribution(double[] expected, double[] actual, double tolerance)
    {
        Assert.Equal(expected.Length, actual.Length);
        for (int index = 0; index < expected.Length; index++)
        {
            Assert.True(
                Math.Abs(expected[index] - actual[index]) <= tolerance,
                $"valeur {index} : attendu {expected[index]}, obtenu {actual[index]} (tolerance {tolerance})");
        }
    }

    private static IEnumerable<Dictionary<string, string>> AllAssignments(BayesianNetwork network)
    {
        return Walk(0, new Dictionary<string, string>(StringComparer.Ordinal));

        IEnumerable<Dictionary<string, string>> Walk(int node, Dictionary<string, string> current)
        {
            if (node == network.NodeCount)
            {
                yield return new Dictionary<string, string>(current, StringComparer.Ordinal);
                yield break;
            }

            string name = network.NameOf(node);
            foreach (string value in network.DomainOf(node))
            {
                current[name] = value;
                foreach (Dictionary<string, string> assignment in Walk(node + 1, current))
                {
                    yield return assignment;
                }
            }

            current.Remove(name);
        }
    }
}
