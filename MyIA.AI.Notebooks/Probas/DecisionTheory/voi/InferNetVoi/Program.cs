// Adaptateur Infer.NET du contrat JSON VoI (tranche 3/3 #13569).
// Extraction fidele de DecInfer-6 : combinateur generique cellule 32 +
// inference bayesienne reelle cellule 35, generalisee a chaque signal.
// Les posterieurs P(etat|signal) ET les marginales P(signal) sortent de
// InferenceEngine (Microsoft.ML.Probabilistic), jamais de Bayes a la main.

using System.Text.Json;
using Microsoft.ML.Probabilistic.Distributions;
using Microsoft.ML.Probabilistic.Models;

public class ProblemSpec
{
    public string problem { get; set; }
    public string[] states { get; set; }
    public Dictionary<string, double> priors { get; set; }
    public string[] actions { get; set; }
    public Dictionary<string, Dictionary<string, double>> utilities { get; set; }
    public string[] signals { get; set; }
    public Dictionary<string, Dictionary<string, double>> likelihood { get; set; }
    public double test_cost { get; set; }
}

public class EngineOutput
{
    public string engine { get; set; }
    public string problem { get; set; }
    public double eu_no_info { get; set; }
    public string action_no_info { get; set; }
    public double evpi { get; set; }
    public double evsi_brute { get; set; }
    public double evsi_nette { get; set; }
    public string decision { get; set; }
    public Dictionary<string, double> signal_marginals { get; set; }
    public Dictionary<string, Dictionary<string, double>> posteriors { get; set; }
}

public static class Program
{
    public static int Main(string[] args)
    {
        if (args.Length < 2)
        {
            Console.Error.WriteLine("usage: InferNetVoi <problem.json> <output.json>");
            return 2;
        }
        var spec = JsonSerializer.Deserialize<ProblemSpec>(
            File.ReadAllText(args[0]),
            new JsonSerializerOptions { PropertyNameCaseInsensitive = true });
        if (spec.states.Length != 2 || spec.signals.Length != 2)
        {
            Console.Error.WriteLine("contrat binaire : 2 etats x 2 signaux (cf problems/*.json)");
            return 2;
        }

        // --- Modele generatif Infer.NET (pattern cellule 35, generalise) ---
        string s1 = spec.states[0], s0 = spec.states[1];
        double p1 = spec.priors[s1];
        string sig1 = spec.signals[0], sig0 = spec.signals[1];
        double lik11 = spec.likelihood[sig1][s1], lik10 = spec.likelihood[sig1][s0];

        Variable<bool> etat = Variable.Bernoulli(p1).Named("etat");
        Variable<bool> signal = Variable.New<bool>().Named("signal");
        using (Variable.If(etat))
            signal.SetTo(Variable.Bernoulli(lik11));
        using (Variable.IfNot(etat))
            signal.SetTo(Variable.Bernoulli(lik10));

        var engine = new InferenceEngine();
        engine.Compiler.CompilerChoice =
            Microsoft.ML.Probabilistic.Compiler.CompilerChoice.Roslyn;

        // Marginales du signal : inference AVANT toute observation.
        Bernoulli marg = engine.Infer<Bernoulli>(signal);
        var signalMarginals = new Dictionary<string, double>
        {
            [sig1] = marg.GetProbTrue(),
            [sig0] = 1.0 - marg.GetProbTrue()
        };

        // Posterieurs : observer chaque signal, inferer l'etat (cellule 35).
        var posteriors = new Dictionary<string, Dictionary<string, double>>();
        foreach (var (name, observed) in new[] { (sig1, true), (sig0, false) })
        {
            signal.ObservedValue = observed;
            Bernoulli post = engine.Infer<Bernoulli>(etat);
            posteriors[name] = new Dictionary<string, double>
            {
                [s1] = post.GetProbTrue(),
                [s0] = 1.0 - post.GetProbTrue()
            };
        }
        signal.ClearObservedValue();

        // --- Combinateur VoI (cellule 32), alimente par les quantites Infer.NET ---
        double EuAction(string a, Dictionary<string, double> belief) =>
            spec.states.Sum(st => belief[st] * spec.utilities[a][st]);

        var prior = spec.priors;
        double euNoInfo = double.NegativeInfinity;
        string bestAction = null;
        foreach (var a in spec.actions)
        {
            double eu = EuAction(a, prior);
            if (eu > euNoInfo) { euNoInfo = eu; bestAction = a; }
        }

        double euPerfect = spec.states.Sum(st => prior[st] *
            spec.actions.Max(a => spec.utilities[a][st]));
        double evpi = euPerfect - euNoInfo;

        double euAvecInfo = spec.signals.Sum(sig => signalMarginals[sig] *
            spec.actions.Max(a => EuAction(a, posteriors[sig])));
        double evsiBrute = euAvecInfo - euNoInfo;
        double evsiNette = evsiBrute - spec.test_cost;

        var output = new EngineOutput
        {
            engine = "infer-net",
            problem = spec.problem,
            eu_no_info = euNoInfo,
            action_no_info = bestAction,
            evpi = evpi,
            evsi_brute = evsiBrute,
            evsi_nette = evsiNette,
            decision = evsiNette > 0 ? "observer" : "agir_sans_test",
            signal_marginals = signalMarginals,
            posteriors = posteriors
        };

        var opts = new JsonSerializerOptions { WriteIndented = true };
        File.WriteAllText(args[1], JsonSerializer.Serialize(output, opts));
        Console.WriteLine($"infer-net | {spec.problem} | EU={euNoInfo:F0} ({bestAction}) " +
                          $"EVPI={evpi:F0} EVSI_brute={evsiBrute:F0} EVSI_nette={evsiNette:F0} " +
                          $"decision={output.decision}");
        return 0;
    }
}
