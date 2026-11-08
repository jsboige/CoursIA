namespace MyIA.AI.Shared.Search.Probability;

/// <summary>
/// Modele temporel probabiliste : chaine de Markov cachee (HMM) discrete, avec
/// filtrage avant, lissage forward-backward et lissage a retard fixe.
/// </summary>
/// <remarks>
/// Port du bloc temporel du patrimoine Aricie (EPIC #7265, volet B2 tranche 2a,
/// issue #21909). Perimetre retenu par la decision user du 2026-11-02 (« 1a / 2a / 3a ») :
/// ne porter que ce que la serie Probas (Infer.NET) ne rend pas sous forme AIMA —
/// lissage forward-backward, lissage a retard fixe et filtrage particulaire
/// (voir <see cref="ParticleFilter"/>). Le bloc bayesien statique de
/// <c>Probability.cs</c>, lui, n'est pas repris : Infer.NET le couvre.
///
/// Conventions (AIMA ch. 14-15) :
/// <list type="bullet">
///   <item><description><c>Transition[i, j] = P(X_t = j | X_{t-1} = i)</c> — ligne = etat source, ligne somme a 1.</description></item>
///   <item><description><c>Sensor[k, j] = P(E_t = k | X_t = j)</c> — colonne = etat cache, chaque colonne represente une distribution sur les observations.</description></item>
///   <item><description><c>Prior[j] = P(X_0 = j)</c> — somme a 1.</description></item>
/// </list>
/// Les messages sont maintenus **normalises** : chaque distribution rendue somme a 1,
/// ce qui rend les trois algorithmes directement comparables entre eux et au filtre
/// particulaire. La vraisemblance de la sequence n'est donc pas rendue par ces
/// methodes (elle exigerait de conserver les facteurs de normalisation).
/// </remarks>
public sealed class HiddenMarkovModel
{
    private readonly double[,] _transition;
    private readonly double[,] _sensor;
    private readonly double[] _prior;

    /// <summary>Construit un HMM discret a partir de ses trois tables.</summary>
    /// <param name="transition">Matrice <c>[etat_source, etat_cible]</c>, chaque ligne somme a 1.</param>
    /// <param name="sensor">Matrice <c>[observation, etat_cache]</c>, chaque colonne somme a 1.</param>
    /// <param name="prior">Distribution initiale sur les etats caches, somme a 1.</param>
    /// <exception cref="ArgumentException">Une table n'est pas stochastique, ou les dimensions sont incoherentes.</exception>
    public HiddenMarkovModel(double[,] transition, double[,] sensor, double[] prior)
    {
        ArgumentNullException.ThrowIfNull(transition);
        ArgumentNullException.ThrowIfNull(sensor);
        ArgumentNullException.ThrowIfNull(prior);

        int states = prior.Length;
        if (states == 0)
            throw new ArgumentException("Le modele doit declarer au moins un etat cache.", nameof(prior));
        if (transition.GetLength(0) != states || transition.GetLength(1) != states)
            throw new ArgumentException(
                $"La transition doit etre {states}x{states} pour {states} etats caches.",
                nameof(transition));
        if (sensor.GetLength(1) != states)
            throw new ArgumentException(
                $"La matrice d'observation doit avoir {states} colonnes (une par etat cache).",
                nameof(sensor));
        if (sensor.GetLength(0) == 0)
            throw new ArgumentException("Le modele doit declarer au moins une observation.", nameof(sensor));

        RequireStochasticRows(transition, nameof(transition));
        RequireStochasticColumns(sensor, nameof(sensor));
        RequireDistribution(prior, nameof(prior));

        _transition = (double[,])transition.Clone();
        _sensor = (double[,])sensor.Clone();
        _prior = (double[])prior.Clone();
    }

    /// <summary>Nombre d'etats caches.</summary>
    public int StateCount => _prior.Length;

    /// <summary>Nombre d'observations possibles.</summary>
    public int EvidenceCount => _sensor.GetLength(0);

    /// <summary>Distribution initiale sur les etats caches (copie).</summary>
    public double[] Prior => (double[])_prior.Clone();

    /// <summary><c>P(X_t = j | X_{t-1} = i)</c>, copie de la table de transition.</summary>
    public double[,] Transition => (double[,])_transition.Clone();

    /// <summary><c>P(E_t = k | X_t = j)</c>, copie de la table d'observation.</summary>
    public double[,] Sensor => (double[,])_sensor.Clone();

    /// <summary>
    /// Filtrage avant : rend la distribution de l'etat cache apres avoir absorbe
    /// toute la sequence d'observations (<c>P(X_t | e_{1:t})</c>).
    /// </summary>
    /// <param name="evidence">Observations successives, dans l'ordre temporel.</param>
    public double[] Filter(IReadOnlyList<int> evidence)
    {
        ArgumentNullException.ThrowIfNull(evidence);
        double[] message = (double[])_prior.Clone();
        foreach (int observation in evidence)
            message = ForwardStep(message, observation);
        return message;
    }

    /// <summary>
    /// Messages avant <c>f_{1:k}</c> pour <c>k = 0..t</c>, le message d'indice 0 etant
    /// la distribution initiale (aucune observation absorbee).
    /// </summary>
    public double[][] ForwardMessages(IReadOnlyList<int> evidence)
    {
        ArgumentNullException.ThrowIfNull(evidence);
        var messages = new double[evidence.Count + 1][];
        messages[0] = (double[])_prior.Clone();
        for (int k = 0; k < evidence.Count; k++)
            messages[k + 1] = ForwardStep(messages[k], RequireObservation(evidence[k]));
        return messages;
    }

    /// <summary>
    /// Messages arriere <c>b_{k+1:t}</c> pour <c>k = 0..t</c> : le message d'indice
    /// <c>t</c> est uniforme (rien apres la derniere observation).
    /// </summary>
    /// <remarks>
    /// Contrairement au manuel AIMA, qui garde le message arriere non normalise,
    /// chaque message est normalise ici : le produit <c>f * b</c> du lissage reste
    /// exact (la normalisation finale l'absorbe), mais la vraisemblance
    /// <c>P(e_{k+1:t} | X_k)</c> n'est pas reconstructible depuis ces messages.
    /// </remarks>
    public double[][] BackwardMessages(IReadOnlyList<int> evidence)
    {
        ArgumentNullException.ThrowIfNull(evidence);
        int t = evidence.Count;
        var messages = new double[t + 1][];
        messages[t] = Uniform(_prior.Length);
        for (int k = t - 1; k >= 0; k--)
            messages[k] = BackwardStep(messages[k + 1], RequireObservation(evidence[k]));
        return messages;
    }

    /// <summary>
    /// Lissage forward-backward : <c>P(X_k | e_{1:t})</c> pour chaque pas de temps,
    /// en utilisant **toute** la sequence — y compris les observations posterieures.
    /// </summary>
    public double[][] Smooth(IReadOnlyList<int> evidence)
    {
        double[][] forward = ForwardMessages(evidence);
        double[][] backward = BackwardMessages(evidence);
        var smoothed = new double[evidence.Count + 1][];
        for (int k = 0; k <= evidence.Count; k++)
            smoothed[k] = Normalize(Product(forward[k], backward[k]), $"lissage au pas {k}");
        return smoothed;
    }

    /// <summary>
    /// Lissage a retard fixe : <c>P(X_{t-lag} | e_{1:t})</c> pour chaque pas, en ne
    /// gardant en memoire que la fenetre de retard demandee — c'est ce qui le rend
    /// utilisable en ligne, la ou <see cref="Smooth"/> exige la sequence entiere.
    /// </summary>
    /// <param name="evidence">Observations successives.</param>
    /// <param name="lag">Retard <c>L</c> : on rend l'etat vieux de <c>L</c> pas.</param>
    /// <returns>
    /// Pour chaque pas <c>t</c> a partir de <c>L</c>, la distribution de <c>X_{t-L}</c>.
    /// Les pas anterieurs a <c>L</c> sont omis : l'etat demande n'existe pas encore.
    /// </returns>
    public double[][] FixedLagSmooth(IReadOnlyList<int> evidence, int lag)
    {
        ArgumentNullException.ThrowIfNull(evidence);
        ArgumentOutOfRangeException.ThrowIfNegative(lag);
        if (lag == 0)
            return ForwardMessages(evidence).Skip(1).ToArray();

        int t = evidence.Count;
        if (t < lag)
            return [];

        // Le message avant est bon marche : on le garde pour toute la sequence.
        // Le message arriere, lui, ne remonte jamais plus loin que `lag` pas —
        // c'est ce qui borne le cout a O(t * lag) et la memoire a la fenetre.
        double[][] forward = ForwardMessages(evidence);
        var results = new List<double[]>(Math.Max(0, t - lag + 1));
        for (int k = lag; k <= t; k++)
        {
            double[] backward = Uniform(_prior.Length);
            for (int j = k - 1; j >= k - lag; j--)
                backward = BackwardStep(backward, RequireObservation(evidence[j]));
            results.Add(Normalize(Product(forward[k - lag], backward), $"lissage a retard fixe, pas {k - lag}"));
        }

        return results.ToArray();
    }

    private double[] ForwardStep(double[] previous, int observation)
    {
        var next = new double[_prior.Length];
        for (int j = 0; j < next.Length; j++)
        {
            double sum = 0;
            for (int i = 0; i < previous.Length; i++)
                sum += previous[i] * _transition[i, j];
            next[j] = sum * _sensor[observation, j];
        }

        return Normalize(next, $"filtrage avant, observation {observation}");
    }

    private double[] BackwardStep(double[] next, int observation)
    {
        var message = new double[_prior.Length];
        for (int i = 0; i < message.Length; i++)
        {
            double sum = 0;
            for (int j = 0; j < message.Length; j++)
                sum += _transition[i, j] * _sensor[observation, j] * next[j];
            message[i] = sum;
        }

        return Normalize(message, $"message arriere, observation {observation}");
    }

    private int RequireObservation(int observation)
    {
        if (observation < 0 || observation >= EvidenceCount)
            throw new ArgumentOutOfRangeException(
                nameof(observation), observation,
                $"L'observation doit appartenir a [0, {EvidenceCount - 1}].");
        return observation;
    }

    internal static double[] Uniform(int length)
    {
        var distribution = new double[length];
        Array.Fill(distribution, 1.0 / length);
        return distribution;
    }

    private static double[] Product(double[] left, double[] right)
    {
        var product = new double[left.Length];
        for (int i = 0; i < product.Length; i++)
            product[i] = left[i] * right[i];
        return product;
    }

    /// <summary>
    /// Normalise une distribution. Un vecteur de masse nulle est une impossibilite
    /// du modele (sequence d'observations de probabilite nulle) : on le signale
    /// plutot que de rendre silencieusement une distribution arbitraire.
    /// </summary>
    private static double[] Normalize(double[] distribution, string context)
    {
        double total = 0;
        foreach (double value in distribution)
            total += value;
        if (total <= 0 || double.IsNaN(total))
            throw new InvalidOperationException(
                $"Distribution de masse nulle au {context} : la sequence d'observations est de probabilite nulle " +
                "sous ce modele — verifier les tables de transition et d'observation.");

        for (int i = 0; i < distribution.Length; i++)
            distribution[i] /= total;
        return distribution;
    }

    private static void RequireStochasticRows(double[,] matrix, string name)
    {
        int rows = matrix.GetLength(0);
        int columns = matrix.GetLength(1);
        for (int i = 0; i < rows; i++)
        {
            double sum = 0;
            for (int j = 0; j < columns; j++)
            {
                RequireProbability(matrix[i, j], name, i, j);
                sum += matrix[i, j];
            }

            RequireUnitSum(sum, $"{name}, ligne {i}");
        }
    }

    private static void RequireStochasticColumns(double[,] matrix, string name)
    {
        int rows = matrix.GetLength(0);
        int columns = matrix.GetLength(1);
        for (int j = 0; j < columns; j++)
        {
            double sum = 0;
            for (int i = 0; i < rows; i++)
            {
                RequireProbability(matrix[i, j], name, i, j);
                sum += matrix[i, j];
            }

            RequireUnitSum(sum, $"{name}, colonne {j} (etat cache)");
        }
    }

    private static void RequireDistribution(double[] distribution, string name)
    {
        double sum = 0;
        for (int i = 0; i < distribution.Length; i++)
        {
            RequireProbability(distribution[i], name, i, -1);
            sum += distribution[i];
        }

        RequireUnitSum(sum, name);
    }

    private static void RequireProbability(double value, string name, int row, int column)
    {
        if (double.IsNaN(value) || value < 0 || value > 1)
        {
            string where = column >= 0 ? $"[{row}, {column}]" : $"[{row}]";
            throw new ArgumentException(
                $"Valeur hors de [0, 1] dans {name}{where} : {value}.", name);
        }
    }

    private static void RequireUnitSum(double sum, string where)
    {
        if (Math.Abs(sum - 1.0) > 1e-6)
            throw new ArgumentException(
                $"La distribution ne somme pas a 1 ({sum:G6}) : {where}.", where);
    }
}
