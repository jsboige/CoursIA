namespace MyIA.AI.Shared.Search.Probability;

/// <summary>
/// Filtrage particulaire (echantillonnage preferentiel avec reechantillonnage,
/// AIMA ch. 15) sur le meme modele qu'un <see cref="HiddenMarkovModel"/>.
/// </summary>
/// <remarks>
/// Le filtre particulaire est l'approximation du <see cref="HiddenMarkovModel.Filter"/>
/// exact : il porte la meme loi a un jeu de particules pondere pres. C'est cette
/// parente qui rend le port pedagogique — les deux moteurs lisent **les memes tables**,
/// donc l'ecart entre eux est un ecart d'echantillonnage, mesurable, et non un
/// desaccord de modele.
///
/// Cycle d'un pas de temps (<see cref="Update"/>) : propagation selon la transition,
/// ponderation par la vraisemblance de l'observation, normalisation, puis
/// reechantillonnage systematique des que la taille effective de l'echantillon
/// (<see cref="EffectiveSampleSize"/>) tombe sous la moitie du jeu.
///
/// Le generateur est seme : deux instances de meme graine et meme sequence
/// d'observations rendent des distributions identiques — condition pour que le
/// comportement du filtre soit verifiable.
/// </remarks>
public sealed class ParticleFilter
{
    private readonly HiddenMarkovModel _model;
    private readonly Random _random;
    private readonly int[] _states;
    private readonly double[] _weights;

    /// <summary>Construit un filtre particulaire initialise sur la loi a priori du modele.</summary>
    /// <param name="model">Modele temporel discret qui fournit transition, observation et a priori.</param>
    /// <param name="particleCount">Nombre de particules (au moins 1).</param>
    /// <param name="seed">Graine du generateur — meme graine, meme trajectoire.</param>
    public ParticleFilter(HiddenMarkovModel model, int particleCount, int seed = 0)
    {
        ArgumentNullException.ThrowIfNull(model);
        ArgumentOutOfRangeException.ThrowIfNegativeOrZero(particleCount);

        _model = model;
        _random = new Random(seed);
        ParticleCount = particleCount;
        _states = new int[particleCount];
        _weights = new double[particleCount];
        Array.Fill(_weights, 1.0 / particleCount);

        double[] prior = model.Prior;
        for (int particle = 0; particle < particleCount; particle++)
            _states[particle] = Sample(prior);
    }

    /// <summary>Nombre de particules portees par le filtre.</summary>
    public int ParticleCount { get; }

    /// <summary>
    /// Taille effective de l'echantillon, <c>1 / sum(w^2)</c> : proche du nombre de
    /// particules quand les poids sont proches de l'uniforme, elle s'effondre quand
    /// quelques particules portent toute la masse — c'est le signal de reechantillonnage.
    /// </summary>
    public double EffectiveSampleSize
    {
        get
        {
            double squared = 0;
            foreach (double weight in _weights)
                squared += weight * weight;
            return squared <= 0 ? 0 : 1.0 / squared;
        }
    }

    /// <summary>
    /// Fait avancer le filtre d'un pas : propagation, ponderation par l'observation,
    /// reechantillonnage si necessaire.
    /// </summary>
    /// <param name="observation">Indice d'observation, dans <c>[0, EvidenceCount - 1]</c>.</param>
    public void Update(int observation)
    {
        if (observation < 0 || observation >= _model.EvidenceCount)
            throw new ArgumentOutOfRangeException(
                nameof(observation), observation,
                $"L'observation doit appartenir a [0, {_model.EvidenceCount - 1}].");

        double[,] transition = _model.Transition;
        double[,] sensor = _model.Sensor;

        // 1. Propagation : chaque particule tire son etat suivant de sa ligne de transition.
        double[][] rows = new double[_model.StateCount][];
        for (int i = 0; i < rows.Length; i++)
        {
            rows[i] = new double[_model.StateCount];
            for (int j = 0; j < rows.Length; j++)
                rows[i][j] = transition[i, j];
        }

        for (int particle = 0; particle < _states.Length; particle++)
            _states[particle] = Sample(rows[_states[particle]]);

        // 2. Ponderation : la vraisemblance de l'observation, colonne par etat cache.
        double total = 0;
        for (int particle = 0; particle < _states.Length; particle++)
        {
            _weights[particle] *= sensor[observation, _states[particle]];
            total += _weights[particle];
        }

        if (total <= 0 || double.IsNaN(total))
            throw new InvalidOperationException(
                $"Aucune particule ne rend l'observation {observation} possible : le jeu de particules " +
                "s'est effondre sur des etats de vraisemblance nulle — augmenter ParticleCount ou revoir les tables.");

        for (int particle = 0; particle < _weights.Length; particle++)
            _weights[particle] /= total;

        // 3. Reechantillonnage systematique des que la masse effective s'effondre.
        if (EffectiveSampleSize < ParticleCount / 2.0)
            Resample();
    }

    /// <summary>
    /// Distribution courante sur les etats caches, obtenue en cumulant le poids des
    /// particules par etat.
    /// </summary>
    public double[] Distribution()
    {
        var distribution = new double[_model.StateCount];
        for (int particle = 0; particle < _states.Length; particle++)
            distribution[_states[particle]] += _weights[particle];
        return distribution;
    }

    /// <summary>Etats portes par les particules (copie).</summary>
    public int[] States => (int[])_states.Clone();

    /// <summary>Poids normalises portes par les particules (copie).</summary>
    public double[] Weights => (double[])_weights.Clone();

    /// <summary>
    /// Reechantillonnage systematique : une seule variable uniforme decale les
    /// <c>N</c> tirages sur la distribution cumulee, ce qui preserve la masse et
    /// garde la variance de l'echantillonneur sous celle du tirage independant.
    /// </summary>
    private void Resample()
    {
        var cumulative = new double[_weights.Length];
        double running = 0;
        for (int particle = 0; particle < _weights.Length; particle++)
        {
            running += _weights[particle];
            cumulative[particle] = running;
        }

        var resampled = new int[_states.Length];
        double step = running / _states.Length;
        double cursor = _random.NextDouble() * step;
        int index = 0;
        for (int particle = 0; particle < resampled.Length; particle++)
        {
            double target = cursor + particle * step;
            while (index < cumulative.Length - 1 && cumulative[index] < target)
                index++;
            resampled[particle] = _states[index];
        }

        Array.Copy(resampled, _states, resampled.Length);
        Array.Fill(_weights, 1.0 / _weights.Length);
    }

    /// <summary>Tirage categoriel sur une distribution deja normalisee.</summary>
    private int Sample(double[] distribution)
    {
        double target = _random.NextDouble();
        double running = 0;
        for (int i = 0; i < distribution.Length; i++)
        {
            running += distribution[i];
            if (target < running)
                return i;
        }

        // Arrondi flottant en bout de distribution : le dernier etat porte la masse restante.
        return distribution.Length - 1;
    }
}
