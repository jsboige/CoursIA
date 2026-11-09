using System.Diagnostics;

namespace MyIA.AI.Shared.Search.Adversarial;

/// <summary>
/// Approfondissement iteratif d'alpha-beta (AIMA section 5.4.3) : des recherches
/// alpha-beta bornees a profondeur croissante, jusqu'a epuisement du budget
/// temps ou de la borne de profondeur, en gardant la meilleure decision etablie.
/// </summary>
/// <remarks>
/// <para>
/// Port du <c>IterativeDeepeningAlphaBetaSearch.createFor(game, min, max, seconds)</c>
/// du patrimoine. Deux bornes y restaient implicites et sont explicites ici :
/// la <see cref="MaxDepth"/>, que le patrimoine n'avait pas (seule l'horloge
/// bornait sa recherche), et l'<see cref="Heuristic"/> d'evaluation des etats non
/// terminaux, que le patrimoine derivait des bornes d'utilite. Rendre ces bornes
/// explicites est ce qui rend le moteur deterministe et testable : un temoin ne
/// peut pas attendre une horloge, et une evaluation heuristique implicite est une
/// evaluation qu'on ne peut pas confronter a un contre-exemple.
/// </para>
/// <para>
/// <b>Contract de decision</b> : la decision rendue est celle du dernier pallier
/// COMPLET. Un pallier interrompu par l'horloge est abandonne en bloc, jamais
/// rendu a moitie -- c'est ce qui distingue « meilleure decision etablie avant
/// expiration » de « decision partielle incoerente ». A palliers complets, la
/// decision du pallier le plus profond est au moins aussi informe que celle du
/// precedent ; l'abandon en bloc garantit qu'on ne rend jamais un melange des deux.
/// </para>
/// <para>
/// La fenetre initiale [<see cref="_minUtility"/>, <see cref="_maxUtility"/>] sert
/// de bornes d'appel au premier pallier : c'est la « fenetre aspiree » du
/// patrimoine, qui laisse le premier pallier etablir les bornes reelles.
/// </para>
/// </remarks>
/// <typeparam name="TState">Type de l'etat du jeu.</typeparam>
/// <typeparam name="TAction">Type d'un coup.</typeparam>
/// <typeparam name="TPlayer">Type du joueur.</typeparam>
public sealed class IterativeDeepeningAlphaBetaSearch<TState, TAction, TPlayer>
    : IAdversarialSearch<TState, TAction, TPlayer>
    where TState : notnull
{
    private readonly double _minUtility;
    private readonly double _maxUtility;
    private readonly TimeSpan _maxDuration;
    private readonly int _maxDepth;
    private readonly Func<TState, TPlayer, double>? _heuristic;

    /// <summary>Jeu sur lequel ce moteur decide.</summary>
    public IGame<TState, TAction, TPlayer> Game { get; }

    /// <summary>Compteurs cumules du dernier appel a <see cref="MakeDecision"/> (tous palliers).</summary>
    public AdversarialMetrics Metrics { get; private set; } = new();

    public IterativeDeepeningAlphaBetaSearch(
        IGame<TState, TAction, TPlayer> game,
        double minUtility,
        double maxUtility,
        double maxDurationSeconds,
        int maxDepth,
        Func<TState, TPlayer, double>? heuristic)
    {
        Game = game;
        _minUtility = minUtility;
        _maxUtility = maxUtility;
        _maxDuration = TimeSpan.FromSeconds(maxDurationSeconds);
        _maxDepth = maxDepth;
        _heuristic = heuristic;
    }

    /// <inheritdoc />
    public AdversarialDecision<TAction>? MakeDecision(TState state)
    {
        ArgumentNullException.ThrowIfNull(state);

        List<TAction> actions = Game.Actions(state).ToList();
        if (actions.Count == 0)
        {
            return null;
        }

        TPlayer player = Game.Player(state);
        Metrics = new AdversarialMetrics();
        Stopwatch clock = Stopwatch.StartNew();

        // Le pallier 1 ne coupe rien (tout etat a profondeur 1 y est une feuille
        // ou une evaluation) : il etablit la decision de repli et les premieres
        // bornes reelles de la fenetre.
        AdversarialDecision<TAction> best = DecideAtDepth(state, actions, player, 1);
        for (int depth = 2; depth <= _maxDepth; depth++)
        {
            if (clock.Elapsed >= _maxDuration)
            {
                break;
            }

            AdversarialDecision<TAction> candidate = DecideAtDepth(state, actions, player, depth);
            if (clock.Elapsed >= _maxDuration)
            {
                // Le pallier a depasse le budget pendant son execution : abandonne
                // en bloc, la decision du pallier precedent reste la reference.
                break;
            }

            best = candidate;

            // Le jeu est resolu plus vite que la borne : un pallier qui atteint
            // une utilite extreme ne peut plus etre ameliore par un pallier plus profond.
            if (best.Value <= _minUtility || best.Value >= _maxUtility)
            {
                break;
            }
        }

        return best;
    }

    private AdversarialDecision<TAction> DecideAtDepth(
        TState state, List<TAction> actions, TPlayer player, int depthLimit)
    {
        double alpha = _minUtility;
        double beta = _maxUtility;
        double best = double.NegativeInfinity;
        TAction bestAction = actions[0];
        foreach (TAction action in actions)
        {
            Metrics.GeneratedActions++;
            double value = Bounded(
                Game.Result(state, action), player, alpha, beta, 1, depthLimit);
            if (value > best)
            {
                best = value;
                bestAction = action;
            }

            alpha = Math.Max(alpha, best);
        }

        return new AdversarialDecision<TAction>(bestAction, best, Metrics, depthLimit);
    }

    private double Bounded(TState state, TPlayer player, double alpha, double beta, int depth, int depthLimit)
    {
        Metrics.ExpandedNodes++;
        Metrics.MaxDepthReached = Math.Max(Metrics.MaxDepthReached, depth);

        if (Game.IsTerminal(state))
        {
            return Game.Utility(state, player);
        }

        // Borne de profondeur atteinte : l'etat n'est pas terminal, on l'evalue
        // par l'heuristique configuree. Sans heuristique, la valeur neutre du
        // milieu de fenetre -- evaluer a une borne sans heuristique est une
        // absence d'avis, pas une opinion.
        if (depth >= depthLimit)
        {
            return _heuristic is null
                ? (_minUtility + _maxUtility) / 2.0
                : _heuristic(state, player);
        }

        bool maximizing = EqualityComparer<TPlayer>.Default.Equals(Game.Player(state), player);
        return maximizing
            ? MaxBounded(state, player, alpha, beta, depth, depthLimit)
            : MinBounded(state, player, alpha, beta, depth, depthLimit);
    }

    private double MaxBounded(TState state, TPlayer player, double alpha, double beta, int depth, int depthLimit)
    {
        double value = double.NegativeInfinity;
        foreach (TAction action in Game.Actions(state))
        {
            Metrics.GeneratedActions++;
            value = Math.Max(value, Bounded(Game.Result(state, action), player, alpha, beta, depth + 1, depthLimit));
            if (value >= beta)
            {
                Metrics.PrunedBranches++;
                return value;
            }

            alpha = Math.Max(alpha, value);
        }

        return value;
    }

    private double MinBounded(TState state, TPlayer player, double alpha, double beta, int depth, int depthLimit)
    {
        double value = double.PositiveInfinity;
        foreach (TAction action in Game.Actions(state))
        {
            Metrics.GeneratedActions++;
            value = Math.Min(value, Bounded(Game.Result(state, action), player, alpha, beta, depth + 1, depthLimit));
            if (value <= alpha)
            {
                Metrics.PrunedBranches++;
                return value;
            }

            beta = Math.Min(beta, value);
        }

        return value;
    }
}
