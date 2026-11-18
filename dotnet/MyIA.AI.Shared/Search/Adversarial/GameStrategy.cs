namespace MyIA.AI.Shared.Search.Adversarial;

/// <summary>
/// Famille de moteurs adversariaux, telle que le patrimoine la configurait.
/// </summary>
public enum GameStrategy
{
    /// <summary>Minimax pur : developpe tout l'arbre, elague rien.</summary>
    MiniMax,

    /// <summary>Alpha-beta : meme decision que minimax, moins de noeuds developpes.</summary>
    AlphaBeta,

    /// <summary>Alpha-beta borne en profondeur et en temps, approfondi par palliers.</summary>
    IterativeDeepeningAlphaBeta,

    /// <summary>
    /// Cas particulier patrimonial du precedent sur Connect Four (demo AIMA) :
    /// le jeu Connect Four n'etant pas porte ici, ce membre se resout en
    /// <see cref="IterativeDeepeningAlphaBeta"/> avec les memes bornes.
    /// </summary>
    ConnectFourIDAlphaBeta,
}

/// <summary>
/// Fabrique et bornes de configuration d'un moteur adversarial -- la surface du
/// <c>GameStrategyInfo</c> du patrimoine, sans ses attributs d'UI DNN.
/// </summary>
/// <typeparam name="TState">Type de l'etat du jeu.</typeparam>
/// <typeparam name="TAction">Type d'un coup.</typeparam>
/// <typeparam name="TPlayer">Type du joueur.</typeparam>
public sealed class GameStrategyInfo<TState, TAction, TPlayer>
    where TState : notnull
{
    /// <summary>Moteur a instancier.</summary>
    public GameStrategy StrategyType { get; init; } = GameStrategy.AlphaBeta;

    /// <summary>
    /// Borne inferieure des utilites, pour la fenetre initiale de l'approfondissement
    /// iteratif. Le patrimoine la fixait a 0.0.
    /// </summary>
    public double MinUtility { get; init; }

    /// <summary>
    /// Borne superieure des utilites, pour la fenetre initiale de l'approfondissement
    /// iteratif. Le patrimoine la fixait a 1.0.
    /// </summary>
    public double MaxUtility { get; init; } = 1.0;

    /// <summary>
    /// Budget temps de l'approfondissement iteratif, en secondes. Le patrimoine le
    /// fixait a 5. Le moteur rend la meilleure decision etablie avant expiration,
    /// jamais une decision partielle incoerente.
    /// </summary>
    public double MaxDurationSeconds { get; init; } = 5;

    /// <summary>
    /// Borne de profondeur de l'approfondissement iteratif. Le patrimoine n'en avait
    /// pas : son unique borne etait le temps. Une borne explicite rend le moteur
    /// deterministe et testable -- un temoin ne peut pas attendre une horloge.
    /// </summary>
    public int MaxDepth { get; init; } = int.MaxValue;

    /// <summary>
    /// Evaluation heuristique d'un etat NON terminal pour le joueur donne, dans
    /// l'echelle [<see cref="MinUtility"/>, <see cref="MaxUtility"/>]. Exigee par
    /// l'approfondissement iteratif au moment ou la borne de profondeur coupe
    /// l'arbre avant la fin de partie ; ignoree par les moteurs complets.
    /// </summary>
    public Func<TState, TPlayer, double>? Heuristic { get; init; }

    /// <summary>
    /// Construit le moteur correspondant a la configuration, pour le jeu donne --
    /// le <c>createFor(objGame)</c> du patrimoine.
    /// </summary>
    public IAdversarialSearch<TState, TAction, TPlayer> CreateFor(IGame<TState, TAction, TPlayer> game) =>
        StrategyType switch
        {
            GameStrategy.MiniMax => new MinimaxSearch<TState, TAction, TPlayer>(game),
            GameStrategy.AlphaBeta => new AlphaBetaSearch<TState, TAction, TPlayer>(game),
            GameStrategy.IterativeDeepeningAlphaBeta or GameStrategy.ConnectFourIDAlphaBeta =>
                new IterativeDeepeningAlphaBetaSearch<TState, TAction, TPlayer>(
                    game, MinUtility, MaxUtility, MaxDurationSeconds, MaxDepth, Heuristic),
            _ => throw new ArgumentOutOfRangeException(nameof(StrategyType)),
        };
}
