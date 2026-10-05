namespace MyIA.AI.Shared.Search.Adversarial;

/// <summary>
/// Minimax exact (AIMA figure 5.2) : developpe tout l'arbre de jeu et remonte
/// l'utilite en faisant jouer chaque niveau a son optimum.
/// </summary>
/// <remarks>
/// <para>
/// Port du <c>MinimaxSearch.createFor(game)</c> du patrimoine. La recursivite est
/// celle du manuel : <c>MinValue</c> et <c>MaxValue</c> s'appellent l'une l'autre,
/// et la decision rassemble les valeurs des fils de la racine pour prendre le
/// maximum. Aucun elagage -- c'est le temoin de reference auquel alpha-beta doit
/// rendre la meme decision pour moins de noeuds.
/// </para>
/// <para>
/// L'egalite de valeur entre coups se tranche par l'ordre de <c>Actions</c> : le
/// premier coup maximisant gagne. C'est ce qui rend les compteurs reproductibles
/// d'une execution a l'autre, meme sur des jeux a coups equivalents.
/// </para>
/// </remarks>
/// <typeparam name="TState">Type de l'etat du jeu.</typeparam>
/// <typeparam name="TAction">Type d'un coup.</typeparam>
/// <typeparam name="TPlayer">Type du joueur.</typeparam>
public sealed class MinimaxSearch<TState, TAction, TPlayer> : IAdversarialSearch<TState, TAction, TPlayer>
    where TState : notnull
{
    /// <inheritdoc />
    public AdversarialDecision<TAction>? MakeDecision(TState state)
    {
        ArgumentNullException.ThrowIfNull(state);

        IGame<TState, TAction, TPlayer> game = Game;
        List<TAction> actions = game.Actions(state).ToList();
        if (actions.Count == 0)
        {
            return null;
        }

        TPlayer player = game.Player(state);
        Metrics = new AdversarialMetrics();
        double best = double.NegativeInfinity;
        TAction? bestAction = default;
        foreach (TAction action in actions)
        {
            Metrics.GeneratedActions++;
            double value = MinValue(game.Result(state, action), player, 1);
            if (value > best)
            {
                best = value;
                bestAction = action;
            }
        }

        return new AdversarialDecision<TAction>(bestAction!, best, Metrics, Metrics.MaxDepthReached);
    }

    /// <summary>Jeu sur lequel ce moteur decide.</summary>
    public IGame<TState, TAction, TPlayer> Game { get; }

    public MinimaxSearch(IGame<TState, TAction, TPlayer> game)
    {
        Game = game;
    }

    /// <summary>Compteurs du dernier appel a <see cref="MakeDecision"/>.</summary>
    public AdversarialMetrics Metrics { get; private set; } = new();

    internal double MaxValue(TState state, TPlayer player, int depth)
    {
        Metrics.ExpandedNodes++;
        Metrics.MaxDepthReached = Math.Max(Metrics.MaxDepthReached, depth);

        IGame<TState, TAction, TPlayer> game = Game;
        if (game.IsTerminal(state))
        {
            return game.Utility(state, player);
        }

        double value = double.NegativeInfinity;
        foreach (TAction action in game.Actions(state))
        {
            Metrics.GeneratedActions++;
            value = Math.Max(value, MinValue(game.Result(state, action), player, depth + 1));
        }

        return value;
    }

    internal double MinValue(TState state, TPlayer player, int depth)
    {
        Metrics.ExpandedNodes++;
        Metrics.MaxDepthReached = Math.Max(Metrics.MaxDepthReached, depth);

        IGame<TState, TAction, TPlayer> game = Game;
        if (game.IsTerminal(state))
        {
            return game.Utility(state, player);
        }

        double value = double.PositiveInfinity;
        foreach (TAction action in game.Actions(state))
        {
            Metrics.GeneratedActions++;
            value = Math.Min(value, MaxValue(game.Result(state, action), player, depth + 1));
        }

        return value;
    }
}
