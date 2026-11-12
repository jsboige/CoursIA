namespace MyIA.AI.Shared.Search.Adversarial;

/// <summary>
/// Elagage alpha-beta (AIMA figure 5.5) : meme decision que minimax, obtenue en
/// developpant moins de noeuds -- les branches qui ne peuvent pas influer sur la
/// decision ne sont pas explorees.
/// </summary>
/// <remarks>
/// <para>
/// Port du <c>AlphaBetaSearch.createFor(game)</c> du patrimoine. La fenetre
/// [alpha, beta] se resserre en descendant : alpha est la meilleure valeur deja
/// assuree pour MAX sur le chemin, beta la pire pour MIN. Une branche dont la
/// valeur sort de la fenetre est coupee : elle ne peut plus changer la decision,
/// seulement la confirmer.
/// </para>
/// <para>
/// Le compteur <see cref="AdversarialMetrics.PrunedBranches"/> compte les coupes.
/// L'egalite de valeur entre coups suit l'ordre de <c>Actions</c>, comme pour
/// minimax : les deux moteurs rendent alors le meme coup ET le comptent pareil,
/// et seul l'ecart de noeuds developpes distingue leurs arbres.
/// </para>
/// <para>
/// L'efficacite de l'elagage depend de l'ordre des coups : le meilleur coup
/// explore en premier resserre la fenetre au maximum. Le compteur de branches
/// coupees est donc une fonction de l'ordre fourni par <c>Actions</c>, pas une
/// constante du jeu -- c'est un fait mesurable, pas un defaut.
/// </para>
/// </remarks>
/// <typeparam name="TState">Type de l'etat du jeu.</typeparam>
/// <typeparam name="TAction">Type d'un coup.</typeparam>
/// <typeparam name="TPlayer">Type du joueur.</typeparam>
public sealed class AlphaBetaSearch<TState, TAction, TPlayer> : IAdversarialSearch<TState, TAction, TPlayer>
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
        double alpha = double.NegativeInfinity;
        double beta = double.PositiveInfinity;
        double best = double.NegativeInfinity;
        TAction? bestAction = default;
        foreach (TAction action in actions)
        {
            Metrics.GeneratedActions++;
            double value = MinValue(game.Result(state, action), player, alpha, beta, 1);
            if (value > best)
            {
                best = value;
                bestAction = action;
            }

            // A la racine, alpha monte : les coups suivants savent deja ce que
            // MAX s'est assure, et MIN pourra couper en dessous.
            alpha = Math.Max(alpha, best);
        }

        return new AdversarialDecision<TAction>(bestAction!, best, Metrics, Metrics.MaxDepthReached);
    }

    /// <summary>Jeu sur lequel ce moteur decide.</summary>
    public IGame<TState, TAction, TPlayer> Game { get; }

    public AlphaBetaSearch(IGame<TState, TAction, TPlayer> game)
    {
        Game = game;
    }

    /// <summary>Compteurs du dernier appel a <see cref="MakeDecision"/>.</summary>
    public AdversarialMetrics Metrics { get; private set; } = new();

    internal double MaxValue(TState state, TPlayer player, double alpha, double beta, int depth)
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
            value = Math.Max(value, MinValue(game.Result(state, action), player, alpha, beta, depth + 1));
            if (value >= beta)
            {
                // Coupe beta : MIN a deja une option au plus aussi bonne ailleurs
                // sur le chemin -- cette branche ne peut plus remonter plus haut.
                Metrics.PrunedBranches++;
                return value;
            }

            alpha = Math.Max(alpha, value);
        }

        return value;
    }

    internal double MinValue(TState state, TPlayer player, double alpha, double beta, int depth)
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
            value = Math.Min(value, MaxValue(game.Result(state, action), player, alpha, beta, depth + 1));
            if (value <= alpha)
            {
                // Coupe alpha : MAX a deja une option au moins aussi bonne ailleurs
                // sur le chemin -- cette branche ne peut plus descendre plus bas.
                Metrics.PrunedBranches++;
                return value;
            }

            beta = Math.Min(beta, value);
        }

        return value;
    }
}
