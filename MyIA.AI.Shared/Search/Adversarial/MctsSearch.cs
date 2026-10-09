namespace MyIA.AI.Shared.Search.Adversarial;

/// <summary>
/// Parametres d'une recherche arborescente Monte-Carlo (UCT). EPIC #7265, pepite B3,
/// tranche 6.
/// </summary>
/// <remarks>
/// Les valeurs par defaut ne sont pas des reglages « qui marchent » : le budget par
/// defaut (1000 iterations) est dimensionne sur le cout de playout <b>mesure</b> de
/// l'adaptateur Go (0,4 ms sur 5x5, 6,4 ms sur 9x9) -- voir la tranche 6 pour la
/// courbe. Un appelant qui change de jeu doit refaire cette mesure, pas heriter du
/// chiffre.
/// </remarks>
public sealed record MctsOptions
{
    /// <summary>Nombre de playouts par decision. Doit etre au moins 1.</summary>
    public int Iterations { get; init; } = 1000;

    /// <summary>
    /// Constante d'exploration de l'UCT, appliquee a la borne de Hoeffding.
    /// <c>sqrt(2)</c> est la valeur theorique pour des recompenses dans [0,1] ; les
    /// utilites du Go sont en points de partie, donc l'echelle relative a la constante
    /// change et la valeur reste un point de depart a mesurer, pas un theoreme.
    /// </summary>
    public double ExplorationConstant { get; init; } = 1.41;

    /// <summary>
    /// Graine du tirage. Le moteur est deterministe a graine fixee -- c'est ce qui
    /// rend un tournoi reproductible, et c'est verifie par temoin.
    /// </summary>
    public int Seed { get; init; }

    /// <summary>
    /// Plafond de coups d'un playout. Filet de securite : sur un jeu ou le passe est
    /// toujours legal (Go), un playout aleatoire atteint un etat terminal avec
    /// probabilite 1, et ce plafond ne devrait jamais mordre. S'il mord, le playout
    /// rend <c>0.0</c> -- une valeur neutre declaree, jamais presentee comme une
    /// evaluation de la position tronquee.
    /// </summary>
    public int MaxPlayoutDepth { get; init; } = 10_000;
}

/// <summary>
/// Recherche arborescente Monte-Carlo a bornes superieures de confiance (UCT) sur un
/// <see cref="IGame{TState, TAction, TPlayer}"/>. EPIC #7265, pepite B3, tranche 6.
/// </summary>
/// <remarks>
/// <para>
/// Les moteurs de la tranche 1 (<see cref="MinimaxSearch{TState, TAction, TPlayer}"/>,
/// <see cref="AlphaBetaSearch{TState, TAction, TPlayer}"/>,
/// <see cref="IterativeDeepeningAlphaBetaSearch{TState, TAction, TPlayer}"/>) partagent
/// une hypothese : une <b>heuristique d'evaluation</b> exploitable a la profondeur
/// atteinte. Sur Go cette hypothese est fausse -- l'evaluation myope ne voit ni les
/// coupes ni les semeai, et le facteur de branchement interdit une profondeur utile.
/// L'UCT remplace l'heuristique par l'<b>echantillonnage</b> : il ne note pas une
/// position, il joue la partie au hasard et compte.
/// </para>
/// <para>
/// <b>Les quatre phases</b>, dans l'ordre, une iteration = un playout :
/// </para>
/// <list type="number">
///   <item><description><b>Selection</b> -- descente depuis la racine en prenant, a
///   chaque noeud, l'enfant qui maximise <c>moyenne + c * sqrt(ln(N_parent) / n_enfant)</c>.
///   Le premier terme exploite, le second explore : c'est le compromis qui donne son
///   nom a l'algorithme.</description></item>
///   <item><description><b>Expansion</b> -- un coup encore jamais joue depuis le noeud
///   atteint est ouvert, tire uniformement parmi les non-essayes.</description></item>
///   <item><description><b>Simulation</b> -- playout a coups uniformement aleatoires
///   jusqu'a un etat terminal.</description></item>
///   <item><description><b>Retropropagation</b> -- le resultat remonte la branche et
///   incremente les visites et la somme de valeurs de chaque ancetre.</description></item>
/// </list>
/// <para>
/// <b>Perspective des valeurs -- le point qui se trompe en silence.</b> Chaque noeud
/// accumule <c>Utility(terminal, joueurRacine)</c>, donc <i>toutes</i> les moyennes de
/// l'arbre sont exprimees du point de vue du <b>joueur qui decide a la racine</b>. La
/// selection maximise a un noeud ou c'est ce joueur qui a le trait, et <b>minimise</b>
/// a un noeud ou c'est l'adversaire. Maximiser partout produirait un moteur qui joue
/// contre lui-meme : les parties seraient legales et les temoins de legalite verts,
/// seul le taux de victoire s'effondrerait. L'hypothese somme nulle du contrat
/// <see cref="IGame{TState, TAction, TPlayer}"/> est ce qui rend ce basculement correct.
/// </para>
/// <para>
/// <b>Le coup rendu est le plus <i>visite</i>, pas le mieux note.</b> Un enfant a
/// une seule visite et une moyenne parfaite est un coup de chance, pas un coup : la
/// moyenne est le bon critere pour choisir ou <i>descendre</i>, la frequentation est
/// le bon critere pour choisir quoi <i>jouer</i>. Meme regle que la source Python de
/// la serie Search (App-14), qui compte egalement les visites.
/// </para>
/// <para>
/// <b>Aucun elagage.</b> <see cref="AdversarialMetrics.PrunedBranches"/> reste a zero
/// par construction : l'UCT n'elague pas, il concentre son budget. Le comparer a
/// alpha-beta sur ce compteur n'a pas de sens -- la comparaison qui en a un est le
/// taux de victoire a budget de temps ou de playouts egal.
/// </para>
/// <para>
/// <b>Operateur natif nomme (doctrine organ-first).</b> Le depot portait deja un MCTS
/// <i>Python</i> : les cellules de <c>App-14-ConnectFour-Adversarial.ipynb</c> et de ses
/// variantes, ecrites pour le seul ConnectFour et non importables (cellules de carnet,
/// pas module). La version C# ci-dessous est <b>generique sur le contrat de jeu</b> et
/// n'importe donc aucune regle de ConnectFour ; c'est la fonction que le carnet rendait
/// au cas particulier, pas une seconde copie de celui-ci. La serie Search garde la
/// main sur la pedagogie, cette bibliotheque sur l'organe.
/// </para>
/// </remarks>
/// <typeparam name="TState">Type de l'etat du jeu.</typeparam>
/// <typeparam name="TAction">Type d'un coup.</typeparam>
/// <typeparam name="TPlayer">Type du joueur.</typeparam>
public sealed class MctsSearch<TState, TAction, TPlayer> : IAdversarialSearch<TState, TAction, TPlayer>
    where TState : notnull
{
    private sealed class Node
    {
        public required TState State { get; init; }

        public Node? Parent { get; init; }

        /// <summary>Coup qui a mene a ce noeud. Nul pour la racine.</summary>
        public TAction? Action { get; init; }

        public List<Node> Children { get; } = [];

        /// <summary>Coups legaux du noeud jamais encore ouverts. L'ordre est celui du jeu.</summary>
        public required List<TAction> Untried { get; init; }

        /// <summary>Nombre de playouts passes par ce noeud.</summary>
        public int Visits { get; set; }

        /// <summary>Somme des utilites recues, du point de vue du joueur qui decide a la racine.</summary>
        public double TotalValue { get; set; }
    }

    private readonly IGame<TState, TAction, TPlayer> _game;
    private readonly MctsOptions _options;

    /// <summary>
    /// Compteurs du dernier appel a <see cref="MakeDecision"/> — meme contrat que les
    /// moteurs de la tranche 1 : remis a zero a chaque decision, jamais cumules.
    /// </summary>
    /// <remarks>
    /// <see cref="AdversarialMetrics.PrunedBranches"/> reste a zero par construction :
    /// l'UCT n'elague pas, il concentre son budget sur les branches prometteuses. Un
    /// moteur qui ne coupe rien et un moteur qui coupe beaucoup ne se comparent donc
    /// pas sur ce compteur, mais a budget de playouts egal.
    /// </remarks>
    public AdversarialMetrics Metrics { get; private set; } = new();

    /// <summary>Moteur UCT sur <paramref name="game"/>, regle par <paramref name="options"/>.</summary>
    /// <exception cref="ArgumentOutOfRangeException">
    /// Si <see cref="MctsOptions.Iterations"/> vaut moins de 1 -- une decision sans
    /// aucun playout n'a pas de coup a rendre, et rendre le premier coup legal
    /// deguiserait ce vide en choix.
    /// </exception>
    public MctsSearch(IGame<TState, TAction, TPlayer> game, MctsOptions? options = null)
    {
        ArgumentNullException.ThrowIfNull(game);
        _game = game;
        _options = options ?? new MctsOptions();

        if (_options.Iterations < 1)
        {
            throw new ArgumentOutOfRangeException(
                nameof(options),
                _options.Iterations,
                "Une recherche Monte-Carlo exige au moins une iteration.");
        }

        if (_options.MaxPlayoutDepth < 1)
        {
            throw new ArgumentOutOfRangeException(
                nameof(options),
                _options.MaxPlayoutDepth,
                "Un playout de profondeur nulle ne rendrait jamais d'etat terminal.");
        }
    }

    /// <inheritdoc />
    /// <remarks>
    /// <see cref="AdversarialDecision{T}.Depth"/> porte ici la <b>profondeur maximale
    /// atteinte dans l'arbre</b>, pas une profondeur garantie : l'UCT approfondit de
    /// facon irreguliere et n'offre aucune borne de qualite liee a cette valeur. Elle
    /// est rapportee pour le diagnostic, pas comme un engagement.
    /// </remarks>
    public AdversarialDecision<TAction>? MakeDecision(TState state)
    {
        ArgumentNullException.ThrowIfNull(state);

        Metrics = new AdversarialMetrics();

        IReadOnlyList<TAction> actions = _game.Actions(state);
        if (actions.Count == 0)
        {
            return null;
        }

        Metrics.ExpandedNodes = 1;
        Metrics.GeneratedActions = actions.Count;

        TPlayer rootPlayer = _game.Player(state);
        var root = new Node
        {
            State = state,
            Untried = [.. actions],
        };

        var rng = new Random(_options.Seed);
        int maxDepth = 0;

        for (int iteration = 0; iteration < _options.Iterations; iteration++)
        {
            // 1. Selection -- descend tant que le noeud est developpe et non terminal.
            Node node = root;
            int depth = 0;
            while (node.Untried.Count == 0 && node.Children.Count > 0 && !_game.IsTerminal(node.State))
            {
                node = SelectChild(node, rootPlayer);
                depth++;
            }

            // 2. Expansion -- ouvre un coup jamais essaye depuis ce noeud.
            if (node.Untried.Count > 0 && !_game.IsTerminal(node.State))
            {
                int pick = rng.Next(node.Untried.Count);
                TAction action = node.Untried[pick];
                node.Untried.RemoveAt(pick);

                TState next = _game.Result(node.State, action);
                List<TAction> nextUntried = [.. _game.Actions(next)];

                var child = new Node
                {
                    State = next,
                    Parent = node,
                    Action = action,
                    Untried = nextUntried,
                };

                node.Children.Add(child);
                Metrics.ExpandedNodes++;
                Metrics.GeneratedActions += nextUntried.Count;
                node = child;
                depth++;
            }

            if (depth > maxDepth)
            {
                maxDepth = depth;
            }

            // 3. Simulation -- playout uniformement aleatoire jusqu'au terminal.
            double outcome = Playout(node.State, rootPlayer, rng);

            // 4. Retropropagation -- la valeur remonte la branche, perspective racine.
            for (Node? ancestor = node; ancestor is not null; ancestor = ancestor.Parent)
            {
                ancestor.Visits++;
                ancestor.TotalValue += outcome;
            }
        }

        Metrics.MaxDepthReached = maxDepth;

        // Le coup joue est le plus visite, pas le mieux note (cf. remarques de classe).
        Node chosen = root.Children[0];
        foreach (Node candidate in root.Children)
        {
            if (candidate.Visits > chosen.Visits)
            {
                chosen = candidate;
            }
        }

        double mean = chosen.Visits == 0 ? 0.0 : chosen.TotalValue / chosen.Visits;
        return new AdversarialDecision<TAction>(chosen.Action!, mean, Metrics, maxDepth);
    }

    /// <summary>
    /// Choisit l'enfant a developer. Maximise si le trait appartient au joueur de la
    /// racine, minimise sinon -- c'est le basculement qui encode « somme nulle ».
    /// </summary>
    /// <remarks>
    /// <b>La negation du signe, et pas seulement du bonus.</b> Le critere d'un noeud
    /// minimisant est <c>argmin(moyenne - bonus)</c> -- on veut l'enfant le plus
    /// <i>bas</i>, en reservant de l'exploration aux moins visites. L'ecrire
    /// <c>argmax(moyenne - bonus)</c> -- la forme qu'on obtient en « retournant le
    /// signe du bonus » -- selectionne exactement l'inverse : l'enfant de moyenne
    /// <b>haute</b> et bien visite. Le moteur jouerait alors le meilleur coup de
    /// l'adversaire, en silence : aucune illegalite, aucun plantage, seulement un taux
    /// de victoire effondre. La forme correcte est donc <c>argmax(signe * moyenne +
    /// bonus)</c> avec <c>signe = -1</c> au noeud minimisant, ce qui donne bien
    /// <c>argmax(-moyenne + bonus)</c>.
    /// </remarks>
    private Node SelectChild(Node node, TPlayer rootPlayer)
    {
        bool maximize = EqualityComparer<TPlayer>.Default.Equals(_game.Player(node.State), rootPlayer);
        double logParent = Math.Log(node.Visits);
        double sign = maximize ? 1.0 : -1.0;

        Node best = node.Children[0];
        double bestScore = Score(best, logParent, sign);

        for (int i = 1; i < node.Children.Count; i++)
        {
            Node candidate = node.Children[i];
            double score = Score(candidate, logParent, sign);
            if (score > bestScore)
            {
                bestScore = score;
                best = candidate;
            }
        }

        return best;
    }

    /// <summary>
    /// Borne superieure de confiance d'un enfant, toujours maximisee : l'orientation
    /// du noeud est portee par <paramref name="sign"/> (+1 si le trait est au joueur
    /// de la racine, -1 sinon), jamais par le sens de la comparaison.
    /// </summary>
    private double Score(Node child, double logParent, double sign)
    {
        if (child.Visits == 0)
        {
            return double.PositiveInfinity;
        }

        double mean = child.TotalValue / child.Visits;
        double bonus = _options.ExplorationConstant * Math.Sqrt(logParent / child.Visits);
        return (sign * mean) + bonus;
    }

    /// <summary>
    /// Playout a coups uniformement aleatoires, rendu du point de vue du joueur de la
    /// racine. Un playout tronque au plafond rend <c>0.0</c> -- valeur neutre declaree,
    /// jamais presentee comme une evaluation.
    /// </summary>
    private double Playout(TState from, TPlayer rootPlayer, Random rng)
    {
        TState current = from;
        int steps = 0;

        while (!_game.IsTerminal(current) && steps < _options.MaxPlayoutDepth)
        {
            IReadOnlyList<TAction> actions = _game.Actions(current);
            if (actions.Count == 0)
            {
                break;
            }

            current = _game.Result(current, actions[rng.Next(actions.Count)]);
            steps++;
        }

        return _game.IsTerminal(current) ? _game.Utility(current, rootPlayer) : 0.0;
    }
}
