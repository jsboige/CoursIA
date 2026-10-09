namespace MyIA.AI.Shared.Search.Adversarial;

/// <summary>
/// Parametres d'une recherche arborescente Monte-Carlo UCT parallele. EPIC #7265,
/// pepite B3, tranche 9 -- transcription moderne du <c>DistributedSearch</c> GoTraxx (C2).
/// </summary>
public sealed record ParallelMctsOptions
{
    /// <summary>Nombre total de playouts par decision, tous fils confondus. Doit etre au moins 1.</summary>
    public int Iterations { get; init; } = 1000;

    /// <summary>
    /// Constante d'exploration UCT, meme role et meme echelle que
    /// <see cref="MctsOptions.ExplorationConstant"/> : <c>sqrt(2)</c> pour des recompenses
    /// dans [0,1], point de depart a re-mesurer sur les utilites du jeu reel.
    /// </summary>
    public double ExplorationConstant { get; init; } = 1.41;

    /// <summary>
    /// Graine du tirage, derivee en une suite par ouvrier (graine + index d'ouvrier + 1).
    /// Le moteur est deterministe <b>uniquement</b> a
    /// <see cref="DegreeOfParallelism"/> 1 ; au-dela, l'entrelacement des ouvriers rend
    /// l'ordre des playouts non reproductible, et c'est le comportement attendu -- la
    /// comparaison d'un tournoi parallele se fait a budget egal, pas a graine egale.
    /// </summary>
    public int Seed { get; init; }

    /// <summary>Plafond de coups d'un playout, filet de securite identique a <see cref="MctsOptions.MaxPlayoutDepth"/>.</summary>
    public int MaxPlayoutDepth { get; init; } = 10_000;

    /// <summary>
    /// Nombre d'ouvriers qui consomment le budget en parallele. 1 = mode sequentiel
    /// deterministe (le temoin de reproductibilite l'exige). Chaque ouvrier boucle
    /// <c>revendication / playout / retropropagation</c> jusqu'a epuisement du budget
    /// global partage.
    /// </summary>
    public int DegreeOfParallelism { get; init; } = Environment.ProcessorCount;
}

/// <summary>
/// Recherche arborescente Monte-Carlo UCT a arbre partage : plusieurs ouvriers
/// descendent, echantillonnent et retropropagent dans le <b>meme</b> arbre
/// concurremment. EPIC #7265, pepite B3, tranche 9.
/// </summary>
/// <remarks>
/// <para>
/// <b>Provenance -- le <c>DistributedSearch</c> GoTraxx relu par son epoque.</b> La
/// source Aricie (<c>Libraries/AI/external/GoTraxx/DistributedSearch/</c> :
/// <c>NagCoordinator</c>, <c>NagNode</c>, <c>Worker</c>, <c>WorkerProxy</c>) repartissait
/// la recherche sur des processus distants via remoting .NET -- l'etat de l'art
/// distribue de son epoque. Le port litteral n'aurait aucun consommateur aujourd'hui
/// (le remoting est retire du runtime) ; ce qui survit de l'idee est le geste :
/// <b>plusieurs chercheurs, un meme arbre, un budget commun</b>. Cette classe le
/// realise en intra-processus sur la bibliotheque parallele, ou la synchronisation
/// coute une operation atomique et non un aller-retour reseau. Le corps de #7265
/// demande une evaluation de pertinence avant d'ouvrir la pepite C2 : la voici --
/// l'equivalent moderne du pattern est intra-machine, et c'est ce fichier.
/// </para>
/// <para>
/// <b>Arbre partage, pas vote d'arbres.</b> L'alternative naive au parallelisme
/// serait N moteurs sequentiels independants puis un vote : elle multiplie le travail
/// par N sans partager aucune information. Ici, chaque playout d'un ouvrier enrichit
/// l'arbre que les autres ouvriers descendent a l'instant suivant -- le budget
/// parallele achete de la <i>profondeur commune</i>, pas de la redondance. C'est la
/// difference entre « tree parallelization » et « root parallelization » dans la
/// litterature MCTS parallele (Browne et al., 2012, section 7.2), et le partage est
/// la forme qui conserve la propriete fondamentale de l'UCT : la convergence vers le
/// coup optimal a budget croissant.
/// </para>
/// <para>
/// <b>Ce qui est protege, et comment.</b> Trois courses existent sur un arbre
/// partage, chacune fermee par un mecanisme nomme :
/// <list type="bullet">
///   <item><description><b>Expansion double</b> -- deux ouvriers ouvriraient le meme
///   coup jamais essaye d'un meme noeud. Fermeture : le choix du coup, son retrait de
///   <c>Untried</c> et l'ajout de l'enfant a <c>Children</c> se font dans la meme
///   section critique du verrou d'expansion du parent. Un ouvrier qui trouve la liste
///   vide en prenant le verrou passe a la selection : le meme enfant ne peut pas
///   etre ouvert deux fois.</description></item>
///   <item><description><b>Division par zero a la selection</b> -- un enfant vient
///   d'etre cree par un autre ouvrier et n'a encore aucune visite. Fermeture : un
///   enfant sans visite a une borne superieure infinie et est selectionne en
///   priorite ; toutes les lectures de compteurs hors verrou passent par
///   <c>Volatile</c>.</description></item>
///   <item><description><b>Perte de mise a jour</b> -- deux ouvriers retropropagent
///   dans le meme ancetre au meme instant. Fermeture : les visites s'accumulent par
///   <c>Interlocked.Increment</c> et la somme de valeurs par une boucle
///   compare-and-swap sur double -- une retropropagation ne peut plus en ecraser
///   une autre.</description></item>
/// </list>
/// Ces fermetures ont un cout : la section critique de l'expansion execute
/// <c>Result</c> et <c>Actions</c> du jeu (elle doit retirer le coup et poser
/// l'enfant d'un meme geste atomique). Le rapport contention/gain est mesure dans
/// le corps de la tranche ; sur Go 9x9 il reste largement en-deca du benefice.
/// </para>
/// <para>
/// <b>Perte virtuelle, ecartee.</b> La technique habituelle contre la sur-selection
/// d'une branche convoitee (chaque ouvrier marque un deficit temporaire sur le
/// chemin qu'il descend) n'est pas employee : elle ferait diverger le mode
/// <see cref="ParallelMctsOptions.DegreeOfParallelism"/> 1 du moteur sequentiel de
/// la tranche 6, et le temoin de parite deterministe existe precisement pour garder
/// cette equivalence. Sans perte virtuelle, deux ouvriers peuvent descendre la meme
/// branche au meme instant -- le budget ainsi double-compte est de l'exploration
/// redondante bornee, pas une erreur.
/// </para>
/// <para>
/// <b>Les phases restent celles de la tranche 6</b> (selection / expansion /
/// simulation / retropropagation), avec la perspective racine unique et la bascule
/// max/min aux noeuds de l'adversaire -- voir les remarques de
/// <see cref="MctsSearch{TState, TAction, TPlayer}"/> pour le piege de la
/// maximisation partout, dont la forme fautive est silencieuse (aucune illegalite,
/// seul le taux de victoire s'effondre). Le coup rendu reste le plus <i>visite</i>,
/// pas le mieux note.
/// </para>
/// <para>
/// <b>Precondition de thread-safety portee par l'appelant.</b> Les ouvriers lisent
/// les memes etats (<c>Player</c>, <c>Actions</c>, <c>IsTerminal</c>, <c>Utility</c>)
/// concurremment : le contrat <see cref="IGame{TState, TAction, TPlayer}"/> doit etre
/// satisfait en lecture pure -- <c>Result</c> ne mute pas l'etat qu'on lui donne (le
/// contrat de la tranche 3 l'exige deja pour <c>Clone</c>), et les lectures
/// concurrentes d'un meme etat sont sans ecriture. Un jeu dont <c>Result</c> ou les
/// lectures muteraient un cache interne casserait ce moteur par course, pas par
/// exception : c'est documente ici comme une precondition, pas verifie a l'execution.
/// </para>
/// </remarks>
/// <typeparam name="TState">Type de l'etat du jeu.</typeparam>
/// <typeparam name="TAction">Type d'un coup.</typeparam>
/// <typeparam name="TPlayer">Type du joueur.</typeparam>
public sealed class ParallelMctsSearch<TState, TAction, TPlayer> : IAdversarialSearch<TState, TAction, TPlayer>
    where TState : notnull
{
    private sealed class Node
    {
        public required TState State { get; init; }

        public Node? Parent { get; init; }

        /// <summary>Coup qui a mene a ce noeud. Nul pour la racine.</summary>
        public TAction? Action { get; init; }

        /// <summary>Enfants ouverts. Ecrits uniquement sous <see cref="ExpandLock"/>, lus par instantane.</summary>
        public List<Node> Children { get; } = [];

        /// <summary>Verrou de ce noeud : protege l'ouverture d'enfants (Children + Untried ensemble).</summary>
        public object ExpandLock { get; } = new();

        /// <summary>Coups legaux jamais encore ouverts, sous <see cref="ExpandLock"/>.</summary>
        public required List<TAction> Untried { get; init; }

        /// <summary>Nombre de playouts passes par ce noeud, accumule par Interlocked, lu par Volatile.</summary>
        public int Visits;

        /// <summary>Somme des utilites recues, perspective du joueur qui decide a la racine.</summary>
        public double TotalValue;
    }

    private readonly IGame<TState, TAction, TPlayer> _game;
    private readonly ParallelMctsOptions _options;

    /// <summary>Compteurs du dernier appel a <see cref="MakeDecision"/>, remis a zero a chaque decision.</summary>
    public AdversarialMetrics Metrics { get; private set; } = new();

    /// <summary>
    /// Visites de la racine au dernier appel : chaque playout, quel que soit l'ouvrier,
    /// retropropage jusqu'a la racine -- ce compteur doit donc valoir exactement
    /// <see cref="ParallelMctsOptions.Iterations"/>. C'est le temoin de conservation du
    /// budget partage : une revendication perdue ou une retropropagation interrompue
    /// s'y lirait immediatement.
    /// </summary>
    public int RootVisits { get; private set; }

    /// <summary>Moteur UCT parallele sur <paramref name="game"/>, regle par <paramref name="options"/>.</summary>
    /// <exception cref="ArgumentOutOfRangeException">
    /// Si <see cref="ParallelMctsOptions.Iterations"/> vaut moins de 1, si
    /// <see cref="ParallelMctsOptions.MaxPlayoutDepth"/> vaut moins de 1, ou si
    /// <see cref="ParallelMctsOptions.DegreeOfParallelism"/> vaut moins de 1 -- un
    /// degre nul ne consommerait aucun playout et rendrait le premier coup legal
    /// deguise en decision.
    /// </exception>
    public ParallelMctsSearch(IGame<TState, TAction, TPlayer> game, ParallelMctsOptions? options = null)
    {
        ArgumentNullException.ThrowIfNull(game);
        _game = game;
        _options = options ?? new ParallelMctsOptions();

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

        if (_options.DegreeOfParallelism < 1)
        {
            throw new ArgumentOutOfRangeException(
                nameof(options),
                _options.DegreeOfParallelism,
                "Un degre de parallelisme nul ne consommerait aucun playout.");
        }
    }

    /// <inheritdoc />
    /// <remarks>
    /// <see cref="AdversarialMetrics.MaxDepthReached"/> porte la profondeur maximale
    /// de l'arbre construit (parcours post-fixe sous verrous courts) : c'est la meme
    /// grandeur que la tranche 6 appelle « profondeur maximale atteinte dans
    /// l'arbre », relevee ici apres coup puisque les ouvriers ne partagent pas de
    /// maximum commun sans lui faire payer un <c>Interlocked</c> par descente.
    /// </remarks>
    public AdversarialDecision<TAction>? MakeDecision(TState state)
    {
        ArgumentNullException.ThrowIfNull(state);

        Metrics = new AdversarialMetrics();
        RootVisits = 0;

        IReadOnlyList<TAction> actions = _game.Actions(state);
        if (actions.Count == 0)
        {
            return null;
        }

        TPlayer rootPlayer = _game.Player(state);
        var root = new Node
        {
            State = state,
            Untried = [.. actions],
        };

        // Budget global : chaque decrement revendique un playout. Le dernier ouvrier
        // a decrementer voit -1 et sort -- exactement Iterations playouts au total.
        int remaining = _options.Iterations;
        int expanded = 1;
        int generated = actions.Count;

        Parallel.For(0, _options.DegreeOfParallelism, worker =>
        {
            // Graine par ouvrier : l'index d'ouvrier est deterministe a chaque appel,
            // contrairement a l'identifiant de thread -- c'est ce qui preserve la
            // reproductibilite du mode a un seul ouvrier entre deux executions.
            var rng = new Random(_options.Seed + worker + 1);
            int localExpanded = 0;
            int localGenerated = 0;

            while (Interlocked.Decrement(ref remaining) >= 0)
            {
                RunPlayout(root, rootPlayer, rng, ref localExpanded, ref localGenerated);
            }

            Interlocked.Add(ref expanded, localExpanded);
            Interlocked.Add(ref generated, localGenerated);
        });

        Metrics.ExpandedNodes = expanded;
        Metrics.GeneratedActions = generated;
        Metrics.MaxDepthReached = TrackMaxDepth(root);
        RootVisits = Volatile.Read(ref root.Visits);

        // Le coup joue est le plus visite, pas le mieux note (meme regle que la tranche 6).
        Node chosen;
        lock (root.ExpandLock)
        {
            if (root.Children.Count == 0)
            {
                return null;
            }

            chosen = root.Children[0];
        }

        foreach (Node candidate in SnapshotChildren(root))
        {
            if (Volatile.Read(ref candidate.Visits) > Volatile.Read(ref chosen.Visits))
            {
                chosen = candidate;
            }
        }

        int visits = Volatile.Read(ref chosen.Visits);
        double mean = visits == 0 ? 0.0 : chosen.TotalValue / visits;
        return new AdversarialDecision<TAction>(chosen.Action!, mean, Metrics, Metrics.MaxDepthReached);
    }

    /// <summary>
    /// Un playout complet dans l'arbre partage : selection, expansion sous verrou,
    /// simulation aleatoire, retropropagation atomique. Les compteurs d'expansion
    /// sont accumules par l'appelant (par ouvrier) puis verses par un seul
    /// <c>Interlocked.Add</c> final.
    /// </summary>
    private void RunPlayout(Node root, TPlayer rootPlayer, Random rng, ref int expanded, ref int generated)
    {
        Node node = root;

        // 1. Selection -- jusqu'a un noeud terminal, ou un coup jamais essaye, ou
        // un noeud pleinement developpe sans enfant (fin de partie).
        while (!_game.IsTerminal(node.State))
        {
            bool expandedHere = false;
            lock (node.ExpandLock)
            {
                if (node.Untried.Count > 0)
                {
                    // 2. Expansion : choix du coup, retrait de Untried et ajout de
                    // l'enfant dans la meme section critique -- deux ouvriers ne
                    // peuvent pas ouvrir le meme coup.
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
                    expanded++;
                    generated += nextUntried.Count;
                    node = child;
                    expandedHere = true;
                }
            }

            if (expandedHere)
            {
                break;
            }

            if (node.Children.Count == 0)
            {
                // Untried vide et aucun enfant : l'etat n'offrait plus de coup au
                // moment de son ouverture. La selection n'a nulle part descendre --
                // le playout part de l'etat courant. (Pas de course : sans Untried,
                // plus aucun enfant ne peut apparaitre -- ils naitraient tous de
                // cette liste, sous le verrou qu'on vient de tenir.)
                break;
            }

            // Noeud pleinement developpe : on descend par la borne de confiance.
            Node? child2 = SelectChild(node, rootPlayer);
            if (child2 is null)
            {
                break;
            }

            node = child2;
        }

        // 3. Simulation -- playout uniformement aleatoire jusqu'au terminal,
        // perspective racine, meme filet de securite que la tranche 6.
        double outcome = Playout(node.State, rootPlayer, rng);

        // 4. Retropropagation -- atomique sur toute la branche.
        for (Node? ancestor = node; ancestor is not null; ancestor = ancestor.Parent)
        {
            Interlocked.Increment(ref ancestor.Visits);
            AddValue(ancestor, outcome);
        }
    }

    /// <summary>
    /// Accumulation d'une valeur sur le champ double d'un noeud par boucle
    /// compare-and-swap : <see cref="Interlocked"/> n'expose pas d'addition double
    /// sur toutes les cibles du projet, et une lecture-modification-ecriture libre
    /// perdrait des retropropagations concurrentes.
    /// </summary>
    private static void AddValue(Node node, double value)
    {
        double current = Volatile.Read(ref node.TotalValue);
        double witness;
        do
        {
            witness = current;
            current = Interlocked.CompareExchange(ref node.TotalValue, witness + value, witness);
        }
        while (current != witness);
    }

    /// <summary>
    /// Choisit l'enfant a descendre : <c>argmax(signe * moyenne + bonus)</c>, signe
    /// -1 aux noeuds de l'adversaire -- meme orientation que la tranche 6, dont la
    /// remarque de methode documente pourquoi retourner le seul signe du bonus
    /// selectionne le meilleur coup de l'adversaire, en silence.
    /// </summary>
    private Node? SelectChild(Node node, TPlayer rootPlayer)
    {
        bool maximize = EqualityComparer<TPlayer>.Default.Equals(_game.Player(node.State), rootPlayer);
        double logParent = Math.Log(Math.Max(1, Volatile.Read(ref node.Visits)));
        double sign = maximize ? 1.0 : -1.0;

        Node? best = null;
        double bestScore = double.NegativeInfinity;

        foreach (Node candidate in SnapshotChildren(node))
        {
            double score = Score(candidate, logParent, sign);
            if (score > bestScore)
            {
                bestScore = score;
                best = candidate;
            }
        }

        return best;
    }

    /// <summary>Borne superieure de confiance ; un enfant sans visite est infini (priorite d'ouverture).</summary>
    private double Score(Node child, double logParent, double sign)
    {
        int visits = Volatile.Read(ref child.Visits);
        if (visits == 0)
        {
            return double.PositiveInfinity;
        }

        double mean = child.TotalValue / visits;
        double bonus = _options.ExplorationConstant * Math.Sqrt(logParent / visits);
        return sign * mean + bonus;
    }

    /// <summary>Playout uniformement aleatoire jusqu'a l'etat terminal, borne par MaxPlayoutDepth.</summary>
    private double Playout(TState start, TPlayer rootPlayer, Random rng)
    {
        TState state = start;
        for (int step = 0; step < _options.MaxPlayoutDepth; step++)
        {
            if (_game.IsTerminal(state))
            {
                return _game.Utility(state, rootPlayer);
            }

            IReadOnlyList<TAction> actions = _game.Actions(state);
            if (actions.Count == 0)
            {
                return _game.Utility(state, rootPlayer);
            }

            state = _game.Result(state, actions[rng.Next(actions.Count)]);
        }

        return 0.0;
    }

    /// <summary>Instantane des enfants d'un noeud, copie courte prise sous son verrou.</summary>
    private static List<Node> SnapshotChildren(Node node)
    {
        lock (node.ExpandLock)
        {
            return [.. node.Children];
        }
    }

    /// <summary>Profondeur maximale de l'arbre, par parcours post-fixe a verrous courts.</summary>
    private static int TrackMaxDepth(Node node)
    {
        List<Node> children = SnapshotChildren(node);

        int max = 0;
        foreach (Node child in children)
        {
            int depth = TrackMaxDepth(child);
            if (depth > max)
            {
                max = depth;
            }
        }

        return max + (children.Count > 0 ? 1 : 0);
    }
}
