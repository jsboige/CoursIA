namespace MyIA.AI.Shared.Search.Adversarial.Go;

/// <summary>
/// Adaptateur <see cref="IGame{TState, TAction, TPlayer}"/> du plateau Go : branche
/// le moteur de regles mutable de la tranche 2 (#19185) sur le contrat fonctionnel
/// des moteurs de recherche de la tranche 1 (#19176). EPIC #7265, pepite B3, tranche 3.
/// </summary>
/// <remarks>
/// <para>
/// La source d'origine (<c>Aricie.PortalKeeper/AI/Go/Go.cs</c>, 383 lignes) etait le
/// harnais complet : features 361 cases, evaluation CNTK, parsing <c>final_status_list</c>
/// de gnugo. Ce qui est porte ici n'est que la jointure des deux tranches livrees :
/// le plateau devient un <c>IGame</c>, donc explorable par les moteurs adversariaux.
/// L'evaluation CNTK reste une tranche separee (techno morte, verdict SOTA et
/// checklist 6 axes requis) ; gnugo/GTP est deja livre par la validation croisee
/// de la tranche 2.
/// </para>
/// <para>
/// <b>Moteurs complets exclus</b> : minimax et alpha-beta sans borne developpent
/// l'arbre jusqu'a une fin de partie -- sur Go, deux passes ne surviennent que
/// par convention d'arbitrage, jamais par epuisement des coups (le passe est
/// toujours legal) : ces moteurs ne terminent pas en pratique. Le moteur de Go est
/// l'<see cref="IterativeDeepeningAlphaBetaSearch{TState, TAction, TPlayer}"/> borne,
/// configure par <see cref="GameStrategyInfo{TState, TAction, TPlayer}"/> -- le
/// patrimoine en faisait autant (son <c>IterativeDeepeningAlphaBetaSearch</c> etait
/// le moteur monte sur le harnais Go).
/// </para>
/// <para>
/// <b>Cout du flood-fill</b> : la tranche 2 a reecrit les chaines et libertes en
/// flood-fill local plutot qu'en structures incrementales (equivalent pour les
/// regles, plus lent par coup). Chaque <see cref="Result"/> est un clone complet du
/// plateau, et chaque evaluation d'egalite/suicide refait un parcours : les
/// temoins de cette tranche mesurent ce cout en noeuds developpes -- c'est le
/// chiffre qu'une future structure incrementale devra battre.
/// </para>
/// </remarks>
public sealed class GoGameAdapter : IGame<GoGame, GoPoint, GoColor>
{
    /// <summary>Taille du plateau adapte, 2 a 25.</summary>
    public int Size { get; }

    /// <summary>Komi du plateau adapte, ajoute au score de territoire du blanc.</summary>
    public double Komi { get; }

    /// <summary>Adaptateur d'un plateau <paramref name="size"/>, komi compris.</summary>
    public GoGameAdapter(int size = 19, double komi = 7.5)
    {
        Size = size;
        Komi = komi;
    }

    /// <summary>
    /// Borne inferieure sure de toute utilite : aucun score de territoire ne
    /// descend sous <c>-(size^2 + |komi|)</c>. Surensemble volontaire de l'intervalle
    /// exact -- la fenetre d'aspiration de l'approfondissement iteratif n'en est
    /// que plus large, jamais prematurement « resolue ».
    /// </summary>
    public double MinUtility => -(double)(Size * Size) - Math.Abs(Komi);

    /// <summary>Borne superieure sure de toute utilite, miroir de <see cref="MinUtility"/>.</summary>
    public double MaxUtility => (double)(Size * Size) + Math.Abs(Komi);

    /// <inheritdoc />
    /// <remarks>Plateau vide, noir au trait.</remarks>
    public GoGame InitialState => new(Size, Komi);

    /// <inheritdoc />
    public GoColor Player(GoGame state) => state.ToPlay;

    /// <inheritdoc />
    /// <remarks>
    /// Ordre d'exploration : balayage ligne par ligne (Y croissant, X croissant),
    /// passe en dernier. L'ordre est significatif pour l'elagage -- c'est un
    /// parametre du moteur, pas un detail. Le passe est toujours legal tant que la
    /// partie n'est pas finie : sans lui, un plateau sans coup avantageux ne
    /// pourrait jamais se terminer.
    /// </remarks>
    public IReadOnlyList<GoPoint> Actions(GoGame state)
    {
        ArgumentNullException.ThrowIfNull(state);

        List<GoPoint> actions = new(state.Size * state.Size + 1);
        if (state.IsOver)
        {
            return actions;
        }

        for (int y = 0; y < state.Size; y++)
        {
            for (int x = 0; x < state.Size; x++)
            {
                GoPoint point = new(x, y);
                if (state.IsLegal(point))
                {
                    actions.Add(point);
                }
            }
        }

        actions.Add(GoPoint.Pass);
        return actions;
    }

    /// <inheritdoc />
    /// <remarks>Le resultat est un clone : l'etat d'origine n'est jamais mute.</remarks>
    public GoGame Result(GoGame state, GoPoint action)
    {
        ArgumentNullException.ThrowIfNull(state);

        GoGame next = state.Clone();
        if (!next.Play(action))
        {
            throw new InvalidOperationException(
                $"Coup illegal pour {state.ToPlay} dans cet etat : {action}.");
        }

        return next;
    }

    /// <inheritdoc />
    public bool IsTerminal(GoGame state) => state.IsOver;

    /// <inheritdoc />
    /// <remarks>
    /// Score de territoire (a la chinoise, komi compris) de la tranche 2, en
    /// points de partie -- pas dans [0, 1] : le patrimoine normalisait via CNTK,
    /// hors perimetre. Antisymetrique par construction, l'hypothese somme nulle
    /// du contrat est tenue. Le vide n'est pas un joueur : il echoue.
    /// </remarks>
    public double Utility(GoGame state, GoColor player)
    {
        ArgumentNullException.ThrowIfNull(state);
        return player switch
        {
            GoColor.Black => state.AreaScore(),
            GoColor.White => -state.AreaScore(),
            _ => throw new ArgumentOutOfRangeException(
                nameof(player), player, "Le vide n'est pas un joueur."),
        };
    }

    /// <summary>
    /// Heuristique d'horizon : l'avance de territoire vivante, la meme mesure que
    /// <see cref="Utility"/> appliquee avant la fin de partie. C'est la ligne de
    /// base honnete qui remplace l'evaluation CNTK du patrimoine (techno morte,
    /// verdict separe) : myope -- elle ne voit ni les coupes ni les semeai -- mais
    /// exacte sur ce qu'elle mesure, et confrontable a un contre-exemple.
    /// </summary>
    public static double TerritoryHeuristic(GoGame state, GoColor player)
    {
        ArgumentNullException.ThrowIfNull(state);
        return player switch
        {
            GoColor.Black => state.AreaScore(),
            GoColor.White => -state.AreaScore(),
            _ => throw new ArgumentOutOfRangeException(
                nameof(player), player, "Le vide n'est pas un joueur."),
        };
    }
}
