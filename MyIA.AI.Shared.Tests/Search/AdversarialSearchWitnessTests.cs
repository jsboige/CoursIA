using MyIA.AI.Shared.Search.Adversarial;
using Xunit;
using Xunit.Abstractions;

namespace MyIA.AI.Shared.Tests.Search;

/// <summary>
/// Temoins adversariaux du moteur de jeux (EPIC #7265, pepite B3).
///
/// Un arbre de jeu explicite, construit noeud par noeud, ou une seule arete fait
/// diverger un moteur de son propre contrat : minimax doit supposer l'adversaire
/// optimal (pas reachable-max), alpha-beta doit rendre la meme decision que
/// minimax pour strictement moins de noeuds developpes -- et l'ordre des coups
/// doit faire varier ce gain, sinon le compteur d'elagage ne mesure rien.
/// L'approfondissement iteratif doit rendre minimax quand la profondeur suffit,
/// et une decision d'horizon borne quand elle ne suffit pas.
/// </summary>
public sealed class AdversarialSearchWitnessTests
{
    private readonly ITestOutputHelper _output;

    public AdversarialSearchWitnessTests(ITestOutputHelper output) => _output = output;

    /// <summary>
    /// Arbre de jeu explicite a deux joueurs (X au trait aux profondeurs paires,
    /// O aux impaires), somme nulle : l'utilite est definie pour X, celle de O
    /// est son oppose. L'ordre des actions dans <see cref="Node"/> est l'ordre
    /// d'exploration -- il est significatif pour l'elagage, c'est un parametre
    /// du temoin, pas un detail.
    /// </summary>
    private sealed class TreeGame : IGame<string, string, char>
    {
        private readonly Dictionary<string, string[]> _actions = new();
        private readonly Dictionary<(string State, string Action), string> _result = new();
        private readonly Dictionary<string, string> _parent = new();
        private readonly Dictionary<string, double> _utilityX = new();
        private readonly string _initial;
        private readonly char _firstPlayer;

        private TreeGame(string initial, Dictionary<string, double> utilityX, char firstPlayer)
        {
            _initial = initial;
            _utilityX = utilityX;
            _firstPlayer = firstPlayer;
        }

        /// <summary>Arbre dont la racine est deja une fin : utilite pour X.</summary>
        public static TreeGame Terminal(string name, double utilityForX) =>
            new(name, new Dictionary<string, double> { [name] = utilityForX }, 'X');

        /// <summary>Arbre dont la racine est un noeud de decision, X au trait.</summary>
        public static TreeGame Root(string name) => new(name, new Dictionary<string, double>(), 'X');

        /// <summary>
        /// Arbre dont la racine est un noeud de decision, O au trait : pour temoiner
        /// le miroir somme nulle depuis l'autre rive du plateau.
        /// </summary>
        public static TreeGame RootO(string name) => new(name, new Dictionary<string, double>(), 'O');

        public string InitialState => _initial;

        /// <summary>Enregistre les coups d'un noeud (dans l'ordre d'exploration voulu).</summary>
        public TreeGame Node(string state, params (string Action, string Child)[] children)
        {
            _actions[state] = children.Select(child => child.Action).ToArray();
            foreach ((string action, string child) in children)
            {
                _result[(state, action)] = child;
                if (!_parent.ContainsKey(child))
                {
                    _parent[child] = state;
                }
            }

            return this;
        }

        /// <summary>Definit l'utilite d'une fin, du point de vue de X.</summary>
        public TreeGame Utility(string terminal, double forX)
        {
            _utilityX[terminal] = forX;
            return this;
        }

        public char Player(string state) =>
            (Depth(state) + (_firstPlayer == 'O' ? 1 : 0)) % 2 == 0 ? 'X' : 'O';

        public IReadOnlyList<string> Actions(string state) =>
            _actions.TryGetValue(state, out string[]? actions) ? actions : Array.Empty<string>();

        public string Result(string state, string action) => _result[(state, action)];

        public bool IsTerminal(string state) => !_actions.ContainsKey(state);

        public double Utility(string state, char player) =>
            player == 'X' ? _utilityX[state] : -_utilityX[state];

        private int Depth(string state)
        {
            int depth = 0;
            string current = state;
            while (_parent.TryGetValue(current, out string? parent))
            {
                depth++;
                current = parent;
            }

            return depth;
        }
    }

    // ------------------------------------------------------------------
    // Temoin 1 -- minimax suppose l'adversaire optimal, pas reachable-max.
    // ------------------------------------------------------------------

    /// <summary>
    /// Racine X ; coup « prendre » mene directement a une fin a 5 ; coup
    /// « tenter » mene a un noeud O qui choisit entre une fin a 1 et une fin a
    /// 10. Un moteur qui maximiserait sur les fins ATTEIGNABLES prefererait
    /// « tenter » (10 &gt; 5) ; minimax doit preferer « prendre », parce que O,
    /// optimal, choisira la fin a 1. La valeur de « tenter » est 1, pas 10.
    /// </summary>
    [Fact]
    public void MinimaxAssumesAnOptimalOpponentNotReachableMax()
    {
        TreeGame game = TreeGame.Root("root")
            .Node("root", ("prendre", "fin5"), ("tenter", "choixO"))
            .Node("choixO", ("gauche", "fin1"), ("droite", "fin10"))
            .Utility("fin5", 5).Utility("fin1", 1).Utility("fin10", 10);

        MinimaxSearch<string, string, char> engine = new(game);
        AdversarialDecision<string> decision = engine.MakeDecision("root")!;

        Assert.Equal("prendre", decision.Action);
        Assert.Equal(5d, decision.Value, 6);
        _output.WriteLine($"minimax : {decision.Action} = {decision.Value} "
                          + $"({engine.Metrics.ExpandedNodes} noeuds)");
    }

    /// <summary>
    /// Somme nulle, temoin comportemental : sur les DEUX memes issues (une fin
    /// a 1 pour X, une fin a 10 pour X), chaque joueur au trait prefere celle
    /// qui lui est la meilleure -- X choisit la fin a 10, O choisit la fin a 1
    /// (qui vaut -1 pour lui, contre -10 pour l'autre). Preferences opposees
    /// sur le meme couple d'issues : c'est ce que « somme nulle » veut dire pour
    /// un moteur qui maximise l'utilitaire de QUI JOUE.
    /// </summary>
    [Fact]
    public void ZeroSumPlayersHaveOppositePreferencesOverTheSameOutcomes()
    {
        TreeGame xGame = TreeGame.Root("choix")
            .Node("choix", ("gauche", "fin1"), ("droite", "fin10"))
            .Utility("fin1", 1).Utility("fin10", 10);
        TreeGame oGame = TreeGame.RootO("choix")
            .Node("choix", ("gauche", "fin1"), ("droite", "fin10"))
            .Utility("fin1", 1).Utility("fin10", 10);

        AdversarialDecision<string> forX = new MinimaxSearch<string, string, char>(xGame)
            .MakeDecision("choix")!;
        AdversarialDecision<string> forO = new MinimaxSearch<string, string, char>(oGame)
            .MakeDecision("choix")!;

        Assert.Equal("droite", forX.Action);
        Assert.Equal("gauche", forO.Action);
        // Ce qu'O securise (-1) est exactement ce que X perd sur cette issue :
        // l'utilite de fin1 vue de X vaut 1, l'oppose de ce qu'O en obtient.
        Assert.Equal(-forO.Value, xGame.Utility("fin1", 'X'), 6);
        _output.WriteLine($"X choisit {forX.Action}={forX.Value} ; O choisit {forO.Action}={forO.Value}");
    }

    // ------------------------------------------------------------------
    // Temoin 2 -- alpha-beta : meme decision, moins de noeuds, elagage mesurable.
    // ------------------------------------------------------------------

    /// <summary>
    /// Arbre ou l'elagage tire : la premiere branche etablit une borne serree
    /// (min 3), et dans la seconde le coup a 2 tombe sous la borne AVANT le
    /// dernier frere -- le frere a 9 n'est jamais developpe. Alpha-beta doit
    /// rendre la meme decision et la meme valeur que minimax, en developpant
    /// strictement moins de noeuds, avec un compteur d'elagage strictement
    /// positif.
    /// </summary>
    [Fact]
    public void AlphaBetaMatchesMinimaxDecisionWhileExpandingFewerNodes()
    {
        TreeGame game = TreeGame.Root("root")
            .Node("root", ("a", "minA"), ("b", "minB"))
            .Node("minA", ("a1", "t3"), ("a2", "t5"))
            .Node("minB", ("b1", "t6"), ("b2", "t2"), ("b3", "t9"))
            .Utility("t3", 3).Utility("t5", 5)
            .Utility("t6", 6).Utility("t2", 2).Utility("t9", 9);

        MinimaxSearch<string, string, char> minimax = new(game);
        AlphaBetaSearch<string, string, char> alphabeta = new(game);

        AdversarialDecision<string> full = minimax.MakeDecision("root")!;
        AdversarialDecision<string> pruned = alphabeta.MakeDecision("root")!;

        Assert.Equal(full.Action, pruned.Action);
        Assert.Equal(full.Value, pruned.Value, 6);
        Assert.True(alphabeta.Metrics.ExpandedNodes < minimax.Metrics.ExpandedNodes,
            $"alpha-beta a developpe {alphabeta.Metrics.ExpandedNodes} noeuds, "
            + $"minimax {minimax.Metrics.ExpandedNodes} : l'elagage n'a pas tire");
        Assert.True(alphabeta.Metrics.PrunedBranches > 0, "aucune branche coupee : le compteur mesure du vide");
        _output.WriteLine($"minimax {minimax.Metrics.ExpandedNodes} noeuds vs "
                          + $"alpha-beta {alphabeta.Metrics.ExpandedNodes} "
                          + $"({alphabeta.Metrics.PrunedBranches} branches coupees) -> {pruned.Action} = {pruned.Value}");
    }

    /// <summary>
    /// Temoin inverse de l'elagage : l'ordre des coups inverse, la decision est
    /// identique mais le nombre de branches coupees change (ici : zero). C'est
    /// la preuve que le compteur mesure l'elagage reel, conditionnel a l'ordre,
    /// pas une constante du jeu.
    /// </summary>
    [Fact]
    public void AlphaBetaPruningDependsOnActionOrder()
    {
        TreeGame ordered = TreeGame.Root("root")
            .Node("root", ("a", "minA"), ("b", "minB"))
            .Node("minA", ("a1", "t3"), ("a2", "t5"))
            .Node("minB", ("b1", "t6"), ("b2", "t2"), ("b3", "t9"))
            .Utility("t3", 3).Utility("t5", 5)
            .Utility("t6", 6).Utility("t2", 2).Utility("t9", 9);

        TreeGame reversed = TreeGame.Root("root")
            .Node("root", ("b", "minB"), ("a", "minA"))
            .Node("minB", ("b3", "t9"), ("b2", "t2"), ("b1", "t6"))
            .Node("minA", ("a2", "t5"), ("a1", "t3"))
            .Utility("t3", 3).Utility("t5", 5)
            .Utility("t6", 6).Utility("t2", 2).Utility("t9", 9);

        AlphaBetaSearch<string, string, char> first = new(ordered);
        AlphaBetaSearch<string, string, char> second = new(reversed);

        AdversarialDecision<string> d1 = first.MakeDecision("root")!;
        AdversarialDecision<string> d2 = second.MakeDecision("root")!;

        Assert.Equal(d1.Action, d2.Action);
        Assert.Equal(d1.Value, d2.Value, 6);
        Assert.NotEqual(first.Metrics.PrunedBranches, second.Metrics.PrunedBranches);
        _output.WriteLine($"ordre favorable : {first.Metrics.PrunedBranches} coupes / "
                          + $"{first.Metrics.ExpandedNodes} noeuds ; ordre defavorable : "
                          + $"{second.Metrics.PrunedBranches} coupes / {second.Metrics.ExpandedNodes} noeuds");
    }

    // ------------------------------------------------------------------
    // Temoin 3 -- approfondissement iteratif : profondeur suffisante = minimax.
    // ------------------------------------------------------------------

    /// <summary>
    /// Sur un arbre entierement terminal a profondeur 2, l'iteratif avec une
    /// borne de profondeur large doit rendre exactement la decision minimax :
    /// chaque pallier complet est un alpha-beta borne, et le pallier qui couvre
    /// l'arbre atteint toutes les fins.
    /// </summary>
    [Fact]
    public void IterativeDeepeningAtFullDepthMatchesMinimax()
    {
        TreeGame game = TreeGame.Root("r")
            .Node("r", ("x", "nx"), ("y", "ny"))
            .Node("nx", ("x1", "tx1"), ("x2", "tx2"))
            .Node("ny", ("y1", "ty1"), ("y2", "ty2"))
            .Utility("tx1", 4).Utility("tx2", 9).Utility("ty1", 8).Utility("ty2", 2);

        MinimaxSearch<string, string, char> minimax = new(game);
        IterativeDeepeningAlphaBetaSearch<string, string, char> deep = new(game, 0d, 1d, 60d, 10, null);

        AdversarialDecision<string> reference = minimax.MakeDecision("r")!;
        AdversarialDecision<string> iterative = deep.MakeDecision("r")!;

        Assert.Equal(reference.Action, iterative.Action);
        Assert.Equal(reference.Value, iterative.Value, 6);
        _output.WriteLine($"minimax {reference.Action}={reference.Value} ; ID {iterative.Action}="
                          + $"{iterative.Value} a la profondeur {iterative.Depth} "
                          + $"({deep.Metrics.ExpandedNodes} noeuds cumules)");
    }

    /// <summary>
    /// Temoin de l'horizon : le gain est a profondeur 3, la borne a 2. Avec une
    /// heuristique myope, l'iteratif borne rend une decision DIFFERENTE de
    /// minimax -- c'est le contrat d'un moteur borne, pas un defaut ; le meme
    /// arbre sans la borne rend minimax. Les deux assertions ensemble prouvent
    /// que c'est la borne qui decide, pas le moteur.
    /// </summary>
    [Fact]
    public void IterativeDeepeningAtShallowDepthFallsToHorizon()
    {
        // r -x-> n1 -p-> n2 -{g,h}-> GAIN(9) | ZERO(0) ; r -y-> FIN(5).
        // Le coup « x » est le bon a profondeur 3 (minimax = 9) ; a profondeur 2,
        // l'heuristique myope ne voit pas la menace et « y », valeur certaine 5,
        // gagne.
        TreeGame game = TreeGame.Root("r")
            .Node("r", ("x", "n1"), ("y", "fin5"))
            .Node("n1", ("p", "n2"))
            .Node("n2", ("g", "gain9"), ("h", "zero"))
            .Utility("fin5", 5).Utility("gain9", 9).Utility("zero", 0);

        MinimaxSearch<string, string, char> minimax = new(game);
        IterativeDeepeningAlphaBetaSearch<string, string, char> shallow = new(game, 0d, 1d, 60d, 2, (_, _) => 0.5);

        AdversarialDecision<string> reference = minimax.MakeDecision("r")!;
        AdversarialDecision<string> horizon = shallow.MakeDecision("r")!;

        Assert.Equal("x", reference.Action);
        Assert.Equal(9d, reference.Value, 6);
        Assert.Equal("y", horizon.Action);
        Assert.Equal(5d, horizon.Value, 6);
        Assert.Equal(2, horizon.Depth);
        _output.WriteLine($"minimax : {reference.Action}={reference.Value} ; borne a 2 : "
                          + $"{horizon.Action}={horizon.Value} (horizon atteint, heuristique myope)");
    }

    /// <summary>
    /// Contract de decision sous budget nul : seul le pallier 1 est etabli, la
    /// decision rendue reste un coup legal coherent -- jamais un melange de
    /// palliers. Deterministe : le budget nul coupe avant tout pallier 2,
    /// quelle que soit la charge de la machine.
    /// </summary>
    [Fact]
    public void IterativeDeepeningUnderZeroBudgetYieldsTheFirstPallier()
    {
        TreeGame game = TreeGame.Root("r")
            .Node("r", ("x", "tx"), ("y", "ty"))
            .Utility("tx", 3).Utility("ty", 7);

        IterativeDeepeningAlphaBetaSearch<string, string, char> rushed = new(game, 0d, 1d, 0d, 10, null);

        AdversarialDecision<string> decision = rushed.MakeDecision("r")!;

        Assert.Equal("y", decision.Action);
        Assert.Equal(1, decision.Depth);
        Assert.Equal(2, rushed.Metrics.ExpandedNodes); // exactement les deux fils de la racine
        _output.WriteLine($"budget nul : pallier {decision.Depth}, {decision.Action}={decision.Value}");
    }

    /// <summary>
    /// Les metriques portent les cles du patrimoine AIMA (nodesExpanded,
    /// maxDepth) -- c'est la surface que <c>GameMoveResult</c> exposait via
    /// <c>getMetrics()</c>, conservee pour la tracabilite du port.
    /// </summary>
    [Fact]
    public void MetricsExposeThePatrimoineKeys()
    {
        TreeGame game = TreeGame.Root("r")
            .Node("r", ("x", "tx"), ("y", "ty"))
            .Utility("tx", 3).Utility("ty", 7);

        MinimaxSearch<string, string, char> engine = new(game);
        engine.MakeDecision("r");

        IReadOnlyDictionary<string, string> map = engine.Metrics.AsMap();
        Assert.Equal("2", map["nodesExpanded"]);
        Assert.Equal("1", map["maxDepth"]);
        Assert.Equal("0", map["branchesPruned"]);
        Assert.Equal("2", map["actionsGenerated"]);
    }
}
