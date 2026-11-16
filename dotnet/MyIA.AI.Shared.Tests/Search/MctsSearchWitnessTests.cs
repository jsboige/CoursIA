using MyIA.AI.Shared.Search.Adversarial;
using MyIA.AI.Shared.Search.Adversarial.Go;
using Xunit;
using Xunit.Abstractions;

namespace MyIA.AI.Shared.Tests.Search;

/// <summary>
/// Temoins de la recherche arborescente Monte-Carlo (EPIC #7265, pepite B3, tranche 6).
///
/// L'UCT est stochastique : un temoin qui se contenterait de « le coup rendu est
/// legal » ne dirait rien, puisque tous les coups legaux le sont. Ce qui se temoigne
/// ici est ce qui distingue l'UCT d'un tirage au hasard -- la convergence vers le
/// coup qu'un adversaire optimal impose, la bascule max/min aux noeuds de l'adversaire,
/// et la reproductibilite a graine fixee, sans laquelle aucun tournoi ne serait
/// falsifiable.
/// </summary>
public sealed class MctsSearchWitnessTests
{
    private readonly ITestOutputHelper _output;

    public MctsSearchWitnessTests(ITestOutputHelper output) => _output = output;

    /// <summary>
    /// Graines balayees par les deux temoins de bascule. Le balayage n'est pas
    /// decoratif : une bascule fautive <b>n'est pas detectee a toutes les graines</b>.
    /// Mesure du 2026-10-09 sur un moteur dont le noeud minimisant comparait dans le
    /// mauvais sens (<c>argmax(moyenne - bonus)</c> au lieu de <c>argmin(moyenne -
    /// bonus)</c>) : l'arbre X rendait le <i>bon</i> coup aux graines 1 et 42 et le
    /// mauvais aux graines 7 et 99, l'arbre O exactement l'inverse. Un temoin a graine
    /// unique peut donc passer <b>par chance</b> sur un moteur casse -- et c'est
    /// precisement ce qui est arrive au premier temoin avant que le second ne tombe.
    /// Balayer quatre graines rend cette coincidence impossible.
    /// </summary>
    private static readonly int[] Seeds = [1, 7, 42, 99];

    /// <summary>
    /// Arbre de jeu explicite a somme nulle (X aux profondeurs paires, O aux impaires).
    /// Volontairement distinct du <c>TreeGame</c> des temoins de la tranche 1 : celui-ci
    /// ne sert qu'a porter les arbres de ces temoins-la et n'expose pas l'utilite par
    /// noeud dont un temoin MCTS a besoin pour verifier la valeur rendue.
    /// </summary>
    private sealed class ZeroSumTree : IGame<string, string, char>
    {
        private readonly Dictionary<string, string[]> _actions = new();
        private readonly Dictionary<(string State, string Action), string> _result = new();
        private readonly Dictionary<string, string> _parent = new();
        private readonly Dictionary<string, double> _utilityX = new();
        private readonly string _initial;
        private readonly char _firstPlayer;

        private ZeroSumTree(string initial, char firstPlayer)
        {
            _initial = initial;
            _firstPlayer = firstPlayer;
        }

        /// <summary>Arbre dont la racine est un noeud de decision, X au trait.</summary>
        public static ZeroSumTree ForX(string root) => new(root, 'X');

        /// <summary>Arbre dont la racine est un noeud de decision, O au trait.</summary>
        public static ZeroSumTree ForO(string root) => new(root, 'O');

        /// <summary>Arbre reduit a une fin : plus aucun coup legal a la racine.</summary>
        public static ZeroSumTree Terminal(string node, double utilityForX)
        {
            ZeroSumTree tree = new(node, 'X');
            tree._utilityX[node] = utilityForX;
            return tree;
        }

        public string InitialState => _initial;

        /// <summary>Declare les coups d'un noeud ; l'ordre est celui d'exploration.</summary>
        public ZeroSumTree Node(string state, params (string Action, string Child)[] children)
        {
            _actions[state] = children.Select(child => child.Action).ToArray();
            foreach ((string action, string child) in children)
            {
                _result[(state, action)] = child;
                _parent.TryAdd(child, state);
            }

            return this;
        }

        /// <summary>Utilite d'une fin, du point de vue de X.</summary>
        public ZeroSumTree Utility(string terminal, double forX)
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

    /// <summary>
    /// Arbre ou l'adversaire decide : X peut prendre 5 tout de suite, ou tenter une
    /// branche que O arbitre entre 1 et 10. Un moteur qui lirait la meilleure fin
    /// ATTEIGNABLE prefererait « tenter » (10) ; l'UCT doit preferer « prendre »,
    /// parce que O jouera 1.
    ///
    /// C'est exactement le temoin de la tranche 1 transpose a un moteur stochastique :
    /// la convergence doit reproduire la decision deterministe quand le budget suffit.
    ///
    /// Le balayage de graines est la partie qui mord : a graine unique, un moteur casse
    /// peut rendre le bon coup <b>par chance</b> (mesure du 2026-10-09, cf. <see cref="Seeds"/>).
    /// S'il tombe sur une seule des quatre graines, c'est le moteur qu'il faut corriger.
    /// </summary>
    [Fact]
    public void MctsConvergesToTheMoveAnOptimalOpponentImposes()
    {
        ZeroSumTree game = ZeroSumTree.ForX("root")
            .Node("root", ("prendre", "fin5"), ("tenter", "choixO"))
            .Node("choixO", ("gauche", "fin1"), ("droite", "fin10"))
            .Utility("fin5", 5).Utility("fin1", 1).Utility("fin10", 10);

        foreach (int seed in Seeds)
        {
            MctsSearch<string, string, char> engine = new(game, new MctsOptions { Iterations = 2000, Seed = seed });
            AdversarialDecision<string> decision = engine.MakeDecision("root")!;

            Assert.True(decision.Action == "prendre",
                $"graine {seed} : « {decision.Action} » rendu au lieu de « prendre » -- "
                + "le moteur joue le meilleur coup de l'adversaire au lieu du sien");

            // « prendre » mene a une fin deterministe : la moyenne rendue est exactement 5,
            // pas une approximation -- c'est ce qui rend l'assertion falsifiable.
            Assert.Equal(5d, decision.Value, 6);
            _output.WriteLine($"graine {seed,3} : UCT {decision.Action} = {decision.Value} "
                              + $"({engine.Metrics.ExpandedNodes} noeuds, profondeur {decision.Depth})");
        }
    }

    /// <summary>
    /// Temoin de la bascule max/min, pris par l'autre rive. Sur le meme arbre, O au
    /// trait doit preferer ce que X redoute : il joue « prendre » pour laisser X a 5
    /// plutot que de lui ouvrir 10.
    ///
    /// Un moteur qui maximiserait la valeur du joueur racine a TOUS les noeuds -- la
    /// facon la plus courte de casser un MCTS, et celle qui ne produit aucun echec de
    /// legalite -- jouerait l'adversaire a sa place et choisirait « tenter » : depuis
    /// la rive de O, « tenter » vaut le <i>maximum</i> (-1) et « prendre » -5. Les deux
    /// assertions de ce temoin et du precedent, prises ensemble, ne peuvent pas etre
    /// satisfaites par un moteur sans bascule.
    ///
    /// Ce temoin attrape aussi la bascule <i>presente mais comparee dans le mauvais
    /// sens</i> (<c>argmax</c> au lieu d'<c>argmin</c> au noeud minimisant), que le
    /// premier temoin laisse passer sur certaines graines -- c'est la panne mesuree le
    /// 2026-10-09, la ou les deux temoins se sont reveles complementaires.
    /// </summary>
    [Fact]
    public void MctsFlipsMaxToMinAtOpponentNodes()
    {
        ZeroSumTree game = ZeroSumTree.ForO("root")
            .Node("root", ("prendre", "fin5"), ("tenter", "choixO"))
            .Node("choixO", ("gauche", "fin1"), ("droite", "fin10"))
            .Utility("fin5", 5).Utility("fin1", 1).Utility("fin10", 10);

        foreach (int seed in Seeds)
        {
            MctsSearch<string, string, char> engine = new(game, new MctsOptions { Iterations = 2000, Seed = seed });
            AdversarialDecision<string> decision = engine.MakeDecision("root")!;

            Assert.True(decision.Action == "prendre",
                $"graine {seed} : « {decision.Action} » rendu au lieu de « prendre » -- "
                + "la bascule max/min est absente ou comparee dans le mauvais sens");

            // Depuis la rive de O, la meme fin vaut l'oppose : c'est la somme nulle.
            Assert.Equal(-5d, decision.Value, 6);
            _output.WriteLine($"graine {seed,3} : UCT depuis O {decision.Action} = {decision.Value} "
                              + "(symetrique de +5 cote X sur le meme arbre)");
        }
    }

    /// <summary>
    /// Reproductibilite a graine fixee : deux moteurs neufs, meme graine, meme budget,
    /// rendent le meme coup ET la meme valeur. Sans ce temoin, un resultat de tournoi
    /// ne serait pas rejouable -- et un echec ne pourrait pas etre distingue d'un
    /// tirage malheureux.
    /// </summary>
    [Fact]
    public void MctsIsReproducibleAtAFixedSeed()
    {
        ZeroSumTree game = ZeroSumTree.ForX("root")
            .Node("root", ("a", "na"), ("b", "nb"), ("c", "nc"))
            .Node("na", ("a1", "ta1"), ("a2", "ta2"))
            .Node("nb", ("b1", "tb1"), ("b2", "tb2"))
            .Node("nc", ("c1", "tc1"), ("c2", "tc2"))
            .Utility("ta1", 3).Utility("ta2", 8)
            .Utility("tb1", 6).Utility("tb2", 1)
            .Utility("tc1", 4).Utility("tc2", 7);

        var options = new MctsOptions { Iterations = 500, Seed = 2026 };
        AdversarialDecision<string> first = new MctsSearch<string, string, char>(game, options)
            .MakeDecision("root")!;
        AdversarialDecision<string> second = new MctsSearch<string, string, char>(game, options)
            .MakeDecision("root")!;

        Assert.Equal(first.Action, second.Action);
        Assert.Equal(first.Value, second.Value, 12);
        _output.WriteLine($"graine 2026 : {first.Action} = {first.Value} (rejoue a l'identique)");
    }

    /// <summary>
    /// Contrat de metriques : l'UCT ne coupe rien (<c>branchesPruned</c> reste a zero
    /// par construction) et developpe au moins la racine. Un temoin qui comparerait
    /// l'UCT a alpha-beta sur le compteur d'elagage mesurerait une constante du moteur,
    /// pas un resultat de recherche -- cette assertion fixe la lecture correcte.
    /// </summary>
    [Fact]
    public void MctsPrunesNothingAndExpandsAtLeastTheRoot()
    {
        ZeroSumTree game = ZeroSumTree.ForX("r")
            .Node("r", ("x", "tx"), ("y", "ty"))
            .Utility("tx", 3).Utility("ty", 7);

        MctsSearch<string, string, char> engine = new(game, new MctsOptions { Iterations = 100, Seed = 1 });
        engine.MakeDecision("r");

        Assert.Equal(0, engine.Metrics.PrunedBranches);
        Assert.True(engine.Metrics.ExpandedNodes >= 1, "la racine elle-meme n'a pas ete comptee");
        Assert.True(engine.Metrics.GeneratedActions >= 2,
            $"les deux coups de la racine n'ont pas ete engendres ({engine.Metrics.GeneratedActions})");

        IReadOnlyDictionary<string, string> map = engine.Metrics.AsMap();
        Assert.Equal("0", map["branchesPruned"]);
        _output.WriteLine($"metriques : {engine.Metrics.ExpandedNodes} noeuds, "
                          + $"{engine.Metrics.GeneratedActions} coups engendres, "
                          + $"{engine.Metrics.PrunedBranches} branches coupees");
    }

    /// <summary>
    /// Etat terminal ou sans coup legal : la decision est nulle, contrat de
    /// <see cref="IAdversarialSearch{TState, TAction, TPlayer}"/>.
    /// </summary>
    [Fact]
    public void MctsReturnsNullWhenNoLegalMoveExists()
    {
        ZeroSumTree game = ZeroSumTree.Terminal("fin", 3);
        MctsSearch<string, string, char> engine = new(game);

        Assert.Null(engine.MakeDecision("fin"));
        Assert.Equal(0, engine.Metrics.GeneratedActions);
    }

    /// <summary>
    /// Un budget nul n'est pas « une recherche tres courte », c'est l'absence de
    /// recherche : rendre un coup dans ce cas serait presenter le premier coup legal
    /// comme un choix. Le constructeur refuse plutot que de deguiser le vide.
    /// </summary>
    [Fact]
    public void MctsRefusesAZeroBudgetRatherThanDisguisingItAsAChoice()
    {
        ZeroSumTree game = ZeroSumTree.ForX("r")
            .Node("r", ("x", "tx"), ("y", "ty"))
            .Utility("tx", 3).Utility("ty", 7);

        Assert.Throws<ArgumentOutOfRangeException>(() =>
            new MctsSearch<string, string, char>(game, new MctsOptions { Iterations = 0 }));
        _output.WriteLine("budget nul : refus a la construction, pas de coup deguise");
    }

    /// <summary>
    /// Sur le Go 5x5, l'UCT rend un coup <b>legal</b> et se termine dans un budget
    /// borne. C'est le temoin de non-degenerescence minimal : la partie n'est pas
    /// resolue, le passe reste disponible, et le moteur doit choisir sans qu'aucune
    /// fin ne soit atteignable par epuisement des coups.
    /// </summary>
    [Fact]
    public void MctsPlaysALegalMoveOn5x5Go()
    {
        GoGameAdapter game = new(size: 5, komi: 0.5);
        MctsSearch<GoGame, GoPoint, GoColor> engine = new(
            game,
            new MctsOptions { Iterations = 200, Seed = 7 });

        AdversarialDecision<GoPoint> decision = engine.MakeDecision(game.InitialState)!;

        IReadOnlyList<GoPoint> legal = game.Actions(game.InitialState);
        Assert.Contains(decision.Action, legal);
        Assert.NotEqual(GoPoint.Pass, decision.Action);
        _output.WriteLine($"Go 5x5, 200 playouts : {decision.Action} "
                          + $"(valeur {decision.Value:F2}, {engine.Metrics.ExpandedNodes} noeuds, "
                          + $"profondeur {decision.Depth})");
    }
}
