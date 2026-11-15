using MyIA.AI.Shared.Search.Adversarial;
using MyIA.AI.Shared.Search.Adversarial.Go;
using Xunit;
using Xunit.Abstractions;

namespace MyIA.AI.Shared.Tests.Search;

/// <summary>
/// Temoins de la recherche arborescente Monte-Carlo parallele (EPIC #7265, pepite B3,
/// tranche 9).
///
/// Ce qui se temoigne ici est ce qui distingue un arbre partage d'un moteur casse
/// par la concurrence : la conservation exacte du budget (chaque playout, quel que
/// soit l'ouvrier, remonte jusqu'a la racine), la reproductibilite au degre un (le
/// mode qui doit rester equivalent au sequentiel de la tranche 6), la survivance de
/// la bascule max/min sous parallelisme (le defaut de signe de la tranche 6 etait
/// silencieux -- il l'est encore plus ici), et l'absence d'echec sur le vrai
/// adaptateur Go concurremment lu. Les temoins sont volontairement exempts de
/// mesure de temps : une assertion de duree serait flaky en CI, et le gain de
/// parallelisme se mesure dans le corps de la tranche, pas dans un temoin.
/// </summary>
public sealed class ParallelMctsSearchWitnessTests
{
    private readonly ITestOutputHelper _output;

    public ParallelMctsSearchWitnessTests(ITestOutputHelper output) => _output = output;

    /// <summary>
    /// Graines balayees par les temoins stochastiques. Le balayage n'est pas
    /// decoratif -- la mesure de la tranche 6 a montre qu'un defaut de selection
    /// passe a certaines graines et echoue a d'autres ; un temoin a graine unique
    /// peut passer par chance sur un moteur casse.
    /// </summary>
    private static readonly int[] Seeds = [1, 7, 42, 99];

    /// <summary>
    /// Arbre de jeu explicite a somme nulle, construit entierement avant la
    /// recherche : les lectures concurrentes des dictionnaires (uniquement des
    /// lectures, l'arbre ne grandit pas) sont ce que le moteur attend du contrat
    /// <see cref="IGame{TState, TAction, TPlayer}"/> en mode parallele.
    /// </summary>
    private sealed class ZeroSumTree : IGame<string, string, char>
    {
        private readonly Dictionary<string, string[]> _actions = new();
        private readonly Dictionary<(string State, string Action), string> _result = new();
        private readonly Dictionary<string, char> _turn = new();
        private readonly Dictionary<string, double> _utilityX = new();
        private readonly string _initial;

        private ZeroSumTree(string initial)
        {
            _initial = initial;
        }

        public static ZeroSumTree Root(string state, char firstPlayer)
        {
            ZeroSumTree tree = new(state);
            tree._turn[state] = firstPlayer;
            return tree;
        }

        /// <summary>Declare les coups d'un noeud ; les tours des enfants alternent.</summary>
        public ZeroSumTree Node(string state, params (string Action, string Child, double UtilityX)[] children)
        {
            _actions[state] = children.Select(child => child.Action).ToArray();
            foreach ((string action, string child, double utilityX) in children)
            {
                _result[(state, action)] = child;
                _utilityX[child] = utilityX;
                _turn[child] = _turn[state] == 'X' ? 'O' : 'X';
            }

            return this;
        }

        public string InitialState => _initial;

        public char Player(string state) => _turn[state];

        public IReadOnlyList<string> Actions(string state) =>
            _actions.TryGetValue(state, out string[]? actions) ? actions : [];

        public string Result(string state, string action) => _result[(state, action)];

        public bool IsTerminal(string state) => !_actions.ContainsKey(state);

        public double Utility(string state, char player) =>
            player == 'X' ? _utilityX[state] : -_utilityX[state];
    }

    /// <summary>
    /// Au degre un, le moteur est deterministe : deux decisions de suite, meme graine,
    /// rendent le meme coup ET les memes compteurs. C'est la propriete qui garde le
    /// moteur parallele comparable au sequentiel de la tranche 6 -- et celle que la
    /// derivation de la graine par identifiant de thread casserait (un identifiant de
    /// thread n'est pas stable entre deux executions ; l'index d'ouvrier, si).
    /// </summary>
    [Fact]
    public void AuDegreUnLeMoteurEstReproductibleEntreDeuxExecutions()
    {
        var game = new GoGameAdapter(size: 9);
        var options = new ParallelMctsOptions { Iterations = 240, Seed = 42, DegreeOfParallelism = 1 };

        var firstEngine = new ParallelMctsSearch<GoGame, GoPoint, GoColor>(game, options);
        AdversarialDecision<GoPoint>? first = firstEngine.MakeDecision(game.InitialState);
        var secondEngine = new ParallelMctsSearch<GoGame, GoPoint, GoColor>(game, options);
        AdversarialDecision<GoPoint>? second = secondEngine.MakeDecision(game.InitialState);

        Assert.NotNull(first);
        Assert.NotNull(second);
        Assert.Equal(first!.Action, second!.Action);
        Assert.Equal(first.Value, second.Value, precision: 10);
        Assert.Equal(first.Metrics.ExpandedNodes, second.Metrics.ExpandedNodes);
        Assert.Equal(first.Metrics.GeneratedActions, second.Metrics.GeneratedActions);
        Assert.Equal(first.Metrics.MaxDepthReached, second.Metrics.MaxDepthReached);
        Assert.Equal(first.Depth, second.Depth);
    }

    /// <summary>
    /// Conservation du budget au degre un : la racine recoit exactement une visite par
    /// playout revendique.
    /// </summary>
    [Fact]
    public void AuDegreUnLeBudgetEstExactementConsomme()
    {
        var engine = new ParallelMctsSearch<string, string, char>(
            ForcedWinTree(), new ParallelMctsOptions { Iterations = 173, Seed = 42, DegreeOfParallelism = 1 });

        engine.MakeDecision("R");

        Assert.Equal(173, engine.RootVisits);
    }

    /// <summary>
    /// Conservation du budget en parallele : quatre ouvriers qui se disputent un
    /// compteur de revendication doivent, au total, consommer exactement le budget.
    /// Une revendication perdue (decrement sans playout) ou une retropropagation
    /// interrompue se lirait ici immediatement.
    /// </summary>
    [Theory]
    [MemberData(nameof(SeedData))]
    public void EnParalleleLeBudgetEstExactementConsomme(int seed)
    {
        var engine = new ParallelMctsSearch<string, string, char>(
            ForcedWinTree(), new ParallelMctsOptions { Iterations = 997, Seed = seed, DegreeOfParallelism = 4 });

        engine.MakeDecision("R");

        Assert.Equal(997, engine.RootVisits);
    }

    /// <summary>
    /// Un coup force reste force en parallele : sur une position ou un seul coup gagne
    /// et tous les autres perdent, quatre ouvriers convergent vers le meme coup que le
    /// mode sequentiel. C'est la propriete « arbre partage, pas vote d'arbres » : le
    /// budget commun achete de la profondeur commune, pas N opinions redondantes.
    /// </summary>
    [Theory]
    [MemberData(nameof(SeedData))]
    public void LeCoupForceResteForceEnParallele(int seed)
    {
        ZeroSumTree game = ForcedWinTree();
        var options = new ParallelMctsOptions { Iterations = 300, Seed = seed };

        var sequential = new ParallelMctsSearch<string, string, char>(
            game, options with { DegreeOfParallelism = 1 }).MakeDecision("R");
        var parallel = new ParallelMctsSearch<string, string, char>(
            game, options with { DegreeOfParallelism = 4 }).MakeDecision("R");

        Assert.NotNull(sequential);
        Assert.NotNull(parallel);
        Assert.Equal("a", sequential!.Action);
        Assert.Equal("a", parallel!.Action);
    }

    /// <summary>
    /// La bascule max/min survit au parallelisme. La position est le piege de la
    /// tranche 6 : apres « right », l'adversaire O choisit entre -2 et +5 pour X et
    /// prend -2 ; apres « left », il choisit entre -10 et +8 et prend -10. Le coup
    /// correct est donc « right » (-2 domine -10). Un moteur qui maximiserait partout
    /// -- le defaut de signe silencieux -- lirait +8 derriere « left » et choisirait
    /// « left ». Le meme piege, pose au mode parallele, doit rendre le meme verdict
    /// qu'au mode sequentiel, a toutes les graines balayees.
    /// </summary>
    [Theory]
    [MemberData(nameof(SeedData))]
    public void LaBasculeMaxMinSurvitAuParallelisme(int seed)
    {
        ZeroSumTree game = BasculeTrapTree();
        var options = new ParallelMctsOptions { Iterations = 400, Seed = seed };

        var sequential = new ParallelMctsSearch<string, string, char>(
            game, options with { DegreeOfParallelism = 1 }).MakeDecision("R");
        var parallel = new ParallelMctsSearch<string, string, char>(
            game, options with { DegreeOfParallelism = 4 }).MakeDecision("R");

        Assert.NotNull(sequential);
        Assert.NotNull(parallel);
        Assert.Equal("right", sequential!.Action);
        Assert.Equal("right", parallel!.Action);
    }

    /// <summary>
    /// Fume sur le vrai adaptateur Go, lu concurremment par quatre ouvriers : la
    /// decision rend un coup legal et le budget est exactement consomme. Ce temoin
    /// n'affirme pas QUEL coup : au-dela du degre un, l'entrelacement des ouvriers
    /// rend l'arbre non reproductible, et c'est documente comme le comportement
    /// attendu -- ce qui se temoigne est l'absence d'echec (course, exception,
    /// budget perdu), pas une identite d'arbre.
    /// </summary>
    [Fact]
    public void GoNeufSurNeufTientQuatreOuvriersSansEchecNiPerteDeBudget()
    {
        var game = new GoGameAdapter(size: 9);
        var engine = new ParallelMctsSearch<GoGame, GoPoint, GoColor>(
            game, new ParallelMctsOptions { Iterations = 240, Seed = 7, DegreeOfParallelism = 4 });

        GoGame initial = game.InitialState;
        AdversarialDecision<GoPoint>? decision = engine.MakeDecision(initial);

        Assert.NotNull(decision);
        Assert.Contains(decision!.Action, game.Actions(initial));
        Assert.Equal(240, engine.RootVisits);
        _output.WriteLine($"decision={decision.Action} rootVisits={engine.RootVisits} expanded={engine.Metrics.ExpandedNodes}");
    }

    /// <summary>
    /// Les reglages vides sont refuses nommement : une iteration nulle rendrait le
    /// premier coup legal deguise en decision, un degre nul ne consommerait aucun
    /// playout, un plafond de playout nul ne terminerait jamais.
    /// </summary>
    [Fact]
    public void LesReglagesVidesSontRefusesNommement()
    {
        var game = ForcedWinTree();

        Assert.Throws<ArgumentOutOfRangeException>(() => new ParallelMctsSearch<string, string, char>(
            game, new ParallelMctsOptions { Iterations = 0 }));
        Assert.Throws<ArgumentOutOfRangeException>(() => new ParallelMctsSearch<string, string, char>(
            game, new ParallelMctsOptions { DegreeOfParallelism = 0 }));
        Assert.Throws<ArgumentOutOfRangeException>(() => new ParallelMctsSearch<string, string, char>(
            game, new ParallelMctsOptions { MaxPlayoutDepth = 0 }));
    }

    /// <summary>Un etat sans coup legal rend une decision nulle, budget intact.</summary>
    [Fact]
    public void LEtatSansCoupRendUneDecisionNulle()
    {
        ZeroSumTree terminal = ZeroSumTree.Root("END", 'X');
        var engine = new ParallelMctsSearch<string, string, char>(
            terminal, new ParallelMctsOptions { Iterations = 50, Seed = 1 });

        Assert.Null(engine.MakeDecision("END"));
        Assert.Equal(0, engine.RootVisits);
    }

    public static TheoryData<int> SeedData => new(Seeds);

    /// <summary>Position a coup force : « a » gagne, « b » et « c » perdent.</summary>
    private static ZeroSumTree ForcedWinTree() => ZeroSumTree.Root("R", 'X')
        .Node("R", ("a", "WIN", 1.0), ("b", "L1", -1.0), ("c", "L2", -1.0));

    /// <summary>Position du piege de bascule : « right » (-2 force par O) domine « left » (-10 force par O).</summary>
    private static ZeroSumTree BasculeTrapTree() => ZeroSumTree.Root("R", 'X')
        .Node("R", ("left", "L", 0.0), ("right", "M", 0.0))
        .Node("L", ("La", "LaT", -10.0), ("Lb", "LbT", 8.0))
        .Node("M", ("Ma", "MaT", -2.0), ("Mb", "MbT", 5.0));
}
