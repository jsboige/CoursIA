using MyIA.AI.Shared.Search.Adversarial;
using MyIA.AI.Shared.Search.Adversarial.Go;
using Xunit;
using Xunit.Abstractions;

namespace MyIA.AI.Shared.Tests.Search;

/// <summary>
/// Temoins du resign Go (EPIC #7265, pepite B3, tranche 10).
///
/// Le resign est une fin de partie par renonciation, pas un coup de plateau :
/// ces temoins severent les trois plans qui se confondent sinon — le plateau ne
/// bouge pas, la partie devient terminale avec un vainqueur nomme, et l'utilite
/// de l'adaptateur reste antisymetrique (hypothese somme nulle du contrat
/// IGame). Le clonage et l'ordre des actions completent la garde : un resign
/// oublie au Clone rouvrirait une partie rendue, et un resign absent des
/// actions laisserait l'arbre de recherche muet sur la concession.
/// </summary>
public sealed class GoGameResignTests
{
    private readonly ITestOutputHelper _output;

    public GoGameResignTests(ITestOutputHelper output) => _output = output;

    private static GoPoint P(int x, int y) => new(x, y);

    [Fact]
    public void Resign_TermineLaPartieSansToucherAuPlateau()
    {
        GoGame game = new(size: 5, komi: 0);
        Assert.True(game.Play(P(2, 2), GoColor.Black));
        GoColor[] boardBefore = Snapshot(game);

        Assert.True(game.Resign());

        Assert.True(game.IsOver);
        Assert.Equal(GoColor.White, game.ResignedBy);
        Assert.Equal(GoColor.Black, game.Winner);
        Assert.Equal(boardBefore, Snapshot(game));
        Assert.Equal(0, game.CapturedStones(GoColor.Black));
        Assert.Equal(0, game.CapturedStones(GoColor.White));
        _output.WriteLine("blanc abandonne : plateau intact, noir vainqueur par renonciation");
    }

    [Fact]
    public void Resign_SuitLAlternanceEtRefuseApresLaFin()
    {
        GoGame game = new(size: 5, komi: 0);

        // Noir vient de jouer : c'est au blanc d'abandonner.
        Assert.True(game.Play(P(2, 2), GoColor.Black));
        Assert.False(game.IsLegal(GoPoint.Resign, GoColor.Black));
        Assert.True(game.IsLegal(GoPoint.Resign, GoColor.White));

        Assert.True(game.Resign());

        // Partie rendue : plus aucune action, meme pas un second abandon.
        Assert.False(game.IsLegal(GoPoint.Resign, GoColor.Black));
        Assert.False(game.Resign());
        Assert.False(game.IsLegal(GoPoint.Pass, GoColor.Black));
        _output.WriteLine("abandon : alternation stricte tenue, partie gelee");
    }

    [Fact]
    public void Resign_SurvitAuClonage()
    {
        GoGame game = new(size: 5, komi: 0);
        Assert.True(game.Play(P(2, 2), GoColor.Black));
        Assert.True(game.Resign());

        GoGame clone = game.Clone();

        Assert.True(clone.IsOver);
        Assert.Equal(game.ResignedBy, clone.ResignedBy);
        Assert.Equal(game.Winner, clone.Winner);
        Assert.False(clone.IsLegal(P(0, 0), GoColor.Black));
        _output.WriteLine("clone d'une partie rendue : vainqueur et gel conserves");
    }

    [Fact]
    public void Adaptateur_ExposeLeResignAvantLePasse()
    {
        GoGameAdapter adapter = new(5, komi: 0.5);
        GoGame initial = adapter.InitialState;

        IReadOnlyList<GoPoint> actions = adapter.Actions(initial);

        Assert.Equal(27, actions.Count);
        Assert.Equal(GoPoint.Resign, actions[^2]);
        Assert.Equal(GoPoint.Pass, actions[^1]);
        Assert.True(initial.IsLegal(GoPoint.Resign));
    }

    [Fact]
    public void Adaptateur_Result_RendLaPartieTerminaleEtVide()
    {
        GoGameAdapter adapter = new(5, komi: 0.5);
        GoGame initial = adapter.InitialState;

        GoGame resigned = adapter.Result(initial, GoPoint.Resign);

        Assert.True(adapter.IsTerminal(resigned));
        Assert.Empty(adapter.Actions(resigned));
        Assert.Equal(GoColor.Black, resigned.ResignedBy);
        Assert.Equal(GoColor.White, resigned.Winner);
        Assert.False(initial.IsOver);
    }

    [Fact]
    public void Adaptateur_Utilite_AbandonAntisymetriqueEtBornee()
    {
        GoGameAdapter adapter = new(5, komi: 0.5);
        GoGame resigned = adapter.Result(adapter.InitialState, GoPoint.Resign);

        double black = adapter.Utility(resigned, GoColor.Black);
        double white = adapter.Utility(resigned, GoColor.White);

        Assert.Equal(adapter.MinUtility, black, 5);
        Assert.Equal(adapter.MaxUtility, white, 5);
        Assert.Equal(-black, white, 5);
        _output.WriteLine($"noir abandonne : noir {black}, blanc {white} — antisymetrie exacte");
    }

    [Fact]
    public void Adaptateur_MoteurBorne_NeChoisitJamaisLAbandonSurPlateauVide()
    {
        GoGameAdapter adapter = new(5, komi: 0.5);
        var engine = new IterativeDeepeningAlphaBetaSearch<GoGame, GoPoint, GoColor>(
            adapter, adapter.MinUtility, adapter.MaxUtility, 10.0, 2,
            GoGameAdapter.TerritoryHeuristic);

        AdversarialDecision<GoPoint>? decision = engine.MakeDecision(adapter.InitialState);

        Assert.NotNull(decision);
        Assert.NotEqual(GoPoint.Resign, decision!.Action);
        _output.WriteLine($"decision p2 sur plateau vide : {decision.Action} (le resign est domine)");
    }

    private static GoColor[] Snapshot(GoGame game)
    {
        GoColor[] colors = new GoColor[game.Size * game.Size];
        for (int y = 0; y < game.Size; y++)
        {
            for (int x = 0; x < game.Size; x++)
            {
                colors[y * game.Size + x] = game.ColorAt(new GoPoint(x, y));
            }
        }

        return colors;
    }
}
