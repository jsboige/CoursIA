using System.Diagnostics;
using MyIA.AI.Shared.Search.Adversarial;
using MyIA.AI.Shared.Search.Adversarial.Go;
using Xunit;
using Xunit.Abstractions;

namespace MyIA.AI.Shared.Tests.Search;

/// <summary>
/// Temoins de l'adaptateur IGame du Go (EPIC #7265, pepite B3, tranche 3).
///
/// Ce que chaque temoin doit attraper : une mutation partagee entre Result et son
/// origine (l'arbre de recherche corromprait le plateau en l'explorant), une
/// utilite non antisymetrique (l'hypothese somme nulle du contrat, celle qui donne
/// a l'elagage sa validite), un passe absent des actions (une partie sans coup
/// avantageux ne pourrait plus finir), et un moteur qui ne choisit pas la capture
/// evidente -- le minimum vital avant de parler d'evaluation.
/// </summary>
public sealed class GoGameAdapterTests
{
    private readonly ITestOutputHelper _output;

    public GoGameAdapterTests(ITestOutputHelper output) => _output = output;

    private static GoGameAdapter Adapter(int size = 5, double komi = 0.5) => new(size, komi);

    /// <summary>
    /// Position d'atari 5x5 : la chaine blanche {(1,1), (2,1)} ne respire plus que
    /// par (3,1). Noirs (0,1), (1,0), (2,0), (1,2), (2,2) ; blancs (1,1), (2,1),
    /// (4,4), (4,3), (3,4) ; noir au trait. La sequence alternante de pose est
    /// calme (aucune capture, aucun suicide).
    /// </summary>
    private static GoGame AtariPosition()
    {
        GoGame game = new(5, komi: 0);
        foreach ((int x, int y) in new[]
        {
            (0, 1), (1, 1), (1, 0), (2, 1), (2, 0), (4, 4), (1, 2), (4, 3), (2, 2), (3, 4),
        })
        {
            Assert.True(game.Play(new GoPoint(x, y)), $"pose setup ({x},{y})");
        }

        Assert.Equal(GoColor.Black, game.ToPlay);
        return game;
    }

    /// <summary>
    /// Position de ko 5x5 apres capture : noir (1,2) vient de prendre le blanc
    /// isole (1,1) en pierre isolee -- le point de ko est (1,1), un prisonnier
    /// blanc est compte, et c'est au blanc de jouer.
    /// </summary>
    private static GoGame KoAfterCapture()
    {
        GoGame game = new(5, komi: 0);
        foreach ((int x, int y) in new[]
        {
            (1, 0), (1, 1), (0, 1), (0, 2), (2, 1), (2, 2), (4, 0), (1, 3),
        })
        {
            Assert.True(game.Play(new GoPoint(x, y)), $"pose setup ({x},{y})");
        }

        Assert.True(game.Play(new GoPoint(1, 2)), "capture du ko");
        return game;
    }

    [Fact]
    public void EtatInitial_EstVideNoirAuTrait_EtOffreToutLePlateauPlusLePasse()
    {
        GoGameAdapter adapter = Adapter();

        GoGame initial = adapter.InitialState;

        Assert.Equal(5, initial.Size);
        Assert.Equal(0.5, initial.Komi);
        Assert.Equal(GoColor.Black, adapter.Player(initial));
        Assert.Equal(26, adapter.Actions(initial).Count);
        Assert.Equal(GoPoint.Pass, adapter.Actions(initial)[^1]);
        Assert.False(adapter.IsTerminal(initial));
    }

    [Fact]
    public void PartieFinie_NiActionsNiDecision()
    {
        GoGameAdapter adapter = Adapter();
        GoGame game = adapter.InitialState;
        Assert.True(game.Play(new GoPoint(0, 0)));
        Assert.True(game.Pass());
        Assert.True(game.Pass());

        Assert.True(adapter.IsTerminal(game));
        Assert.Empty(adapter.Actions(game));

        var engine = new IterativeDeepeningAlphaBetaSearch<GoGame, GoPoint, GoColor>(
            adapter, adapter.MinUtility, adapter.MaxUtility, 1.0, 3,
            GoGameAdapter.TerritoryHeuristic);
        Assert.Null(engine.MakeDecision(game));
    }

    [Fact]
    public void Result_EstUnClone_LOriginaleNeBougeJamais()
    {
        GoGameAdapter adapter = Adapter();
        GoGame original = AtariPosition();
        GoColor[] before = AllColors(original);
        int beforeCaptured = original.CapturedStones(GoColor.White);

        GoGame result = adapter.Result(original, new GoPoint(3, 1));

        // Explorer le resultat ne doit rien changer a l'originale : ni le plateau,
        // ni le trait, ni les prisonniers -- sinon l'arbre de recherche corromprait
        // la position qu'il explore.
        Assert.True(result.Play(new GoPoint(4, 0)));
        Assert.Equal(before, AllColors(original));
        Assert.Equal(GoColor.Black, original.ToPlay);
        Assert.Equal(beforeCaptured, original.CapturedStones(GoColor.White));
    }

    [Fact]
    public void Result_AppliqueLeCoupEtBasculeLeTrait()
    {
        GoGameAdapter adapter = Adapter();
        GoGame original = AtariPosition();

        GoGame result = adapter.Result(original, new GoPoint(3, 1));

        Assert.Equal(GoColor.Black, result.ColorAt(new GoPoint(3, 1)));
        Assert.Equal(GoColor.Empty, result.ColorAt(new GoPoint(1, 1)));
        Assert.Equal(GoColor.Empty, result.ColorAt(new GoPoint(2, 1)));
        Assert.Equal(2, result.CapturedStones(GoColor.White));
        Assert.Equal(GoColor.White, adapter.Player(result));
    }

    [Fact]
    public void Result_CoupIllegal_Leve()
    {
        GoGameAdapter adapter = Adapter();
        GoGame game = AtariPosition();

        Assert.Throws<InvalidOperationException>(
            () => adapter.Result(game, new GoPoint(1, 1)));
    }

    [Fact]
    public void UtiliteTerminale_EstLeScoreDeTerritoire_Antisymetrique()
    {
        GoGameAdapter adapter = Adapter();
        GoGame game = adapter.InitialState;
        Assert.True(game.Play(new GoPoint(0, 0)));
        Assert.True(game.Pass());
        Assert.True(game.Pass());

        // Une seule pierre noire et 24 vides bordes de noir seul : territoire
        // chinois 25 - 0, moins le komi 0.5. Le blanc voit l'oppose exact --
        // l'hypothese somme nulle que l'elagage suppose.
        Assert.Equal(24.5, adapter.Utility(game, GoColor.Black), 5);
        Assert.Equal(-24.5, adapter.Utility(game, GoColor.White), 5);
    }

    [Fact]
    public void Utilite_AntisymetriqueSurUnePartieEnCours()
    {
        GoGameAdapter adapter = Adapter();
        GoGame game = KoAfterCapture();

        double black = adapter.Utility(game, GoColor.Black);
        double white = adapter.Utility(game, GoColor.White);

        Assert.Equal(-black, white, 5);
    }

    [Fact]
    public void Clonage_Fidele_ToutLEtatDePartieSurvit()
    {
        GoGame game = KoAfterCapture();
        GoColor[] board = AllColors(game);

        GoGame clone = game.Clone();

        Assert.Equal(game.ToPlay, clone.ToPlay);
        Assert.Equal(game.IsOver, clone.IsOver);
        Assert.Equal(game.KoPoint, clone.KoPoint);
        Assert.Equal(game.CapturedStones(GoColor.White), clone.CapturedStones(GoColor.White));
        Assert.Equal(board, AllColors(clone));

        // Le clone est independent : jouer dessus ne touche pas l'original.
        Assert.True(clone.Play(new GoPoint(4, 4)));
        Assert.Equal(board, AllColors(game));
        Assert.NotEqual(board, AllColors(clone));
    }

    [Fact]
    public void ApprofondissementIteratif_ChoisitLaCaptureConfirmeeParEnumeration()
    {
        GoGameAdapter adapter = Adapter();
        GoGame game = AtariPosition();
        var engine = new IterativeDeepeningAlphaBetaSearch<GoGame, GoPoint, GoColor>(
            adapter, adapter.MinUtility, adapter.MaxUtility, 30.0, 3,
            GoGameAdapter.TerritoryHeuristic);

        AdversarialDecision<GoPoint>? decision = engine.MakeDecision(game);

        Assert.NotNull(decision);

        // Controle par enumeration directe a profondeur 1 : la meme heuristique,
        // appliquee coup par coup, doit designer la capture comme strictement
        // meilleure -- le moteur n'a pas le droit de la manquer a sa profondeur.
        GoPoint expected = default;
        double best = double.NegativeInfinity;
        foreach (GoPoint action in adapter.Actions(game))
        {
            double value = GoGameAdapter.TerritoryHeuristic(
                adapter.Result(game, action), GoColor.Black);
            if (value > best)
            {
                best = value;
                expected = action;
            }
        }

        _output.WriteLine($"enumeration p1 : meilleur {expected} = {best}");
        Assert.Equal(new GoPoint(3, 1), expected);
        Assert.Equal(new GoPoint(3, 1), decision!.Action);
        _output.WriteLine(
            $"decision p3 : {decision.Action} valeur {decision.Value} "
            + $"({decision.Metrics.AsMap()["nodesExpanded"]} noeuds, "
            + $"{decision.Metrics.PrunedBranches} elagues)");
    }

    [Fact]
    public void ApprofondissementIteratif_EstDeterministe()
    {
        GoGameAdapter adapter = Adapter();
        GoGame game = AtariPosition();
        var engine = new IterativeDeepeningAlphaBetaSearch<GoGame, GoPoint, GoColor>(
            adapter, adapter.MinUtility, adapter.MaxUtility, 30.0, 2,
            GoGameAdapter.TerritoryHeuristic);

        AdversarialDecision<GoPoint>? first = engine.MakeDecision(game);
        AdversarialDecision<GoPoint>? second = engine.MakeDecision(game);

        Assert.NotNull(first);
        Assert.NotNull(second);
        Assert.Equal(first!.Action, second!.Action);
        Assert.Equal(first.Value, second.Value, 5);
        Assert.Equal(first.Depth, second.Depth);
    }

    [Fact]
    public void Elagage_EngageEtSeCompte()
    {
        GoGameAdapter adapter = Adapter();
        GoGame game = AtariPosition();
        var engine = new IterativeDeepeningAlphaBetaSearch<GoGame, GoPoint, GoColor>(
            adapter, adapter.MinUtility, adapter.MaxUtility, 30.0, 3,
            GoGameAdapter.TerritoryHeuristic);

        AdversarialDecision<GoPoint>? decision = engine.MakeDecision(game);

        Assert.NotNull(decision);
        Assert.True(decision!.Metrics.PrunedBranches > 0,
            "aucune branche elaguee : le compteur d'elagage ne mesure rien");
        Assert.True(decision.Metrics.MaxDepthReached >= 3);
    }

    /// <summary>
    /// Temoin du cout du flood-fill promis par la tranche 2 : plateau 9x9 apres
    /// quelques coups, approfondissement borne a 2 palliers. Ce temoin n'asserte
    /// pas de duree (une horloge ne se temoinne pas) -- il imprime les compteurs
    /// et le temps, pour le corps de PR ; une future structure incrementelle
    /// devra battre ce chiffre a palliers egaux.
    /// </summary>
    [Fact]
    public void CoutFloodFill_Temoin9x9_CompteursImpress()
    {
        GoGameAdapter adapter = new(9, komi: 7.5);
        GoGame game = adapter.InitialState;
        foreach ((int x, int y) in new[]
        {
            (2, 2), (6, 6), (4, 4), (4, 3), (2, 6), (6, 2),
        })
        {
            Assert.True(game.Play(new GoPoint(x, y)));
        }

        var engine = new IterativeDeepeningAlphaBetaSearch<GoGame, GoPoint, GoColor>(
            adapter, adapter.MinUtility, adapter.MaxUtility, 60.0, 2,
            GoGameAdapter.TerritoryHeuristic);

        Stopwatch clock = Stopwatch.StartNew();
        AdversarialDecision<GoPoint>? decision = engine.MakeDecision(game);
        clock.Stop();

        Assert.NotNull(decision);
        _output.WriteLine(
            $"9x9 p2 : {decision!.Action} en {clock.ElapsedMilliseconds} ms -- "
            + string.Join(", ", decision.Metrics.AsMap().Select(kv => $"{kv.Key}={kv.Value}")));
        Assert.True(decision.Metrics.ExpandedNodes > 0);
    }

    private static GoColor[] AllColors(GoGame game)
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
