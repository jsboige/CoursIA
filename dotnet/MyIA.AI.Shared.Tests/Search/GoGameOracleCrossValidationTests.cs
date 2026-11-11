using System.Text.Json;
using System.Text.Json.Serialization;
using MyIA.AI.Shared.Search.Adversarial.Go;
using Xunit;
using Xunit.Abstractions;

namespace MyIA.AI.Shared.Tests.Search;

/// <summary>
/// Validation croisee du moteur de regles du Go contre DEUX oracles
/// independants (EPIC #7265, pepite B3, tranche 2b).
///
/// La fixture <c>Search/Go/oracles/go_oracle_fixture.json</c> est produite par
/// <c>generate_go_oracle_fixture.py</c> : douze parties aleatoires seedees sur
/// 5x5 et 7x7, dont chaque coup porte le verdict de legalite de pyspiel
/// (OpenSpiel) et l'acceptation de gnugo 3.8, chaque etat sonde porte le refus
/// des deux, et chaque fin porte le plateau des deux moteurs, les captures
/// comptees par gnugo et le vainqueur pyspiel.
///
/// Le moteur maison rejoue les memes sequences et doit s'accorder sur tout :
/// legalite coup par coup, refus des coups illlegaux, plateau final pierre a
/// pierre, captures par couleur, et signe du score sur les positions
/// terminales. C'est le temoin negatif que la tranche 2 ne pouvait pas
/// fournir seule : un moteur qui s'accorde avec lui-meme ne prouve rien.
/// </summary>
public sealed class GoGameOracleCrossValidationTests
{
    private static readonly Fixture Data = Fixture.Load();

    private readonly ITestOutputHelper _output;

    public GoGameOracleCrossValidationTests(ITestOutputHelper output) => _output = output;

    public static IEnumerable<object[]> SequenceIndices() =>
        Enumerable.Range(0, Data.Sequences.Count).Select(i => new object[] { i });

    private static GoColor ColorOf(string name) => name switch
    {
        "black" => GoColor.Black,
        "white" => GoColor.White,
        _ => throw new InvalidOperationException($"couleur inconnue : {name}"),
    };

    private static GoColor CharOf(char cell) => cell switch
    {
        'X' => GoColor.Black,
        'O' => GoColor.White,
        _ => GoColor.Empty,
    };

    private static GoPoint PointOf(int x, int y) => x < 0 ? GoPoint.Pass : new GoPoint(x, y);

    private static void AssertProbesAt(GoGame go, Sequence seq, int afterMoves)
    {
        foreach (Probe probe in seq.Probes.Where(p => p.AfterMoves == afterMoves))
        {
            GoPoint p = PointOf(probe.X, probe.Y);
            GoColor color = ColorOf(probe.Color);

            // Les deux oracles refusent ce coup -- le moteur doit le refuser
            // aussi, et le refus ne consomme pas le tour.
            Assert.False(probe.PyspielLegal, "la fixture ne sonde que des coups non legaux");
            Assert.False(go.IsLegal(p, color));
            Assert.False(go.Play(p, color));
            Assert.Equal(color, go.ToPlay);
        }
    }

    /// <summary>
    /// Rejoue une sequence entiere : chaque coup joue par les deux oracles est
    /// accepte, chaque coup sonde non legal est refuse, et l'alternance stricte
    /// du moteur tient a chaque etape (elle-meme un temoin).
    /// </summary>
    [Theory]
    [MemberData(nameof(SequenceIndices))]
    public void EveryMoveAndRefusalAgreesWithBothOracles(int index)
    {
        Sequence seq = Data.Sequences[index];
        GoGame go = new(seq.BoardSize, seq.Komi);
        GoColor expected = GoColor.Black;

        AssertProbesAt(go, seq, 0);

        int played = 0;
        foreach (Move move in seq.Moves)
        {
            GoColor color = ColorOf(move.Color);
            Assert.Equal(expected, go.ToPlay);
            Assert.True(move.PyspielLegal && move.GnugoLegal);

            Assert.True(go.Play(PointOf(move.X, move.Y), color),
                $"coup {played + 1} refuse par GoGame : ({move.X},{move.Y}) {move.Color}");

            expected = color.Opposite();
            played++;
            AssertProbesAt(go, seq, played);
        }

        _output.WriteLine($"{seq.BoardSize}x{seq.BoardSize} seed={seq.Seed} : "
                          + $"{played} coups, {seq.Probes.Count} refus concordants");
    }

    /// <summary>
    /// Le plateau final doit etre identique pierre a pierre a celui des deux
    /// oracles (ils concordent entre eux, la fixture le porte : c'est la
    /// validation des captures, qui ne se lisent qu'en creux).
    /// </summary>
    [Theory]
    [MemberData(nameof(SequenceIndices))]
    public void FinalBoardMatchesBothOraclesStoneForStone(int index)
    {
        Sequence seq = Data.Sequences[index];
        GoGame go = new(seq.BoardSize, seq.Komi);
        foreach (Move move in seq.Moves)
        {
            Assert.True(go.Play(PointOf(move.X, move.Y), ColorOf(move.Color)));
        }

        Assert.True(seq.Final.BoardAgree, "pyspiel et gnugo doivent concorder avant d'accuser GoGame");
        for (int y = 0; y < seq.BoardSize; y++)
        {
            for (int x = 0; x < seq.BoardSize; x++)
            {
                Assert.Equal(CharOf(seq.Final.PyspielBoard[y][x]), go.ColorAt(new GoPoint(x, y)));
            }
        }

        _output.WriteLine($"{seq.BoardSize}x{seq.BoardSize} seed={seq.Seed} : plateau concordant");
    }

    /// <summary>
    /// Les prisonniers comptes par gnugo doivent egalement tomber juste, par
    /// couleur : gnugo nomme qui a capture, le moteur compte les prisonniers
    /// de chaque couleur.
    /// </summary>
    [Theory]
    [MemberData(nameof(SequenceIndices))]
    public void PrisonerCountsMatchGnuGo(int index)
    {
        Sequence seq = Data.Sequences[index];
        GoGame go = new(seq.BoardSize, seq.Komi);
        foreach (Move move in seq.Moves)
        {
            Assert.True(go.Play(PointOf(move.X, move.Y), ColorOf(move.Color)));
        }

        // gnugo : "WHITE has captured N" = N pierres NOIRES prisonnieres.
        Assert.Equal(seq.Final.GnugoWhiteCaptures, go.CapturedStones(GoColor.Black));
        Assert.Equal(seq.Final.GnugoBlackCaptures, go.CapturedStones(GoColor.White));

        _output.WriteLine($"{seq.BoardSize}x{seq.BoardSize} seed={seq.Seed} : "
                          + $"prisonniers noir/blanc = {go.CapturedStones(GoColor.Black)}"
                          + $"/{go.CapturedStones(GoColor.White)}");
    }

    /// <summary>
    /// Sur une position terminale, le vainqueur de pyspiel (score Tromp-Taylor,
    /// sans detection de vie/morte) doit tomber du meme cote que le signe du
    /// score de territoire du moteur. Le score chiffre de gnugo n'est PAS
    /// asserte : il applique une detection de vie/morte et diverge legitimement
    /// sur des plateaux aleatoires -- la fixture porte ces valeurs en
    /// information, pas en attendu.
    /// </summary>
    [Theory]
    [MemberData(nameof(SequenceIndices))]
    public void TerminalScoreSignMatchesPyspielWinner(int index)
    {
        Sequence seq = Data.Sequences[index];
        GoGame go = new(seq.BoardSize, seq.Komi);
        foreach (Move move in seq.Moves)
        {
            Assert.True(go.Play(PointOf(move.X, move.Y), ColorOf(move.Color)));
        }

        if (!seq.Final.Terminal || seq.Final.PyspielWinner is null)
        {
            _output.WriteLine($"{seq.BoardSize}x{seq.BoardSize} seed={seq.Seed} : non terminale, signe non asserte");
            return;
        }

        double score = go.AreaScore();
        if (seq.Final.PyspielWinner == "black")
        {
            Assert.True(score >= 0, $"pyspiel donne noir vainqueur, score={score}");
        }
        else
        {
            Assert.True(score <= 0, $"pyspiel donne blanc vainqueur, score={score}");
        }

        _output.WriteLine($"{seq.BoardSize}x{seq.BoardSize} seed={seq.Seed} : "
                          + $"vainqueur {seq.Final.PyspielWinner}, score={score} "
                          + $"(gnugo : {seq.Final.GnugoFinalScore})");
    }

    /// <summary>
    /// Garde de la fixture elle-meme : les oracles doivent concorder entre eux
    /// (sinon la fixture ne vaut rien), et la suite doit mordre -- des captures
    /// reelles, des positions terminales et non terminales.
    /// </summary>
    [Fact]
    public void FixtureIsSoundAndDiscriminating()
    {
        Assert.Equal(0, Data.Meta.Divergences.GnugoRefusedPlayedMove);
        Assert.Equal(0, Data.Meta.Divergences.BoardMismatchAtEnd);
        Assert.All(Data.Sequences, s => Assert.True(s.Final.BoardAgree));
        Assert.True(Data.Sequences.Count >= 10);

        int totalPrisoners = Data.Sequences.Sum(
            s => s.Final.GnugoWhiteCaptures + s.Final.GnugoBlackCaptures);
        Assert.True(totalPrisoners > 0, "la fixture doit contenir de vraies captures");
        Assert.Contains(Data.Sequences, s => s.Final.Terminal);
        Assert.Contains(Data.Sequences, s => !s.Final.Terminal);

        _output.WriteLine($"fixture : {Data.Sequences.Count} sequences, "
                          + $"{totalPrisoners} prisonniers, oracles concordants");
    }

    // ------------------------------------------------------------------
    // Chargement de la fixture (meme schema que le generateur python).
    // On ne mappe que les champs lus : le reste du JSON est ignore.
    // ------------------------------------------------------------------

    private sealed record Fixture(Meta Meta, List<Sequence> Sequences)
    {
        private static readonly JsonSerializerOptions Options = new()
        {
            PropertyNamingPolicy = JsonNamingPolicy.SnakeCaseLower,
            PropertyNameCaseInsensitive = false,
        };

        public static Fixture Load()
        {
            string path = Path.Combine(
                AppContext.BaseDirectory, "Search", "Go", "oracles", "go_oracle_fixture.json");
            if (!File.Exists(path))
            {
                throw new FileNotFoundException(
                    "fixture de validation croisee absente -- regenerer via "
                    + "Search/Go/oracles/generate_go_oracle_fixture.py", path);
            }

            return JsonSerializer.Deserialize<Fixture>(File.ReadAllText(path), Options)
                   ?? throw new InvalidOperationException($"fixture illisible : {path}");
        }
    }

    private sealed record Meta(Divergences Divergences);

    private sealed record Divergences(int GnugoRefusedPlayedMove, int BoardMismatchAtEnd);

    private sealed record Sequence(
        int BoardSize,
        double Komi,
        int Seed,
        List<Move> Moves,
        List<Probe> Probes,
        Final Final);

    private sealed record Move(int X, int Y, string Color, bool PyspielLegal, bool GnugoLegal);

    private sealed record Probe(int X, int Y, int AfterMoves, string Color, bool PyspielLegal);

    private sealed record Final(
        bool Terminal,
        List<string> PyspielBoard,
        List<string> GnugoBoard,
        int GnugoWhiteCaptures,
        int GnugoBlackCaptures,
        bool BoardAgree,
        [property: JsonPropertyName("pyspiel_winner")] string? PyspielWinner,
        string? GnugoFinalScore);
}
