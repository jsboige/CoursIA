using System.Text.Json;
using System.Text.Json.Serialization;
using Microsoft.ML.OnnxRuntime.Tensors;
using MyIA.AI.Shared.Search.Adversarial.Go;
using Xunit;
using Xunit.Abstractions;

namespace MyIA.AI.Shared.Tests.Search;

/// <summary>
/// Temoins de l'evaluation Go apprise voie ONNX (EPIC #7265, pepite B3, tranche 8).
/// La fixture <c>Search/Go/oracles/go_eval_onnx_expected.json</c> est produite par
/// <c>train_go_eval_onnx.py</c> : positions relevees sur une partie sonde pyspiel
/// hors des jeux d'entrainement, sorties attendues calculees par ONNX Runtime
/// lui-meme sur le modele exporte. Le rejouer ici prouve que la consommation C#
/// (construction du tenseur + inference) est bit-compatible avec la generation --
/// c'est la parite d'orientation GoPoint -> reseau qui est a l'epreuve.
/// </summary>
public sealed class GoOnnxEvaluationWitnessTests : IDisposable
{
    private readonly ITestOutputHelper _output;
    private readonly GoOnnxEvaluation _eval;
    private readonly Manifest _manifest;

    public GoOnnxEvaluationWitnessTests(ITestOutputHelper output)
    {
        _output = output;
        string modelPath = Path.Combine(
            AppContext.BaseDirectory, "Search", "Go", "oracles", "go_eval_9x9_v1.onnx");
        if (!File.Exists(modelPath))
        {
            throw new FileNotFoundException(
                "modele ONNX absent -- regenerer via "
                + "Search/Go/oracles/train_go_eval_onnx.py", modelPath);
        }

        _eval = new GoOnnxEvaluation(modelPath);
        _manifest = Manifest.Load();
    }

    public void Dispose() => _eval.Dispose();

    /// <summary>Rejoue chaque temoin figee : la sortie C# egale la sortie figee.</summary>
    [Fact]
    public void PariteRejoueLesTemoinsFiges()
    {
        Assert.NotEmpty(_manifest.Witnesses);
        foreach (Witness witness in _manifest.Witnesses)
        {
            GoGame game = Replay(witness);
            double predicted = _eval.PredictBlackArea(game);
            Assert.InRange(
                predicted,
                witness.ExpectedScore - 1e-3, witness.ExpectedScore + 1e-3);
            _output.WriteLine(
                $"ply {witness.Ply,3} ({witness.ToPlay} au trait) : attendu "
                + $"{witness.ExpectedScore,7:F3}, rendu {predicted,7:F3} ; baseline "
                + $"TerritoryHeuristic {witness.CurrentArea,4} ; vrai final "
                + $"{witness.FinalLabel,4}");
        }
    }

    /// <summary>
    /// La komi n'est pas apprise : elle s'ajoute en arithmetique exacte apres
    /// l'inference. Deux fois la meme position, deux komis -- l'ecart est la komi.
    /// </summary>
    [Fact]
    public void KomiAjouteeExactementApresInference()
    {
        Witness witness = _manifest.Witnesses.OrderBy(w => w.Ply).First(w => w.Ply > 0);
        double sansKomi = _eval.PredictBlackArea(Replay(witness, komi: 0.0));
        double avecKomi = _eval.PredictBlackArea(Replay(witness, komi: 5.5));
        Assert.InRange(avecKomi - sansKomi, 5.5 - 1e-6, 5.5 + 1e-6);
    }

    /// <summary>Antisymetrie du point de vue joueur, et le vide n'est pas un joueur.</summary>
    [Fact]
    public void PointDeVueJoueurAntisymetriqueEtVideRefuse()
    {
        Witness witness = _manifest.Witnesses.First(w => w.Ply >= 12);
        GoGame game = Replay(witness);

        double black = _eval.Evaluate(game, GoColor.Black);
        double white = _eval.Evaluate(game, GoColor.White);
        Assert.InRange(black + white, -1e-9, 1e-9);

        // Le rejeu suit ToPlay : au temoin fige, le trait doit etre celui que la
        // fixture declare -- sinon le rejeu a derape d'un demi-coup quelque part.
        Assert.Equal(
            witness.ToPlay == "black" ? GoColor.Black : GoColor.White, game.ToPlay);
        Assert.Throws<ArgumentOutOfRangeException>(
            () => _eval.Evaluate(game, GoColor.Empty));
    }

    /// <summary>Un goban hors modele est refuse en nommant la sortie, pas en devinant.</summary>
    [Fact]
    public void GobanHorsModeleRefuseEnNommantLaSortie()
    {
        GoGame petit = new(5, 0.0);
        InvalidOperationException ex = Assert.Throws<InvalidOperationException>(
            () => _eval.PredictBlackArea(petit));
        Assert.Contains("reentrainer", ex.Message);
    }

    /// <summary>
    /// L'orientation du tenseur, unite la plus fine : une pierre noire en
    /// <c>GoPoint(0, 0)</c> (bas-gauche du goban) alimente la case [0, 0] du plan
    /// noir -- et nulle part ailleurs. Le plan du trait suit <c>ToPlay</c>.
    /// </summary>
    [Fact]
    public void OrientationGoPointVersTenseurEpinglee()
    {
        GoGame game = new(9, 0.0);
        Assert.True(game.Play(new GoPoint(0, 0)));
        DenseTensor<float> tensor = GoOnnxEvaluation.BuildInput(game);

        Assert.Equal(1f, tensor[0, 0, 0, 0]);
        Assert.Equal(0f, tensor[0, 1, 0, 0]);
        // Apres le coup de noir, c'est BLANC au trait : le plan vaut 0 partout.
        Assert.Equal(0f, tensor[0, 2, 4, 4]);
        Assert.Equal(0f, tensor[0, 0, 8, 8]);        // la pierre n'a pas voyage
        Assert.Equal(0f, tensor[0, 0, 0, 8]);

        // La passe consomme le trait de blanc : noir au trait, plan a 1 partout.
        Assert.True(game.Play(GoPoint.Pass));
        DenseTensor<float> apresPasse = GoOnnxEvaluation.BuildInput(game);
        Assert.Equal(1f, apresPasse[0, 2, 4, 4]);
    }

    /// <summary>
    /// La fixture porte le releve honnet du duel net/baseline -- il ne se
    /// reformule pas en reussite : BEATS ou NO BEATS, tel que mesure.
    /// </summary>
    [Fact]
    public void ManifestPorteLeVerdictMesure()
    {
        Metrics metrics = _manifest.Metrics;
        Assert.Contains(metrics.Verdict, new[] { "BEATS", "NO BEATS" });
        Assert.True(metrics.MaeNetExported > 0, "un MAE nul n'a pas ete mesure");
        Assert.True(metrics.MaeBaselineTerritoryHeuristic > 0);
        _output.WriteLine(
            $"releve figure : net {metrics.MaeNetExported} vs baseline "
            + $"{metrics.MaeBaselineTerritoryHeuristic} -> {metrics.Verdict} "
            + $"({metrics.PositionsTrain} train / {metrics.PositionsTest} test)");
    }

    // ------------------------------------------------------------------
    // Rejeu d'un temoin : les coups alternent depuis noir, le passe compris,
    // exactement comme la partie sonde du generateur (Play suit ToPlay).
    // ------------------------------------------------------------------

    private static GoGame Replay(Witness witness, double komi = 0.0)
    {
        GoGame game = new(9, komi);
        foreach (Move move in witness.Moves)
        {
            GoPoint point = move.X is int x && move.Y is int y
                ? new GoPoint(x, y)
                : GoPoint.Pass;
            Assert.True(game.Play(point), $"coup refuse au rejeu : {point}");
        }

        return game;
    }

    // ------------------------------------------------------------------
    // Chargement de la fixture (meme schema que le generateur python).
    // ------------------------------------------------------------------

    private sealed record Manifest(
        int BoardSize,
        double Komi,
        string ModelFile,
        string Generator,
        Metrics Metrics,
        List<Witness> Witnesses)
    {
        private static readonly JsonSerializerOptions Options = new()
        {
            PropertyNamingPolicy = JsonNamingPolicy.SnakeCaseLower,
            PropertyNameCaseInsensitive = false,
        };

        public static Manifest Load()
        {
            string path = Path.Combine(
                AppContext.BaseDirectory, "Search", "Go", "oracles",
                "go_eval_onnx_expected.json");
            if (!File.Exists(path))
            {
                throw new FileNotFoundException(
                    "fixture des temoins ONNX absente -- regenerer via "
                    + "Search/Go/oracles/train_go_eval_onnx.py", path);
            }

            return JsonSerializer.Deserialize<Manifest>(File.ReadAllText(path), Options)
                   ?? throw new InvalidOperationException($"fixture illisible : {path}");
        }
    }

    private sealed record Metrics(
        int PositionsTrain,
        int PositionsTest,
        Dictionary<string, double> MaeNetPerSeed,
        double MaeNetExported,
        double MaeBaselineTerritoryHeuristic,
        string Verdict);

    private sealed record Witness(
        int Ply,
        List<Move> Moves,
        [property: JsonPropertyName("to_play")] string ToPlay,
        double ExpectedScore,
        double CurrentArea,
        double FinalLabel);

    /// <summary>Coup au referentiel GoPoint ; passe = X/Y absents.</summary>
    private sealed record Move(int? X, int? Y);
}
