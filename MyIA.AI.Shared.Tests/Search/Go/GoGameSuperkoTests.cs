using MyIA.AI.Shared.Search.Adversarial;
using MyIA.AI.Shared.Search.Adversarial.Go;
using Xunit;
using Xunit.Abstractions;

namespace MyIA.AI.Shared.Tests.Search;

/// <summary>
/// Temoins du superko positionnel et du hachage Zobrist (EPIC #7265, pepite B3,
/// tranche 4).
///
/// Le temoin central est un <b>double ko</b> : deux kos independants dont les
/// prises alternent. Chaque recapture y est legale au ko simple — le point de ko
/// vient de bouger sur l'AUTRE site — et seule la recreation de la position
/// d'origine, au quatrieme demi-coup, arrete le cycle. C'est exactement la classe
/// de boucle que la recherche adversariale de la tranche 3 pourrait parcourir en
/// boucle si l'historique de positions ne survivait pas au clonage.
/// </summary>
public sealed class GoGameSuperkoTests
{
    private readonly ITestOutputHelper _output;

    public GoGameSuperkoTests(ITestOutputHelper output) => _output = output;

    /// <summary>
    /// Position de double ko, 5x5, komi 0, noir au trait. Site A en haut a
    /// gauche : W(1,1) en atari par B(1,0),(0,1),(2,1), liberte (1,2) ;
    /// l'isolant de la future pierre B(1,2) est W(0,2),(2,2),(1,3). Site B en
    /// bas a droite : B(4,3) en atari par W(3,3),(4,4), liberte (4,2) ;
    /// l'isolant de la future W(4,2) est B(3,2),(4,1). La sequence de pose est
    /// alternante et calme (aucune capture, aucun suicide).
    /// </summary>
    private static GoGame DoubleKoPosition()
    {
        GoGame game = new(5, komi: 0);
        foreach ((int x, int y, GoColor c) in new[]
        {
            (1, 0, GoColor.Black), (1, 1, GoColor.White),
            (0, 1, GoColor.Black), (0, 2, GoColor.White),
            (2, 1, GoColor.Black), (2, 2, GoColor.White),
            (3, 2, GoColor.Black), (1, 3, GoColor.White),
            (4, 3, GoColor.Black), (3, 3, GoColor.White),
            (4, 1, GoColor.Black), (4, 4, GoColor.White),
        })
        {
            Assert.True(game.Play(new GoPoint(x, y), c), $"pose setup ({x},{y})");
        }

        Assert.Equal(GoColor.Black, game.ToPlay);
        return game;
    }

    [Fact]
    public void DoubleKo_LeCycleSeTermineParLeSuperkoPasParLeKoSimple()
    {
        GoGame game = DoubleKoPosition();
        int stonesBefore = CountStones(game);

        // Prise du ko A par noir : capture W(1,1), ko simple sur (1,1).
        Assert.True(game.Play(new GoPoint(1, 2)));
        Assert.Equal(new GoPoint(1, 1), game.KoPoint);

        // Prise du ko B par blanc : capture B(4,3), ko simple sur (4,3) — le
        // recapture immediat de B est bloque, mais ce n'est pas lui qu'on joue.
        Assert.True(game.Play(new GoPoint(4, 2)));
        Assert.Equal(new GoPoint(4, 3), game.KoPoint);

        // Noir passe : la seule facon de rendre le trait sans toucher au plateau.
        Assert.True(game.Pass());

        // Blanc reprend le ko A : legal au ko simple (le point de ko est sur
        // l'autre site), la position du site A revient a l'origine.
        Assert.True(game.Play(new GoPoint(1, 1)));

        // Noir reprend le ko B : LEGAL au ko simple (point de ko sur (1,2)),
        // pas un suicide (il capture W(4,2)) — mais la position produite est
        // EXACTEMENT celle d'ouverture : seul le superko peut l'interdire.
        Assert.False(game.IsLegal(new GoPoint(4, 3)),
            "la recreation de la position d'ouverture doit etre interdite");
        Assert.False(game.Play(new GoPoint(4, 3)),
            "un coup illegal ne doit rien changer au plateau");
        Assert.Equal(stonesBefore, CountStones(game));
        Assert.Equal(new GoPoint(1, 2), game.KoPoint);
    }

    [Fact]
    public void Superko_SurvitAuClonage()
    {
        GoGame game = DoubleKoPosition();
        Assert.True(game.Play(new GoPoint(1, 2)));
        Assert.True(game.Play(new GoPoint(4, 2)));
        Assert.True(game.Pass());
        Assert.True(game.Play(new GoPoint(1, 1)));

        // Un clone oublieux de l'historique autoriserait en sous-arbre la
        // repetition que la racine interdit — c'est la boucle infinie que cette
        // tranche ferme pour la recherche de la tranche 3.
        GoGame clone = game.Clone();

        Assert.Equal(game.PositionHash, clone.PositionHash);
        Assert.Equal(game.PositionCount, clone.PositionCount);
        Assert.False(clone.IsLegal(new GoPoint(4, 3)));
    }

    [Fact]
    public void Adaptateur_NeProposePasLeCoupDeRepetition()
    {
        GoGameAdapter adapter = new(5, komi: 0);
        GoGame game = DoubleKoPosition();
        Assert.True(game.Play(new GoPoint(1, 2)));
        Assert.True(game.Play(new GoPoint(4, 2)));
        Assert.True(game.Pass());
        Assert.True(game.Play(new GoPoint(1, 1)));

        IReadOnlyList<GoPoint> actions = adapter.Actions(game);

        Assert.DoesNotContain(new GoPoint(4, 3), actions);
        Assert.Contains(GoPoint.Pass, actions);
    }

    [Fact]
    public void HachageZobrist_SuitLesPierresSansBougerAuHasard()
    {
        GoGame game = DoubleKoPosition();
        ulong before = game.PositionHash;
        int count = game.PositionCount;

        Assert.True(game.Play(new GoPoint(1, 2)));
        ulong afterCapture = game.PositionHash;

        // Le coup change l'empreinte (pierre posee, pierre capturee) et une
        // position nouvelle entre dans l'historique.
        Assert.NotEqual(before, afterCapture);
        Assert.Equal(count + 1, game.PositionCount);

        // Le passe ne change ni l'empreinte ni l'historique : la position
        // courante est deja inscrite, le passe ne la recree pas.
        Assert.True(game.Pass());
        Assert.Equal(afterCapture, game.PositionHash);
        Assert.Equal(count + 1, game.PositionCount);

        // Deux executions produisent la meme table (graine fixe) : deux parties
        // identiques ont les memes empreintes, sinon aucun temoin ne serait
        // reproductible d'un run a l'autre.
        GoGame replay = DoubleKoPosition();
        Assert.Equal(before, replay.PositionHash);
    }

    [Fact]
    public void KoSimple_RecaptureImmediateInterdite_CommeAvant()
    {
        // Regression du ko simple : la regle locale doit continuer de bloquer le
        // recapture immediat, le superko ne la remplace pas — il la prolonge.
        GoGame game = new(5, komi: 0);
        foreach ((int x, int y) in new[]
        {
            (1, 0), (1, 1), (0, 1), (0, 2), (2, 1), (2, 2), (4, 0), (1, 3),
        })
        {
            Assert.True(game.Play(new GoPoint(x, y)));
        }

        Assert.True(game.Play(new GoPoint(1, 2)));
        Assert.Equal(new GoPoint(1, 1), game.KoPoint);
        Assert.False(game.IsLegal(new GoPoint(1, 1)));
    }

    [Fact]
    public void Passe_ToujoursLegalLaPartieTermine()
    {
        GoGame game = DoubleKoPosition();
        Assert.True(game.Play(new GoPoint(1, 2)));
        Assert.True(game.Play(new GoPoint(4, 2)));
        Assert.True(game.Pass());

        // La position de fin reste atteignable : deux passes consecutives
        // terminent la partie meme au milieu d'un cycle de repetition.
        Assert.True(game.Pass());
        Assert.True(game.IsOver);
    }

    private static int CountStones(GoGame game)
    {
        int stones = 0;
        for (int y = 0; y < game.Size; y++)
        {
            for (int x = 0; x < game.Size; x++)
            {
                if (game.ColorAt(new GoPoint(x, y)) != GoColor.Empty)
                {
                    stones++;
                }
            }
        }

        return stones;
    }
}
