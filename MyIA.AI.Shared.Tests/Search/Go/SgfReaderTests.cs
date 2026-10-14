using MyIA.AI.Shared.Search.Adversarial.Go;
using Xunit;
using Xunit.Abstractions;

namespace MyIA.AI.Shared.Tests.Search;

/// <summary>
/// Temoins du lecteur SGF (EPIC #7265, pepite B3, tranche 5).
///
/// Le contrat tenu ici est celui d'un lecteur <b>honnete</b> : ce qu'il ne sait
/// pas lire, il le refuse en le nommant, plutot que de rendre une position qui
/// aurait l'air chargee. Trois temoins portent ce contrat a eux seuls — les
/// pierres de handicap (les ignorer decalerait la partie), la ligne principale
/// d'un arbre a variantes (le chiffre est rendu, pas tu), et le coup illicite
/// (le rejeu s'arrete et dit ou). Deux autres verrouillent des choix de
/// conception qui se casseraient en silence : la couleur portee par le coup, et
/// la lecture de SZ avant le decodage des points.
/// </summary>
public sealed class SgfReaderTests
{
    private readonly ITestOutputHelper _output;

    public SgfReaderTests(ITestOutputHelper output) => _output = output;

    [Fact]
    public void Analyse_UnePartieSimple()
    {
        SgfGame game = SgfReader.Parse("(;GM[1]FF[4]SZ[5]KM[0.5];B[aa];W[bb];B[cc];W[dd])");

        Assert.Equal(5, game.Size);
        Assert.Equal(0.5, game.Komi);
        Assert.Equal(4, game.Moves.Count);
        Assert.Equal(0, game.SkippedVariations);
        Assert.Equal(new GoPoint(0, 0), game.Moves[0].Point);
        Assert.Equal(new GoPoint(1, 1), game.Moves[1].Point);
        Assert.Equal(new GoPoint(2, 2), game.Moves[2].Point);
        Assert.Equal(new GoPoint(3, 3), game.Moves[3].Point);
    }

    [Fact]
    public void Couleur_PorteeParLeCoup_PasParLeRang()
    {
        // Un enregistrement dont le PREMIER coup est blanc : la couleur doit
        // venir de la lettre de la propriete, jamais du rang du coup.
        SgfGame game = SgfReader.Parse("(;SZ[5]KM[0];W[cc];B[dd])");

        Assert.Equal(GoColor.White, game.Moves[0].Color);
        Assert.Equal(GoColor.Black, game.Moves[1].Color);
    }

    [Fact]
    public void Passe_DeuxEcritures()
    {
        // B[] est la passe FF[4] ; B[tt] est la passe historique des plateaux
        // jusqu'a 19. Les deux doivent se lire pareil.
        SgfGame moderne = SgfReader.Parse("(;SZ[19]KM[7.5];B[pd];W[];B[tt])");

        Assert.False(moderne.Moves[0].Point.IsPass);
        Assert.True(moderne.Moves[1].Point.IsPass);
        Assert.True(moderne.Moves[2].Point.IsPass);
    }

    [Fact]
    public void Tt_N_est_Passe_Que_jusqu_a_19()
    {
        // Sur un plateau de 20, 't' vaut 19 : c'est une intersection reelle,
        // pas la passe. La borne historique doit etre respectee, sinon un coup
        // reel serait lu comme une passe.
        SgfGame game = SgfReader.Parse("(;SZ[20]KM[0];B[tt])");

        Assert.False(game.Moves[0].Point.IsPass);
        Assert.Equal(new GoPoint(19, 19), game.Moves[0].Point);
    }

    [Fact]
    public void Lettres_Au_dela_de_z()
    {
        // Le codage SGF continue au-dela de 'z' par les majuscules : 'A' = 26.
        // Analyse seule : le moteur de regles plafonne plus bas que le codage,
        // et c'est au chargement que cette limite se dit, pas ici.
        SgfGame game = SgfReader.Parse("(;SZ[30]KM[0];B[Aa])");

        Assert.Equal(30, game.Size);
        Assert.Equal(new GoPoint(26, 0), game.Moves[0].Point);
    }

    [Fact]
    public void Variantes_SeulementLaLigne_Principale_Et_Le_Chiffre_Est_Rendu()
    {
        SgfGame game = SgfReader.Parse(
            "(;SZ[5]KM[0];B[aa];W[bb](;B[cc])(;B[dd]))");

        Assert.Equal(2, game.Moves.Count);
        Assert.Equal(2, game.SkippedVariations);
        Assert.DoesNotContain(game.Moves, m => m.Point == new GoPoint(2, 2));
        Assert.DoesNotContain(game.Moves, m => m.Point == new GoPoint(3, 3));
    }

    [Fact]
    public void PierresDeHandicap_Refusees_Parce_Qu_elles_Decaleraient_La_Partie()
    {
        // Refuser est ici le contraire d'un exces de prudence : ignorer AB
        // chargerait une position ou les pierres noires du handicap manquent,
        // c'est-a-dire une autre partie, presentee comme la bonne.
        SgfFormatException ab = Assert.Throws<SgfFormatException>(
            () => SgfReader.Parse("(;SZ[5]KM[0]AB[cc][dd]AW[bb];W[aa])"));

        Assert.Contains("AB", ab.Message);
        Assert.Contains("non supportees", ab.Message);

        Assert.Throws<SgfFormatException>(() => SgfReader.Parse("(;SZ[5]KM[0]AW[bb];B[aa])"));
    }

    [Fact]
    public void CoupIllicite_Rapporte_Et_Le_Rejeu_S_arrete_La()
    {
        // Le troisieme coup rejoue sur une intersection occupee. Le chargement
        // doit rendre la position des DEUX premiers coups et nommer le refus,
        // jamais presenter la position partielle comme la partie complete.
        SgfLoadResult result = SgfReader.Load("(;SZ[5]KM[0];B[aa];W[bb];B[aa];W[cc])");

        Assert.Equal(2, result.AppliedMoves);
        Assert.Equal(3, result.RefusedPly);
        Assert.NotNull(result.Refusal);
        Assert.Contains("3", result.Refusal!);
        Assert.False(result.Game.IsOver);

        // La position rendue est celle des coups precedents, intacte.
        Assert.Equal(GoColor.Black, result.Game.ColorAt(new GoPoint(0, 0)));
        Assert.Equal(GoColor.White, result.Game.ColorAt(new GoPoint(1, 1)));
        Assert.Equal(GoColor.Empty, result.Game.ColorAt(new GoPoint(2, 2)));
    }

    [Fact]
    public void Sz_Lu_Avant_Le_Decodage_Des_Points()
    {
        // SZ arrive ICI apres le coup. Decoder au fil de l'eau prendrait le
        // defaut 19 et accepterait (6,6) : le plateau reel est 5x5, et c'est
        // cette lecture-la qui doit refuser. Temoin du decodage en deux passes.
        SgfFormatException ex = Assert.Throws<SgfFormatException>(() => SgfReader.Parse("(;B[gg];SZ[5]KM[0])"));

        Assert.Contains("hors plateau", ex.Message);
        Assert.Contains("5x5", ex.Message);
    }

    [Fact]
    public void Entrees_Malformees_Levent_En_Nommant_La_Raison()
    {
        Assert.Throws<SgfFormatException>(() => SgfReader.Parse(""));
        Assert.Throws<SgfFormatException>(() => SgfReader.Parse("   "));
        Assert.Throws<SgfFormatException>(() => SgfReader.Parse("B[aa]"));

        SgfFormatException nonEquilibre = Assert.Throws<SgfFormatException>(
            () => SgfReader.Parse("(;SZ[5]KM[0];B[aa]"));
        Assert.Contains("non equilibrees", nonEquilibre.Message);

        SgfFormatException sansCrochet = Assert.Throws<SgfFormatException>(
            () => SgfReader.Parse("(;SZ[5]KM[0];B)"));
        Assert.Contains("sans valeur entre crochets", sansCrochet.Message);

        SgfFormatException rectangulaire = Assert.Throws<SgfFormatException>(
            () => SgfReader.Parse("(;SZ[5:7]KM[0];B[aa])"));
        Assert.Contains("rectangulaire", rectangulaire.Message);
    }

    [Fact]
    public void Chargement_Produit_Une_Position_Jouable()
    {
        const string texte = "(;GM[1]FF[4]SZ[5]KM[0];B[aa];W[bb];B[cc];W[dd];B[])";

        SgfLoadResult result = SgfReader.Load(texte);

        Assert.Equal(5, result.AppliedMoves);
        Assert.Equal(-1, result.RefusedPly);
        Assert.Null(result.Refusal);
        Assert.Equal(GoColor.White, result.Game.ToPlay);
        Assert.Equal(5, result.Game.Size);
        Assert.Equal(4, CountStones(result.Game));

        // Le chemin en une passe et le chemin en deux passes rendent la meme chose.
        SgfLoadResult deux = SgfReader.Load(SgfReader.Parse(texte));
        Assert.Equal(result.AppliedMoves, deux.AppliedMoves);
        Assert.Equal(result.Game.AreaScore(), deux.Game.AreaScore());

        _output.WriteLine($"chargement : {result.AppliedMoves} coups, score {result.Game.AreaScore()}");
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
