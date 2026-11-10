using MyIA.AI.Shared.Search.Adversarial.Go;
using Xunit;
using Xunit.Abstractions;

namespace MyIA.AI.Shared.Tests.Search;

/// <summary>
/// Temoins des regles du Go (EPIC #7265, pepite B3, tranche 2 — port GoTraxx).
///
/// Chaque regle est confrontee a une position construite coup par coup, ou
/// une seule arete la fait diverger : capturer retire la chaine ENTIERE et
/// seulement elle ; le suicide est refuse, SAUF s'il capture ; le ko simple
/// interdit le recapture immediat et lui seul ; deux passes finissent la
/// partie ; le territoire appartient a la couleur qui l'enceint seule, le
/// dame a personne. Le noir joue en premier partout — l'alternance stricte
/// est elle-meme un temoin.
/// </summary>
public sealed class GoGameWitnessTests
{
    private readonly ITestOutputHelper _output;

    public GoGameWitnessTests(ITestOutputHelper output) => _output = output;

    private static GoPoint P(int x, int y) => new(x, y);

    // ------------------------------------------------------------------
    // Capture — la chaine entiere, et seulement les chaines sans liberte.
    // ------------------------------------------------------------------

    /// <summary>
    /// Une pierre noire entouree : le coup blanc qui prend sa derniere
    /// liberte la capture, l'intersection redevient vide, la prisonniere est
    /// comptee. Le fil du temoin : ce n'est pas la pose qui capture, c'est la
    /// derniere liberte prise.
    /// </summary>
    [Fact]
    public void LoneStoneIsCapturedWhenItsLastLibertyIsTaken()
    {
        GoGame go = new(size: 9, komi: 0);
        // Victime noire (4,4) ; blanc enceint par le haut, l'ouest, le bas,
        // puis l'est. Les coups noirs de detour (0,0..2) s'accumulent en
        // bord de plateau, hors du combat.
        Assert.True(go.Play(P(4, 4), GoColor.Black));
        Assert.True(go.Play(P(4, 3), GoColor.White));
        Assert.True(go.Play(P(0, 0), GoColor.Black));
        Assert.True(go.Play(P(3, 4), GoColor.White));
        Assert.True(go.Play(P(0, 1), GoColor.Black));
        Assert.True(go.Play(P(4, 5), GoColor.White));

        Assert.Equal(GoColor.Black, go.ColorAt(P(4, 4)));

        Assert.True(go.Play(P(0, 2), GoColor.Black));
        Assert.True(go.Play(P(5, 4), GoColor.White));   // la derniere liberte

        Assert.Equal(GoColor.Empty, go.ColorAt(P(4, 4)));
        Assert.Equal(1, go.CapturedStones(GoColor.Black));
        Assert.Equal(0, go.CapturedStones(GoColor.White));
        _output.WriteLine("pierre isolee capturee : (4,4) vide, 1 prisonnier noir");
    }

    /// <summary>
    /// Deux pierres noires connectees meurent ENSEMBLE quand leur derniere
    /// liberte commune tombe — la chaine est l'unite de vie, pas la pierre.
    /// </summary>
    [Fact]
    public void ConnectedGroupIsCapturedAsAWhole()
    {
        GoGame go = new(size: 9, komi: 0);
        // Chaine noire (3,4)-(4,4), enceinte par le haut, le bas, l'ouest,
        // puis l'est. Pierres noires de detour sur la colonne 0.
        Assert.True(go.Play(P(3, 4), GoColor.Black));
        Assert.True(go.Play(P(3, 3), GoColor.White));
        Assert.True(go.Play(P(4, 4), GoColor.Black));
        Assert.True(go.Play(P(4, 3), GoColor.White));
        Assert.True(go.Play(P(0, 0), GoColor.Black));
        Assert.True(go.Play(P(3, 5), GoColor.White));
        Assert.True(go.Play(P(0, 1), GoColor.Black));
        Assert.True(go.Play(P(4, 5), GoColor.White));
        Assert.True(go.Play(P(0, 2), GoColor.Black));
        Assert.True(go.Play(P(2, 4), GoColor.White));

        Assert.Equal(GoColor.Black, go.ColorAt(P(3, 4)));
        Assert.Equal(GoColor.Black, go.ColorAt(P(4, 4)));

        Assert.True(go.Play(P(0, 3), GoColor.Black));
        Assert.True(go.Play(P(5, 4), GoColor.White));   // l'est : derniere liberte

        Assert.Equal(GoColor.Empty, go.ColorAt(P(3, 4)));
        Assert.Equal(GoColor.Empty, go.ColorAt(P(4, 4)));
        Assert.Equal(2, go.CapturedStones(GoColor.Black));
        _output.WriteLine("groupe de deux capture d'un bloc : 2 prisonniers noirs");
    }

    // ------------------------------------------------------------------
    // Suicide — refuse, sauf s'il capture : la paire discriminante.
    // ------------------------------------------------------------------

    /// <summary>
    /// Jouer dans une intersection ou la pierre n'aurait AUCUNE liberte, sans
    /// rien capturer : refuse, le plateau ne bouge pas. Les chaines noires
    /// voisines (1,0) et (0,1) ont chacune une seconde liberte — le coup ne
    /// peut pas se sauver en capturant.
    /// </summary>
    [Fact]
    public void SuicideWithoutCaptureIsRefused()
    {
        GoGame go = new(size: 5, komi: 0);
        // Coin nord-ouest (0,0) : noir occupe (1,0) et (0,1), chacune pourvue
        // d'une autre liberte ((2,0) et (0,2)).
        Assert.True(go.Play(P(1, 0), GoColor.Black));
        Assert.True(go.Play(P(4, 4), GoColor.White));
        Assert.True(go.Play(P(0, 1), GoColor.Black));

        Assert.False(go.IsLegal(P(0, 0), GoColor.White));
        Assert.False(go.Play(P(0, 0), GoColor.White));

        Assert.Equal(GoColor.Empty, go.ColorAt(P(0, 0)));
        Assert.Equal(GoColor.White, go.ToPlay);   // le refus ne consomme pas le tour
        _output.WriteLine("suicide au coin refuse : (0,0) reste vide");
    }

    /// <summary>
    /// La MEME intersection (0,0) du coin, mais ou chaque chaine noire
    /// voisine n'a QUE cette liberte : le coup blanc, suicidaire de face, est
    /// legal parce qu'il capture les deux. C'est la paire qui prouve que le
    /// moteur evalue le suicide APRES les captures — la reponse canonique au
    /// suicide apparent est de prendre la derniere liberte de l'ennemi.
    /// </summary>
    [Fact]
    public void TheSamePointIsLegalWhenItCaptures()
    {
        GoGame go = new(size: 5, komi: 0);
        // Victimes noires (1,0) et (0,1) — diagonales, donc DEUX chaines.
        // Blanc les met toutes deux en atari sur (0,0) : W(2,0), W(1,1),
        // W(0,2), pierres vivantes chacune par ailleurs.
        Assert.True(go.Play(P(1, 0), GoColor.Black));
        Assert.True(go.Play(P(2, 0), GoColor.White));
        Assert.True(go.Play(P(0, 1), GoColor.Black));
        Assert.True(go.Play(P(4, 4), GoColor.White));   // detour
        Assert.True(go.Play(P(3, 4), GoColor.Black));   // detour
        Assert.True(go.Play(P(1, 1), GoColor.White));
        Assert.True(go.Play(P(4, 3), GoColor.Black));   // detour
        Assert.True(go.Play(P(0, 2), GoColor.White));
        Assert.True(go.Play(P(2, 4), GoColor.Black));   // detour

        Assert.False(go.ColorAt(P(0, 0)) == GoColor.White);
        Assert.True(go.Play(P(0, 0), GoColor.White));   // suicidaire de face, capturant de fond

        Assert.Equal(GoColor.White, go.ColorAt(P(0, 0)));
        Assert.Equal(GoColor.Empty, go.ColorAt(P(1, 0)));
        Assert.Equal(GoColor.Empty, go.ColorAt(P(0, 1)));
        Assert.Equal(2, go.CapturedStones(GoColor.Black));
        _output.WriteLine("coup suicidaire de face, capturant de fond : 2 prisonniers noirs");
    }

    // ------------------------------------------------------------------
    // Ko simple — le recapture immediat, et lui seul.
    // ------------------------------------------------------------------

    /// <summary>
    /// La forme du ko : noir capture une pierre blanche isolee par une pierre
    /// isolee. Le recapture blanc IMMEDIAT est refuse ; apres un echange
    /// quelconque, il redevient legal — le ko simple interdit le retour
    /// instantane a la position precedente, pas la repetition en general.
    /// </summary>
    [Fact]
    public void ImmediateKoRecaptureIsRefusedThenAllowedAfterAnInterveningMove()
    {
        GoGame go = new(size: 5, komi: 0);
        // Noir : (1,0), (0,1), (1,2). Blanc : (2,0), (2,2), (3,1), puis la
        // victime (1,1) — enceinte de noir sauf par (2,1).
        foreach ((int x, int y, GoColor c) in new[]
                 {
                     (1, 0, GoColor.Black), (2, 0, GoColor.White),
                     (0, 1, GoColor.Black), (2, 2, GoColor.White),
                     (1, 2, GoColor.Black), (3, 1, GoColor.White),
                 })
        {
            Assert.True(go.Play(P(x, y), c));
        }

        Assert.True(go.Pass());                       // noir cede le tempo
        Assert.True(go.Play(P(1, 1), GoColor.White)); // la future victime
        Assert.Equal(GoColor.White, go.ColorAt(P(1, 1)));

        Assert.True(go.Play(P(2, 1), GoColor.Black)); // capture (1,1) : ko !
        Assert.Equal(GoColor.Empty, go.ColorAt(P(1, 1)));
        Assert.NotNull(go.KoPoint);
        Assert.Equal(P(1, 1), go.KoPoint!.Value);

        // Recapture immediat : refuse — et ce refus est bien le KO, pas le
        // suicide : sans lui, le coup capturerait (2,1) et vivrait.
        Assert.False(go.IsLegal(P(1, 1), GoColor.White));
        Assert.False(go.Play(P(1, 1), GoColor.White));

        // Un echange quelconque leve le ko simple.
        Assert.True(go.Play(P(4, 4), GoColor.White));
        Assert.True(go.Pass());
        Assert.True(go.IsLegal(P(1, 1), GoColor.White));
        Assert.True(go.Play(P(1, 1), GoColor.White)); // recapture enfin legal
        Assert.Equal(GoColor.Empty, go.ColorAt(P(2, 1)));
        Assert.Equal(1, go.CapturedStones(GoColor.Black));
        _output.WriteLine("ko : recapture immediat refuse, recapture differe joue");
    }

    // ------------------------------------------------------------------
    // Passes, fin de partie, alternance.
    // ------------------------------------------------------------------

    /// <summary>
    /// Deux passes CONSECUTIVES terminent la partie ; une passe isolee par un
    /// coup non. Apres la fin, plus aucun coup n'est legal.
    /// </summary>
    [Fact]
    public void TwoConsecutivePassesEndTheGameAndFreezeTheBoard()
    {
        GoGame go = new(size: 9, komi: 0);
        Assert.True(go.Play(P(4, 4), GoColor.Black));
        Assert.True(go.Pass());               // blanc passe
        Assert.True(go.Play(P(3, 3), GoColor.Black));
        Assert.True(go.Pass());               // passe isolee par le coup noir
        Assert.False(go.IsOver);
        Assert.True(go.Pass());               // noir passe : consecutif
        Assert.True(go.IsOver);

        Assert.False(go.IsLegal(P(0, 0), GoColor.White));
        Assert.False(go.Play(P(0, 0), GoColor.White));
        _output.WriteLine("deux passes consecutives : partie terminee, plateau gele");
    }

    /// <summary>
    /// L'alternance est stricte : jouer deux fois de suite la meme couleur,
    /// ou jouer sur une intersection occupee, est refuse sans effet.
    /// </summary>
    [Fact]
    public void AlternationAndOccupationAreEnforced()
    {
        GoGame go = new(size: 9, komi: 0);
        Assert.True(go.Play(P(2, 2), GoColor.Black));

        Assert.False(go.Play(P(3, 3), GoColor.Black));   // deux noirs de suite
        Assert.True(go.Play(P(3, 3), GoColor.White));
        Assert.False(go.Play(P(3, 3), GoColor.White));   // intersection occupee
        Assert.False(go.Play(P(2, 2), GoColor.White));

        Assert.Equal(GoColor.Black, go.ColorAt(P(2, 2)));
        Assert.Equal(GoColor.White, go.ColorAt(P(3, 3)));
        _output.WriteLine("alternance et occupation : trois refus, plateau intact");
    }

    // ------------------------------------------------------------------
    // Score de territoire — pierre + enceinte monochrome, komi au blanc.
    // ------------------------------------------------------------------

    /// <summary>
    /// Sur un 5x5 divise par une ligne noire (y=1) et une ligne blanche
    /// (y=3) : la rangee du haut est territoire noir, celle du bas territoire
    /// blanc, la rangee centrale touche les deux couleurs et n'appartient a
    /// personne. Le score rend exactement le komi negatif.
    /// </summary>
    [Fact]
    public void TerritoryIsMonochromeEnclosureAndDameBelongsToNoOne()
    {
        GoGame go = new(size: 5, komi: 2.5);
        for (int x = 0; x < 5; x++)
        {
            Assert.True(go.Play(P(x, 1), GoColor.Black));
            Assert.True(go.Play(P(x, 3), GoColor.White));
        }

        Assert.True(go.Pass());
        Assert.True(go.Pass());
        Assert.True(go.IsOver);

        // Noir : 5 pierres + 5 (rangee y=0). Blanc : 5 + 5 (rangee y=4).
        // La rangee y=2 touche les deux : dame. Komi 2.5 pour blanc.
        Assert.Equal(-2.5, go.AreaScore(), 6);
        _output.WriteLine("5x5 divise : 10-10-2.5 = -2.5, la rangee centrale a personne");
    }

    /// <summary>
    /// Sans opposant, chaque region vide que le noir enceint seul est
    /// territoire noir — le mur plein separe la rangee 0 du reste, mais les
    /// DEUX regions sont monochromes : 5 pierres + 20 vides, komi nul.
    /// </summary>
    [Fact]
    public void UnopposedEnclosureCountsEveryEmptyRegionItBounds()
    {
        GoGame go = new(size: 5, komi: 0);
        for (int x = 0; x < 5; x++)
        {
            Assert.True(go.Play(P(x, 1), GoColor.Black));
            Assert.True(go.Pass());            // blanc passe : forme pour noir
        }
        Assert.True(go.Pass());

        Assert.Equal(25.0, go.AreaScore(), 6);
        _output.WriteLine("enceinte sans opposition : 5 pierres + 20 territoire = 25");
    }

    /// <summary>
    /// Le nom de point suit la convention GTP : colonnes lettrees en sautant
    /// I, rangees numerotees depuis le bas — la convention que le patrimoine
    /// lisait dans la sortie gnugo.
    /// </summary>
    [Theory]
    [InlineData(0, 0, "A1")]
    [InlineData(7, 0, "H1")]
    [InlineData(8, 0, "J1")]      // le I est saute : 9e colonne = J
    [InlineData(0, 18, "A19")]
    [InlineData(18, 18, "T19")]
    public void PointNamesSkipTheLetterIAndNumberRowsFromTheBottom(int x, int y, string expected)
    {
        Assert.Equal(expected, new GoPoint(x, y).ToString());
    }
}
