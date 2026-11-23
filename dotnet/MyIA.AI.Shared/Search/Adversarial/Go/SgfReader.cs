using System.Globalization;

namespace MyIA.AI.Shared.Search.Adversarial.Go;

/// <summary>
/// Entree SGF illisible. La raison est toujours nommee : le lecteur ne rend
/// jamais une position partielle en silence.
/// </summary>
public sealed class SgfFormatException : Exception
{
    /// <summary>Construit l'exception avec sa raison.</summary>
    /// <param name="message">La raison, en clair.</param>
    public SgfFormatException(string message) : base(message)
    {
    }
}

/// <summary>
/// Un coup lu dans un enregistrement SGF.
/// </summary>
/// <param name="Color">La couleur qui joue — portee par le coup, jamais deduite du rang.</param>
/// <param name="Point">L'intersection jouee, ou <see cref="GoPoint.Pass"/>.</param>
public readonly record struct SgfMove(GoColor Color, GoPoint Point);

/// <summary>
/// Une partie SGF analysee : dimensions, komi et ligne principale.
/// </summary>
/// <param name="Size">Cote du plateau carre.</param>
/// <param name="Komi">Komi, 0 si la propriete KM est absente (defaut de la specification).</param>
/// <param name="Moves">La ligne principale, dans l'ordre du fichier.</param>
/// <param name="SkippedVariations">
/// Nombre de variantes de premier niveau ecartees. Le chiffre est rendu plutot que
/// tu : il dit a l'appelant sur quelle part du fichier il est en train de lire.
/// </param>
public sealed record SgfGame(
    int Size,
    double Komi,
    IReadOnlyList<SgfMove> Moves,
    int SkippedVariations);

/// <summary>
/// Resultat d'un chargement dans le moteur de regles.
/// </summary>
/// <param name="Game">La position atteinte — un etat legal par construction.</param>
/// <param name="AppliedMoves">Nombre de coups effectivement joues.</param>
/// <param name="RefusedPly">Rang (1 inclus) du premier coup refuse, -1 si aucun.</param>
/// <param name="Refusal">La raison du refus, nommee, ou <c>null</c>.</param>
public sealed record SgfLoadResult(GoGame Game, int AppliedMoves, int RefusedPly, string? Refusal);

/// <summary>
/// Lecteur SGF (FF[4]) reduit a la ligne principale d'un enregistrement.
///
/// <para>
/// <b>Ce qui est lu</b> : <c>SZ</c> (plateau carre), <c>KM</c>, les coups <c>B</c>/<c>W</c>
/// avec leurs deux ecritures de la passe (<c>B[]</c> et le <c>tt</c> historique des
/// plateaux jusqu'a 19), et la <b>ligne principale</b> d'un arbre qui porterait
/// plusieurs variantes.
/// </para>
/// <para>
/// <b>Ce qui est refuse nommement</b>, plutot que devine : les pierres de handicap
/// ou de position initiale (<c>AB</c>/<c>AW</c>), les plateaux rectangulaires
/// (<c>SZ[w:h]</c>) et toute entree malformee. Refuser est ici le contraire d'un
/// exces de prudence : les ignorer chargerait une position <i>fausse</i>, qui
/// aurait l'air d'avoir ete chargee. Un enregistrement de handicap rentre donc par
/// le handicap, pas par la ligne de coups.
/// </para>
/// <para>
/// <b>Sous quelles regles</b> : celles du moteur disponible, c'est-a-dire le ko
/// simple. Le superko positionnel est porte par la tranche 4 (PR #20045), non
/// encore fusionnee : un enregistrement qui repeterait une position se charge
/// aujourd'hui sous la regle locale, sans que le lecteur ait a le savoir.
/// </para>
/// </summary>
public static class SgfReader
{
    /// <summary>
    /// Plus grande dimension codable par le couple de lettres SGF
    /// (<c>a</c>-<c>z</c> puis <c>A</c>-<c>Z</c>).
    /// </summary>
    public const int MaxBoardSize = 52;

    private const int DefaultSize = 19;
    private const double DefaultKomi = 0.0;

    /// <summary>Analyse un enregistrement SGF et rend sa ligne principale.</summary>
    /// <param name="text">Le texte SGF.</param>
    /// <returns>La partie analysee.</returns>
    /// <exception cref="SgfFormatException">
    /// Entree vide, malformee, ou portant une propriete que le lecteur refuse de deviner.
    /// </exception>
    public static SgfGame Parse(string text)
    {
        if (string.IsNullOrWhiteSpace(text))
        {
            throw new SgfFormatException("entree vide");
        }

        int depth = 0;
        int skippedVariations = 0;
        bool sawTree = false;
        int size = DefaultSize;
        double komi = DefaultKomi;
        List<(GoColor Color, string Raw)> rawMoves = new();

        int i = 0;
        while (i < text.Length)
        {
            char c = text[i];

            if (c == '(')
            {
                depth++;
                sawTree = true;
                if (depth == 2)
                {
                    // Variante de premier niveau : ecartee en bloc, puis comptee.
                    skippedVariations++;
                    i = SkipGroup(text, i) + 1;
                    depth--;
                    continue;
                }

                i++;
                continue;
            }

            if (c == ')')
            {
                depth--;
                if (depth < 0)
                {
                    throw new SgfFormatException("parenthese fermante sans ouvrante");
                }

                i++;
                continue;
            }

            if (c == ';' || char.IsWhiteSpace(c))
            {
                i++;
                continue;
            }

            int start = i;
            while (i < text.Length && char.IsLetter(text[i]))
            {
                i++;
            }

            if (i == start)
            {
                throw new SgfFormatException($"caractere inattendu '{c}' a la position {i}");
            }

            string ident = text[start..i];
            if (i >= text.Length || text[i] != '[')
            {
                throw new SgfFormatException($"propriete {ident} sans valeur entre crochets");
            }

            List<string> values = new();
            while (i < text.Length && text[i] == '[')
            {
                int close = FindValueEnd(text, i);
                values.Add(text[(i + 1)..close]);
                i = close + 1;
            }

            if (depth != 1)
            {
                // Hors de l'arbre principal (entete parasite) : rien a en faire.
                continue;
            }

            switch (ident)
            {
                case "SZ":
                    size = ParseSize(values[0]);
                    break;

                case "KM":
                    komi = ParseDouble(values[0], "KM");
                    break;

                case "B":
                case "W":
                    rawMoves.Add((ident == "B" ? GoColor.Black : GoColor.White, values[0]));
                    break;

                case "AB":
                case "AW":
                    throw new SgfFormatException(
                        $"{ident} : pierres de handicap ou de position initiale non supportees — " +
                        "les ignorer chargerait une position differente de l'enregistrement");

                default:
                    // Commentaires et metadonnees (C, PB, PW, RE, DT...) : hors du contrat.
                    break;
            }
        }

        if (!sawTree)
        {
            throw new SgfFormatException("aucun arbre de partie : le texte ne porte pas de '('");
        }

        if (depth != 0)
        {
            throw new SgfFormatException("parentheses non equilibrees");
        }

        // Les points sont decodes APRES la lecture : un SZ place avant les coups
        // n'est pas garanti par la specification, et decoder au fil de l'eau
        // rendrait un plateau faux sur un fichier ou SZ suit le premier coup.
        List<SgfMove> moves = new(rawMoves.Count);
        foreach ((GoColor color, string raw) in rawMoves)
        {
            moves.Add(new SgfMove(color, DecodePoint(raw, size, color)));
        }

        return new SgfGame(size, komi, moves, skippedVariations);
    }

    /// <summary>Analyse puis charge un enregistrement SGF.</summary>
    /// <param name="text">Le texte SGF.</param>
    /// <returns>Le resultat du chargement.</returns>
    /// <exception cref="SgfFormatException">Entree illisible (cf <see cref="Parse"/>).</exception>
    public static SgfLoadResult Load(string text) => Load(Parse(text));

    /// <summary>
    /// Rejoue la ligne principale dans le moteur de regles.
    ///
    /// <para>
    /// Le rejeu s'arrete au <b>premier coup illicite</b> et le nomme : un
    /// enregistrement reel peut porter des coups que le moteur refuse (ko simple
    /// contre superko, ou fichier annote pour un autre reglement), et rendre la
    /// position des coups precedents en la presentant comme complete serait le
    /// mensonge que ce resultat existe pour empecher.
    /// </para>
    /// </summary>
    /// <param name="sgf">La partie analysee.</param>
    /// <returns>La position atteinte et, s'il y a lieu, le coup refuse.</returns>
    public static SgfLoadResult Load(SgfGame sgf)
    {
        GoGame game = new(sgf.Size, sgf.Komi);

        for (int i = 0; i < sgf.Moves.Count; i++)
        {
            SgfMove move = sgf.Moves[i];
            if (!game.IsLegal(move.Point, move.Color))
            {
                return new SgfLoadResult(
                    game,
                    i,
                    i + 1,
                    $"coup {i + 1} refuse ({move.Color} {move.Point}) : illicite sous le moteur de regles " +
                    "(ko simple) — la position rendue est celle des coups precedents");
            }

            game.Play(move.Point, move.Color);
        }

        return new SgfLoadResult(game, sgf.Moves.Count, -1, null);
    }

    private static int ParseSize(string value)
    {
        if (value.Contains(':'))
        {
            throw new SgfFormatException($"SZ[{value}] : plateau rectangulaire non supporte");
        }

        int size = ParseInt(value, "SZ");
        if (size < 1 || size > MaxBoardSize)
        {
            throw new SgfFormatException($"SZ[{value}] : dimension hors du codage SGF (1 a {MaxBoardSize})");
        }

        return size;
    }

    private static GoPoint DecodePoint(string value, int size, GoColor color)
    {
        if (value.Length == 0)
        {
            // FF[4] : B[] est la passe.
            return GoPoint.Pass;
        }

        if (value.Length != 2)
        {
            throw new SgfFormatException($"coup {color} illisible : '{value}' (deux lettres attendues)");
        }

        if (size <= 19 && value == "tt")
        {
            // Ecriture historique de la passe sur les plateaux jusqu'a 19.
            return GoPoint.Pass;
        }

        int x = LetterValue(value[0]);
        int y = LetterValue(value[1]);
        if (x < 0 || y < 0 || x >= size || y >= size)
        {
            throw new SgfFormatException($"coup {color} hors plateau : '{value}' sur {size}x{size}");
        }

        return new GoPoint(x, y);
    }

    private static int LetterValue(char c) => c switch
    {
        >= 'a' and <= 'z' => c - 'a',
        >= 'A' and <= 'Z' => c - 'A' + 26,
        _ => -1,
    };

    private static int ParseInt(string value, string ident) =>
        int.TryParse(value, NumberStyles.Integer, CultureInfo.InvariantCulture, out int parsed)
            ? parsed
            : throw new SgfFormatException($"{ident}[{value}] : entier attendu");

    private static double ParseDouble(string value, string ident) =>
        double.TryParse(value, NumberStyles.Float, CultureInfo.InvariantCulture, out double parsed)
            ? parsed
            : throw new SgfFormatException($"{ident}[{value}] : nombre attendu");

    /// <summary>Rend l'index du <c>]</c> fermant, les echappements respectes.</summary>
    private static int FindValueEnd(string text, int open)
    {
        int i = open + 1;
        while (i < text.Length)
        {
            if (text[i] == '\\')
            {
                i += 2;
                continue;
            }

            if (text[i] == ']')
            {
                return i;
            }

            i++;
        }

        throw new SgfFormatException("valeur de propriete non fermee");
    }

    /// <summary>Rend l'index du <c>)</c> qui ferme le groupe ouvert en <paramref name="open"/>.</summary>
    private static int SkipGroup(string text, int open)
    {
        int depth = 0;
        int i = open;
        while (i < text.Length)
        {
            char c = text[i];
            if (c == '[')
            {
                i = FindValueEnd(text, i) + 1;
                continue;
            }

            if (c == '(')
            {
                depth++;
            }
            else if (c == ')')
            {
                depth--;
                if (depth == 0)
                {
                    return i;
                }
            }

            i++;
        }

        throw new SgfFormatException("groupe de variante non ferme");
    }
}
