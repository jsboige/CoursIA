namespace MyIA.AI.Shared.Search.Adversarial.Go.Gtp;

/// <summary>
/// Decodage des coordonnees GTP (« C3 », « pass ») vers <see cref="GoPoint"/>.
/// Le sens inverse existe deja : <see cref="GoPoint"/>.ToString() emet le format
/// GTP (lettres sans le I, rangees 1-base). Ce parseur boucle la boucle pour
/// lire les reponses de <c>genmove</c>.
/// </summary>
public static class GtpCoordinate
{
    /// <summary>Les lettres GTP sautent le I : la 9e colonne s'appelle J.</summary>
    public const string Letters = "ABCDEFGHJKLMNOPQRSTUVWXYZ";

    /// <summary>
    /// Decode « pass » ou une intersection « lettre + rangee » pour un plateau
    /// de <paramref name="size"/> cases. Refuse (en nommant) le I, les lettres
    /// hors plateau et les rangees nulles ou hors plateau — un moteur qui
    /// repond « Z42 » a un plateau 5x5 est une panne, pas un coup.
    /// </summary>
    public static GoPoint Parse(string token, int size)
    {
        ArgumentNullException.ThrowIfNull(token);

        if (token == "pass")
        {
            return GoPoint.Pass;
        }

        if (token == "resign")
        {
            throw new GtpException(
                "le moteur a rendu « resign » : ce n'est pas une intersection, et la decision d'abandonner n'est pas deleguee au parseur");
        }

        if (token.Length < 2)
        {
            throw new GtpException($"coordonnee GTP invalide : « {token} »");
        }

        char letter = char.ToUpperInvariant(token[0]);
        int column = Letters.IndexOf(letter);
        if (column < 0 || column >= size)
        {
            throw new GtpException(
                $"colonne « {token[0]} » invalide sur un plateau {size}x{size} (rappel : GTP saute la lettre I)");
        }

        if (!int.TryParse(token[1..], out int row) || row < 1 || row > size)
        {
            throw new GtpException(
                $"rangee « {token[1..]} » invalide sur un plateau {size}x{size}");
        }

        return new GoPoint(column, row - 1);
    }
}
