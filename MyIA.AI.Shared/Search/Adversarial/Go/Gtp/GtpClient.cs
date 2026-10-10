namespace MyIA.AI.Shared.Search.Adversarial.Go.Gtp;

/// <summary>
/// Client du protocole GTP (Go Text Protocol) sur un canal texte quelconque.
/// EPIC #7265, pepite B3, tranche 7.
/// </summary>
/// <remarks>
/// <para>
/// GTP est le protocole canonique des moteurs de Go : une commande par ligne
/// (« boardsize 5 », « play B C3 », « genmove W »), une reponse cadree
/// <c>=[id] contenu</c> ou <c>?[id] erreur</c>, terminee par une ligne vide.
/// La tranche 2b parlait deja GTP cote generation de fixtures (python,
/// <c>oracles/generate_go_oracle_fixture.py</c>) pour figer des verdicts gnugo ;
/// ce client porte la capacite complementaire : un adversaire <b>vivant</b> que
/// les moteurs de recherche peuvent affronter coup a coup, en C#, dans la
/// bibliotheque partagee.
/// </para>
/// <para>
/// Le client est deliberement decouple du moteur : il ne connait que deux flux.
/// Les temoins de la tranche parlent donc a un <b>faux moteur scripte</b> (des
/// reponses pre-ecrites dans des tubes en memoire), et le preuve contre le vrai
/// gnugo est mesuree localement et consignee dans le corps de la PR — le meme
/// partage fixture/execution que la tranche 2b, et non un temoin qui se met au
/// vert tout seul quand le binaire est absent (voir le corps de la PR pour le
/// releve).
/// </para>
/// <para>
/// <b>Timeout</b> : chaque commande lit avec un delai ; un moteur muet est
/// nomine (<see cref="GtpException"/> porte la commande en attente), jamais
/// rendu comme une reponse vide — une reponse vide est un resultat GTP valide
/// (le score d'un plateau vide, par exemple).
/// </para>
/// </remarks>
public sealed class GtpClient : IDisposable
{
    private readonly TextWriter _commandSink;
    private readonly TextReader _responseSource;
    private readonly TimeSpan _timeout;

    /// <summary>Client sur un couple de flux donnes, delai de lecture compris.</summary>
    public GtpClient(TextWriter commandSink, TextReader responseSource, TimeSpan? timeout = null)
    {
        _commandSink = commandSink;
        _responseSource = responseSource;
        _timeout = timeout ?? TimeSpan.FromSeconds(30);
    }

    /// <summary>
    /// Envoie une commande et attend sa reponse cadree. L'identifiant est
    /// optionnel ; quand il est fourni, la reponse doit le renvoyer.
    /// </summary>
    public GtpResponse Send(string command, int? id = null)
    {
        if (string.IsNullOrWhiteSpace(command))
        {
            throw new ArgumentException("une commande GTP n'est jamais vide", nameof(command));
        }

        string prefix = id is null ? command : $"{id} {command}";
        _commandSink.WriteLine(prefix);
        _commandSink.Flush();

        return ReadResponse(prefix);
    }

    private GtpResponse ReadResponse(string command)
    {
        string? header = ReadLineOrTimeout(command);
        if (header is null)
        {
            throw new GtpException(
                $"le moteur GTP a ferme son canal avant de repondre a « {command} »");
        }

        if (header.Length == 0 || (header[0] != '=' && header[0] != '?'))
        {
            throw new GtpException(
                $"reponse non cadree a « {command} » : « {header} » — attendu = ou ? en tete");
        }

        bool success = header[0] == '=';
        string rest = header.Length > 1 ? header[1..] : string.Empty;

        // Un identifiant echoe est colle au prefixe : "=12 ok" ou "?3 bad".
        int? echoedId = null;
        if (rest.Length > 0 && char.IsDigit(rest[0]))
        {
            int cut = 0;
            while (cut < rest.Length && char.IsDigit(rest[cut]))
            {
                cut++;
            }

            echoedId = int.Parse(rest[..cut]);
            rest = rest[cut..];
        }

        if (rest.StartsWith(' '))
        {
            rest = rest[1..];
        }

        // Le contenu est multi-lignes jusqu'a la ligne vide de fin de trame.
        var lines = new List<string>();
        if (rest.Length > 0)
        {
            lines.Add(rest);
        }

        while (true)
        {
            string? line = ReadLineOrTimeout(command);
            if (line is null)
            {
                throw new GtpException(
                    $"le moteur GTP a ferme son canal au milieu de la reponse a « {command} »");
            }

            if (line.Length == 0)
            {
                break;
            }

            lines.Add(line);
        }

        return new GtpResponse(success, echoedId, string.Join("\n", lines));
    }

    private string? ReadLineOrTimeout(string command)
    {
        Task<string?> read = _responseSource.ReadLineAsync();
        try
        {
            return read.WaitAsync(_timeout).GetAwaiter().GetResult();
        }
        catch (TimeoutException)
        {
            throw new GtpException(
                $"le moteur GTP est reste muet {(_timeout.TotalSeconds):0} s apres « {command} »");
        }
    }

    /// <summary>Libere les flux donnes au constructeur (l'appelant reste proprietaire du processus, s'il y en a un).</summary>
    public void Dispose()
    {
        // Les flux appartiennent a l'appelant (tubes en memoire des temoins,
        // stdin/stdout du processus moteur) : le client ne ferme que le sink
        // de commandes pour signaler la fin de session.
        _commandSink.Flush();
    }
}
