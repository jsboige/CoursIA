using System.Collections.Concurrent;
using MyIA.AI.Shared.Search.Adversarial.Go;
using MyIA.AI.Shared.Search.Adversarial.Go.Gtp;
using Xunit;
using Xunit.Abstractions;

namespace MyIA.AI.Shared.Tests.Search;

/// <summary>
/// Temoins du client GTP (EPIC #7265, pepite B3, tranche 7).
///
/// Le client est parle ici a un <b>faux moteur scripte</b> : des trames
/// pre-ecrites dans un lecteur bloquant, et un ecritoir qui capte les commandes
/// envoyees. C'est ce decouplage qui rend le protocole temoignable sans le
/// binaire — la preuve contre le vrai gnugo 3.8 (WSL) est mesuree localement et
/// consignee dans le corps de la PR, sur le meme partage que la fixture de la
/// tranche 2b.
///
/// Trois contrats portent la tranche : la trame reussite multi-lignes ne se
/// confond pas avec l'erreur cadree <c>?</c> ; un moteur muet est <b>nomme</b>
/// apres le delai (un silence n'est pas une reponse vide — une reponse vide est
/// un resultat GTP valide) ; et les coordonnees bouclent avec
/// <see cref="GoPoint"/>, le I saute compris.
/// </summary>
public sealed class GtpClientWitnessTests
{
    private readonly ITestOutputHelper _output;

    public GtpClientWitnessTests(ITestOutputHelper output) => _output = output;

    /// <summary>Un moteur GTP scripte : des trames posees d'avance dans un lecteur bloquant.</summary>
    private sealed class ScriptedEngine : IDisposable
    {
        public ScriptedWriter Commands { get; } = new();

        public ScriptedReader Responses { get; } = new();

        public void Dispose() => Responses.CloseChannel();
    }

    /// <summary>Ce que le moteur a recu, capte pour les temoins.</summary>
    private sealed class ScriptedWriter : TextWriter
    {
        private readonly StringWriter _sink = new();

        public override System.Text.Encoding Encoding => _sink.Encoding;

        public override void Write(char value) => _sink.Write(value);

        public override string ToString() => _sink.ToString();
    }

    /// <summary>
    /// Un lecteur qui bloque tant qu'aucune trame n'a ete posee — c'est lui qui
    /// joue le moteur muet du temoin de delai, sans processus.
    /// </summary>
    private sealed class ScriptedReader : TextReader
    {
        private readonly BlockingCollection<string?> _lines = new(boundedCapacity: 128);

        public override Task<string?> ReadLineAsync()
            => Task.Run<string?>(() =>
            {
                try
                {
                    return _lines.Take();
                }
                catch (InvalidOperationException)
                {
                    // Canal ferme : fin de flux, comme un moteur qui quitte.
                    return null;
                }
            });

        public void Respond(params string[] frame)
        {
            foreach (string line in frame)
            {
                _lines.Add(line);
            }
        }

        public void CloseChannel() => _lines.CompleteAdding();
    }

    [Fact]
    public void LeProtocoleEncadreUneReussiteMultiligne()
    {
        using ScriptedEngine engine = new();
        engine.Responses.Respond("= A B C D E", "5 . . . . .", "4 . . O . .", "");
        using GtpClient client = new(engine.Commands, engine.Responses);

        GtpResponse response = client.Send("showboard");

        Assert.True(response.IsSuccess);
        Assert.Null(response.Id);
        Assert.Equal("A B C D E\n5 . . . . .\n4 . . O . .", response.Content);
        Assert.StartsWith("showboard", engine.Commands.ToString());
    }

    [Fact]
    public void LeProtocoleEncadreUneErreurEtLaNomme()
    {
        using ScriptedEngine engine = new();
        engine.Responses.Respond("? illegal move", "");
        using GtpClient client = new(engine.Commands, engine.Responses);

        GtpResponse response = client.Send("play B C3");

        Assert.False(response.IsSuccess);
        GtpException ex = Assert.Throws<GtpException>(() => response.EnsureSuccess("play B C3"));
        Assert.Contains("play B C3", ex.Message);
        Assert.Contains("illegal move", ex.Message);
    }

    [Fact]
    public void LIdentifiantFaitLAlleRetour()
    {
        using ScriptedEngine engine = new();
        engine.Responses.Respond("=7 3.8", "");
        using GtpClient client = new(engine.Commands, engine.Responses);

        GtpResponse response = client.Send("protocol_version", id: 7);

        Assert.Equal("7 protocol_version\n", engine.Commands.ToString().Replace("\r\n", "\n"));
        Assert.Equal(7, response.Id);
        Assert.Equal("3.8", response.Content);
    }

    [Fact]
    public void UneReponseNonCadreeEstRefusee()
    {
        using ScriptedEngine engine = new();
        engine.Responses.Respond("GNU Go 3.8", "");
        using GtpClient client = new(engine.Commands, engine.Responses);

        GtpException ex = Assert.Throws<GtpException>(() => client.Send("version"));
        Assert.Contains("non cadree", ex.Message);
    }

    [Fact]
    public void UnMoteurMuetEstNommeApresLeDelai()
    {
        using ScriptedEngine engine = new();
        using GtpClient client = new(engine.Commands, engine.Responses, TimeSpan.FromMilliseconds(200));

        GtpException ex = Assert.Throws<GtpException>(() => client.Send("genmove B"));
        Assert.Contains("genmove B", ex.Message);
        Assert.Contains("muet", ex.Message);
    }

    [Fact]
    public void UneReponseVideEstUnResultatValide()
    {
        using ScriptedEngine engine = new();
        engine.Responses.Respond("= ", "");
        using GtpClient client = new(engine.Commands, engine.Responses);

        GtpResponse response = client.Send("board_size 5");

        Assert.True(response.IsSuccess);
        Assert.Equal(string.Empty, response.Content);
    }

    [Fact]
    public void UneReponseNumeriqueSansIdentifiantResteUnContenu()
    {
        // "= 12" : l'espace apres = dit « pas d'identifiant » — le 12 est le
        // resultat, pas un id. Un parseur qui lirait 12 comme id rendrait une
        // reponse vide a la place du compte.
        using ScriptedEngine engine = new();
        engine.Responses.Respond("= 12", "");
        using GtpClient client = new(engine.Commands, engine.Responses);

        GtpResponse response = client.Send("list_commands_nom_de_test");

        Assert.Null(response.Id);
        Assert.Equal("12", response.Content);
    }

    [Fact]
    public void LesCoordonneesBouclentAvecGoPoint()
    {
        // Le I est saute : la 9e colonne (index 8) s'ecrit J.
        Assert.Equal("J3", new GoPoint(8, 2).ToString());
        Assert.Equal(new GoPoint(8, 2), GtpCoordinate.Parse("J3", 9));
        Assert.Equal(new GoPoint(0, 0), GtpCoordinate.Parse("A1", 19));
        Assert.Equal(new GoPoint(18, 18), GtpCoordinate.Parse("T19", 19));
        Assert.Equal(GoPoint.Pass, GtpCoordinate.Parse("pass", 9));
    }

    [Fact]
    public void LesCoordonneesInvalidesSontRefuseesEnEtantNommees()
    {
        Assert.Throws<GtpException>(() => GtpCoordinate.Parse("I3", 9));   // le I n'existe pas en GTP
        Assert.Throws<GtpException>(() => GtpCoordinate.Parse("Z1", 5));   // colonne hors plateau
        Assert.Throws<GtpException>(() => GtpCoordinate.Parse("C0", 5));   // rangee nulle
        Assert.Throws<GtpException>(() => GtpCoordinate.Parse("C6", 5));   // rangee hors plateau
        Assert.Throws<GtpException>(() => GtpCoordinate.Parse("resign", 9)); // abandon : pas une intersection
    }

    [Fact]
    public void LaVariableDenvironnementPrimeSurLaResolution()
    {
        string? before = Environment.GetEnvironmentVariable(GnuGoLauncher.CommandVariable);
        try
        {
            Environment.SetEnvironmentVariable(GnuGoLauncher.CommandVariable, "wsl -d Ubuntu -- gnugo");
            IReadOnlyList<string> resolved = GnuGoLauncher.Resolve();
            Assert.Equal(["wsl", "-d", "Ubuntu", "--", "gnugo"], resolved);
        }
        finally
        {
            Environment.SetEnvironmentVariable(GnuGoLauncher.CommandVariable, before);
        }
    }

    [Fact]
    public void SansMoteurLeRefusNommeLInstallation()
    {
        string? beforeVar = Environment.GetEnvironmentVariable(GnuGoLauncher.CommandVariable);
        string? beforePath = Environment.GetEnvironmentVariable("PATH");
        try
        {
            Environment.SetEnvironmentVariable(GnuGoLauncher.CommandVariable, null);
            Environment.SetEnvironmentVariable("PATH", "");
            GtpException ex = Assert.Throws<GtpException>(GnuGoLauncher.Resolve);
            Assert.Contains("apt install gnugo", ex.Message);
            Assert.Contains(GnuGoLauncher.CommandVariable, ex.Message);
        }
        finally
        {
            Environment.SetEnvironmentVariable(GnuGoLauncher.CommandVariable, beforeVar);
            Environment.SetEnvironmentVariable("PATH", beforePath);
        }
    }
}
