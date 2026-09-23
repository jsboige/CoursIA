// Grains du lab de cluster : le meme domaine que les labs 01 a 03 (sessions
// d'agents), l'etat en IPersistentState<T> comme au lab 03. Ce qui change est
// ailleurs : le fournisseur "sessions" n'est plus enregistre par du code, il est
// designe par la configuration qu'Aspire injecte dans chaque replique du silo.

using Orleans;
using Orleans.Placement;
using Orleans.Runtime;

namespace OrleansClusterLab;

/// <summary>Etat persiste d'une session.</summary>
[GenerateSerializer]
public sealed class SessionState
{
    [Id(0)] public List<string> Turns { get; set; } = new();
    /// <summary>Identifiants des requetes deja appliquees (exercice 3).</summary>
    [Id(1)] public List<string> RequestIds { get; set; } = new();
}

/// <summary>Recu d'une operation : l'etat apres coup, et OU vit l'activation.</summary>
[GenerateSerializer]
public sealed record TurnReceipt(
    [property: Id(0)] int TurnCount,
    [property: Id(1)] string? ETag,
    [property: Id(2)] string ActivationSilo,
    [property: Id(3)] string ActivationReplica,
    [property: Id(4)] int ActivationPid);

public interface ISessionGrain : IGrainWithStringKey
{
    /// <summary>Ajoute un tour, ecrit l'etat, retourne le recu.</summary>
    Task<TurnReceipt> AppendTurnAsync(string text);

    /// <summary>Etat courant, sans rien ecrire.</summary>
    Task<TurnReceipt> GetReceiptAsync();

    /// <summary>Exercice 3 : ajouter un tour au plus une fois par requestId.</summary>
    Task<TurnReceipt> AppendOnceAsync(string requestId, string text);
}

// TODO etudiant (Exercice 2) : placer chaque nouvelle activation sur le silo qui a
// recu la requete HTTP, pour eviter un saut reseau entre repliques.
// Indice : un attribut de placement du namespace Orleans.Placement, pose sur la classe.
public sealed class SessionGrain : Grain, ISessionGrain
{
    private readonly IPersistentState<SessionState> _session;

    // "sessions" est le nom du fournisseur que l'AppHost a declare par
    // WithGrainStorage("sessions", redis) : le grain ne sait pas que c'est Redis.
    public SessionGrain(
        [PersistentState("session", "sessions")] IPersistentState<SessionState> session)
    {
        _session = session;
    }

    private TurnReceipt Receipt() =>
        new(_session.State.Turns.Count, _session.Etag, RuntimeIdentity, SiloReplica.Name, Environment.ProcessId);

    public async Task<TurnReceipt> AppendTurnAsync(string text)
    {
        _session.State.Turns.Add(text);
        await _session.WriteStateAsync();
        return Receipt();
    }

    public Task<TurnReceipt> GetReceiptAsync() => Task.FromResult(Receipt());

    public Task<TurnReceipt> AppendOnceAsync(string requestId, string text)
    {
        // TODO etudiant (Exercice 3) : remplacer cette delegation. Si requestId figure
        // deja dans _session.State.RequestIds, retourner le recu SANS ecrire (l'ETag ne
        // doit pas bouger) ; sinon ajouter le tour, memoriser requestId, puis ecrire.
        return AppendTurnAsync(text);
    }
}

/// <summary>Nom de la replique Aspire qui heberge ce process.</summary>
public static class SiloReplica
{
    // Aspire nomme chaque replique "<ressource>-<suffixe>" (ex. "silo-abcd1234") : le
    // nom de la ressource arrive dans OTEL_SERVICE_NAME, le suffixe dans l'attribut
    // OpenTelemetry service.instance.id. C'est ce nom que "aspire resource" attend.
    public static string Name { get; } = ReadName();

    private static string ReadName()
    {
        var service = Environment.GetEnvironmentVariable("OTEL_SERVICE_NAME") ?? "silo";
        var attributes = Environment.GetEnvironmentVariable("OTEL_RESOURCE_ATTRIBUTES") ?? "";
        foreach (var pair in attributes.Split(','))
        {
            var parts = pair.Split('=', 2);
            if (parts.Length == 2 && parts[0].Trim() == "service.instance.id")
            {
                return $"{service}-{parts[1].Trim()}";
            }
        }
        return "(inconnue)";
    }
}
