// Grains du lab de persistance : le meme domaine que les labs 01 et 02 (sessions
// d'agents, consommation de tokens), mais l'etat n'est plus un champ prive du grain.
// Il est un IPersistentState<T> injecte, lu a l'activation et ecrit par le grain.

using Orleans;
using Orleans.Runtime;
using Orleans.Storage;

namespace OrleansPersistenceLab;

/// <summary>Etat persiste d'une session. Les attributs Id fixent le contrat de
/// serialisation : ils rendent l'evolution du schema explicite.</summary>
[GenerateSerializer]
public sealed class SessionState
{
    [Id(0)] public List<string> Turns { get; set; } = new();
    [Id(1)] public long TokenTotal { get; set; }
}

/// <summary>Photographie lisible cote client : l'etat et ses metadonnees de stockage.</summary>
[GenerateSerializer]
public sealed record SessionSnapshot(
    [property: Id(0)] int TurnCount,
    [property: Id(1)] long TokenTotal,
    [property: Id(2)] string? ETag,
    [property: Id(3)] bool RecordExists,
    [property: Id(4)] string ActivationId);

public interface IPersistentSessionGrain : IGrainWithStringKey
{
    /// <summary>Ajoute un tour, cumule ses tokens, ecrit l'etat et retourne le nombre de tours.</summary>
    Task<int> AppendTurnAsync(string role, string excerpt, int tokens);

    /// <summary>Etat courant de l'activation, avec l'ETag et l'existence de l'enregistrement.</summary>
    Task<SessionSnapshot> GetSnapshotAsync();

    /// <summary>Historique des tours, dans l'ordre d'arrivee.</summary>
    Task<IReadOnlyList<string>> GetTurnsAsync();

    /// <summary>Relit l'etat depuis le stockage (ReadStateAsync), sans rien ecrire.</summary>
    Task ReloadAsync();

    /// <summary>Exercice 1 : effacer l'etat persiste de la session.</summary>
    Task ResetAsync();

    /// <summary>Exercice 2 : consommer des tokens sous un budget. Retourne true si la
    /// consommation est acceptee et ecrite, false si elle depasse le budget (sans ecriture).</summary>
    Task<bool> TryConsumeAsync(int tokens, long budget);

    /// <summary>Exercice 3 : ajouter un tour en survivant a un conflit d'ETag.
    /// Retourne le nombre de tours apres l'ecriture reussie, ou -1 tant que c'est le stub.</summary>
    Task<int> AppendTurnWithRetryAsync(string role, string excerpt, int tokens);
}

public sealed class PersistentSessionGrain : Grain, IPersistentSessionGrain
{
    private readonly IPersistentState<SessionState> _session;

    // "session" est le nom de l'etat dans le grain, "sessions" le nom du fournisseur
    // enregistre sur le silo : c'est la configuration du silo qui decide ou il vit.
    public PersistentSessionGrain(
        [PersistentState("session", "sessions")] IPersistentState<SessionState> session)
    {
        _session = session;
    }

    public async Task<int> AppendTurnAsync(string role, string excerpt, int tokens)
    {
        _session.State.Turns.Add($"{role} : {excerpt}");
        _session.State.TokenTotal += tokens;
        // L'ecriture est explicite : rien n'est persiste tant que le grain ne l'a pas demande.
        await _session.WriteStateAsync();
        return _session.State.Turns.Count;
    }

    public Task<SessionSnapshot> GetSnapshotAsync() => Task.FromResult(new SessionSnapshot(
        _session.State.Turns.Count,
        _session.State.TokenTotal,
        _session.Etag,
        _session.RecordExists,
        this.GetGrainId() + "@" + RuntimeIdentity));

    public Task<IReadOnlyList<string>> GetTurnsAsync() =>
        Task.FromResult<IReadOnlyList<string>>(_session.State.Turns.ToList());

    public Task ReloadAsync() => _session.ReadStateAsync();

    public Task ResetAsync()
    {
        // TODO etudiant (Exercice 1) : effacer l'etat persiste.
        // Indice : IPersistentState<T> expose une operation dediee, distincte de WriteStateAsync.
        return Task.CompletedTask;
    }

    public Task<bool> TryConsumeAsync(int tokens, long budget)
    {
        // TODO etudiant (Exercice 2) : si TokenTotal + tokens <= budget, cumuler puis ecrire
        // et retourner true ; sinon retourner false SANS ecrire (l'ETag ne doit pas bouger).
        return Task.FromResult(false);
    }

    public Task<int> AppendTurnWithRetryAsync(string role, string excerpt, int tokens)
    {
        // TODO etudiant (Exercice 3) : tenter l'ajout + WriteStateAsync ; sur
        // InconsistentStateException, relire l'etat (ReadStateAsync), rejouer la mutation
        // sur l'etat frais et reecrire. Retourner le nombre de tours final.
        return Task.FromResult(-1);
    }
}
